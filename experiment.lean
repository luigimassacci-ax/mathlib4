import Mathlib

open SchwartzMap Filter Nat NNReal ContDiff Topology

noncomputable def bumpAux (x : ℝ) : ℂ :=
 if x ∈ Set.Ioo (-1 : ℝ) 1  then Real.exp (-1 / (1 - x^2)) else 0

theorem smooth_bumpAux : ContDiff ℝ ∞ bumpAux := by
  have heq : bumpAux = Complex.ofRealCLM ∘ expNegInvGlue ∘ (fun x : ℝ => 1 - x ^ 2) := by
    funext x; simp only [Function.comp, Complex.ofRealCLM_apply, bumpAux]
    split_ifs with hx
    · have h1 : (0 : ℝ) < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, sq_nonneg x]
      simp only [expNegInvGlue, if_neg (not_le.mpr h1), Complex.ofReal_exp]
      congr 1; push_cast; ring
    · have h2 : 1 - x ^ 2 ≤ 0 := by
        simp only [Set.mem_Ioo, not_and_or, not_lt] at hx
        rcases hx with h | h <;> nlinarith [sq_nonneg x]
      simp [expNegInvGlue, h2]
  rw [heq]; fun_prop

theorem bumpAux_hasCompactSupport : HasCompactSupport bumpAux := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  simp only [Function.mem_support, bumpAux] at hx
  exact Set.Ioo_subset_Icc_self (not_not.mp fun h => hx (if_neg h))

noncomputable def bump : 𝓢(ℝ, ℂ) := bumpAux_hasCompactSupport.toSchwartzMap smooth_bumpAux

theorem iteratedDeriv_bump_one (n : ℕ) : iteratedDeriv n bump 1 = 0 := by
  have h_cont : Continuous (iteratedDeriv n bump) := by
    apply smooth_bumpAux.continuous_iteratedDeriv n
    exact_mod_cast le_top
  have h_zero : ∀ x : ℝ, 1 < x → iteratedDeriv n bump x = 0 := fun x hx => by
    have heq : bump =ᶠ[𝓝 x] 0 :=
      Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy => by
        show bumpAux y = 0
        simp [bumpAux, show y ∉ Set.Ioo (-1 : ℝ) 1 from
          fun h => absurd h.2 (not_lt.mpr hy.le)]
    exact (heq.iteratedDeriv_eq n).trans iteratedDeriv_const_zero
  have h_tendsto : Tendsto (iteratedDeriv n bump) (𝓝[>] 1) (nhds 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (h_zero x hx).symm)
  exact tendsto_nhds_unique (h_cont.continuousAt.mono_left nhdsWithin_le_nhds) h_tendsto

-- Helper: derivCLM^n f at a point equals iteratedDeriv n f
private lemma derivCLM_pow_eq (n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ((((derivCLM ℂ ℂ) ^ n) f) : ℝ → ℂ) x = iteratedDeriv n (f : ℝ → ℂ) x := by
  have hsemi : Function.Semiconj (↑· : 𝓢(ℝ, ℂ) → ℝ → ℂ) (derivCLM ℂ ℂ) deriv :=
    fun g => funext (derivCLM_apply ℂ g)
  rw [congr_fun (ContinuousLinearMap.coe_pow' _ _) f, iteratedDeriv_eq_iterate]
  exact congr_fun (hsemi.iterate_right n f) x

-- Helper: iteratedDeriv of the real part = real part of iteratedDeriv
private lemma iteratedDeriv_re_of_bump (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => (bump y : ℂ).re) x = (iteratedDeriv n (bump : ℝ → ℂ) x).re := by
  rw [show (fun y : ℝ => (bump y : ℂ).re) = Complex.reCLM ∘ (bump : ℝ → ℂ) from rfl,
      iteratedDeriv_eq_iteratedFDeriv,
      Complex.reCLM.iteratedFDeriv_comp_left (i := n) (bump.contDiffAt ⊤)
        (by exact_mod_cast le_top),
      iteratedDeriv_eq_iteratedFDeriv]; rfl

private lemma isBounded_iteratedDeriv_bump :
    ∀ m : ℕ, BddAbove (Set.range (fun x => ‖(((derivCLM ℂ ℂ) ^ (m)) bump : ℝ → ℂ) x‖)) := by
  intro m
  refine ⟨SchwartzMap.seminorm ℂ 0 0 (((derivCLM ℂ ℂ) ^ (m)) bump), fun _ ⟨y, hy⟩ => hy ▸ ?_⟩
  simpa using SchwartzMap.le_seminorm ℂ 0 0 (((derivCLM ℂ ℂ) ^ (m)) bump) y

theorem tendsto_atTop_supNorm_derivPow_div_factorial :
    Tendsto (fun n : ℕ => (⨆ x : ℝ, ‖(((derivCLM ℂ ℂ) ^ n) bump) x‖) / (n.factorial : ℝ))
    atTop atTop := by
  set g : ℝ → ℝ := fun x => (bump x : ℂ).re
  have hg_smooth : ContDiff ℝ ∞ g := Complex.reCLM.contDiff.comp smooth_bumpAux
  have hg_pos : 0 < g (1 / 2) := by
    show 0 < (bumpAux (1 / 2 : ℝ)).re
    simp only [bumpAux, if_pos (show (1/2 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num),
               Complex.ofReal_re]
    exact Real.exp_pos _
  have hg_zero_at_one : ∀ n : ℕ, iteratedDeriv n g 1 = 0 := fun n => by
    simp only [g, iteratedDeriv_re_of_bump, iteratedDeriv_bump_one, Complex.zero_re]
  have lower_bound : ∀ n : ℕ,
      g (1 / 2) * 2 ^ (n + 1) ≤
      (⨆ x : ℝ, ‖(((derivCLM ℂ ℂ) ^ (n + 1)) bump) x‖) / ((n + 1).factorial : ℝ) := by
    intro n
    obtain ⟨c, hc, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := g) (x₀ := 1) (x := 1/2) (n := n)
      (by norm_num)
      (hg_smooth.contDiffOn.of_le (by exact mod_cast le_top))
    have hpoly_zero : taylorWithinEval g n (Set.uIcc 1 (1 / 2 : ℝ)) 1 (1 / 2) = 0 := by
      rw [taylor_within_apply]
      apply Finset.sum_eq_zero
      intro k _
      have hk_zero : iteratedDerivWithin k g (Set.uIcc (1 : ℝ) (1 / 2)) 1 = 0 := by
        rw [iteratedDerivWithin_eq_iteratedDeriv
              (uniqueDiffOn_uIcc (by norm_num : (1 : ℝ) ≠ 1 / 2))
              (hg_smooth.contDiffAt.of_le (by exact_mod_cast le_top))
              (Set.left_mem_uIcc)]
        exact hg_zero_at_one k
      rw [hk_zero]
      simp
    rw [hpoly_zero, sub_zero] at hrem
    have hfact_pos : (0 : ℝ) < (n + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have h2n_pos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    have hkey : g (1 / 2) * 2 ^ (n + 1) ≤ |iteratedDeriv (n + 1) g c| / (n + 1).factorial := by
      rw [le_div_iff₀ hfact_pos]
      have heq : g (1 / 2) * (n + 1).factorial =
          iteratedDeriv (n + 1) g c * (1 / 2 - 1) ^ (n + 1) / (n + 1).factorial *
          (n + 1).factorial := by
        rw [← hrem]
      rw [div_mul_cancel₀ _ (ne_of_gt hfact_pos)] at heq
      rw [show g (1 / 2) * 2 ^ (n + 1) * (n + 1).factorial =
          |g (1 / 2) * (n + 1).factorial| * 2 ^ (n + 1) by
            rw [abs_of_pos (mul_pos hg_pos hfact_pos)]; ring]
      rw [← mul_one |iteratedDeriv (n + 1) g c|, heq, abs_mul, mul_assoc]
      gcongr
      rw [show (1 / 2 - 1 : ℝ) = -(1 / 2) by ring,
          neg_pow, abs_mul, abs_pow, abs_neg, abs_of_pos (show 0 < (1 : ℝ) by positivity), abs_pow,
           abs_of_pos (show 0 < (1 / 2 : ℝ) by positivity), one_pow, one_mul]
      simp
    calc g (1 / 2) * 2 ^ (n + 1)
        ≤ |iteratedDeriv (n + 1) g c| / (n + 1).factorial := hkey
      _ = |(iteratedDeriv (n + 1) (bump : ℝ → ℂ) c).re| / (n + 1).factorial := by
            rw [← iteratedDeriv_re_of_bump]
      _ ≤ ‖iteratedDeriv (n + 1) (bump : ℝ → ℂ) c‖ / (n + 1).factorial :=
            div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (le_of_lt hfact_pos)
      _ = ‖(((derivCLM ℂ ℂ) ^ (n + 1)) bump : ℝ → ℂ) c‖ / (n + 1).factorial := by
            rw [derivCLM_pow_eq]
      _ ≤ (⨆ x : ℝ, ‖(((derivCLM ℂ ℂ) ^ (n + 1)) bump : ℝ → ℂ) x‖) / (n + 1).factorial :=
            div_le_div_of_nonneg_right (le_ciSup (isBounded_iteratedDeriv_bump (n+1)) c)
                                      (le_of_lt hfact_pos)
  apply tendsto_atTop_mono' atTop _ ((tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℝ) < 2)).const_mul_atTop' hg_pos)
  filter_upwards [eventually_ge_atTop 1] with m hm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hm)
  exact lower_bound n

example (hExp : Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • ((SchwartzMap.derivCLM ℂ ℂ) ^ n))))
  : False := by
  have tendstoZero := Summable.tendsto_cofinite_zero hExp
  have H := WithSeminorms.tendsto_nhds_atTop (schwartz_withSeminorms ℂ ..)
    ((fun n => ((n.factorial : ℂ)⁻¹ • ((SchwartzMap.derivCLM ℂ ℂ) ^ n)) bump))
    ((0 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) bump)
  have hcont : Continuous (fun T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) => T bump) :=
    ContinuousLinearMap.instContinuousEvalConst.continuous_eval_const _
  have h1 : Tendsto (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • (SchwartzMap.derivCLM ℂ ℂ) ^ n) bump)
    cofinite (nhds ((0 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) bump)) :=
    (hcont.tendsto 0).comp tendstoZero
  rw [Nat.cofinite_eq_atTop, H] at h1
  have hε_pos : 0 < ‖bump (1/2 : ℝ)‖ := by
    show 0 < ‖bumpAux (1/2 : ℝ)‖
    simp only [bumpAux, if_pos (show (1/2 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)]
    exact norm_pos_iff.mpr (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  specialize h1 ⟨0, 0⟩ ‖bump (1/2 : ℝ)‖ hε_pos
  rcases h1 with ⟨N, hN⟩
  contrapose! hN
  have := tendsto_atTop_supNorm_derivPow_div_factorial
  rw [Filter.tendsto_atTop_atTop] at this
  rcases (this (‖bump (1/2 : ℝ)‖)) with ⟨N', hN'⟩
  set M := max N N' with M_def
  use M
  specialize hN' M (show N' ≤ M from le_max_right N N')
  simp [-one_div] at hN'
  simp [-one_div]
  set f : 𝓢(ℝ, ℂ) :=
    (((M).factorial : ℂ)⁻¹ • (⇑(derivCLM ℂ ℂ))^[M] bump) with f_def
  have hbound := (le_seminorm ℂ 0 0 f)
  simp at hbound
  nth_rewrite 1 [f_def] at hbound
  simp at hbound
  refine ⟨by simp [M_def], ?_⟩
  simp [-one_div, derivCLM] at this
  apply le_trans hN'
  rw [show (⨆ x, ‖((⇑(derivCLM ℂ ℂ))^[M] bump) x‖) / ↑M ! =
      ⨆ x, (↑M !)⁻¹ * ‖((⇑(derivCLM ℂ ℂ))^[M] bump) x‖ by
    rw [← Real.mul_iSup_of_nonneg (by positivity), mul_comm, div_eq_mul_inv]]
  exact ciSup_le hbound
