-- Prove2me | solution 1 for LL_Decomp530a.leaf_regularPart_finite_order_growth
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T07:15:00.812013+00:00
-- url     : https://prove2.me/submissions/aaff4860-2361-4307-9ba7-cd383ac740bc

import Mathlib
import Definitions.Def_LL_Decomp530a_regularPart
import Theorems.Thm_QRHLittlewood_rademacher_convexity
import Theorems.Thm_Zeta23_RvM_riemannZeta_linear_growth

open Classical Complex Set Filter ZMod LL_Decomp530a
open scoped Topology

/-! ### Helper lemmas for Euler factors, Gamma, cos, and dslope -/

private lemma norm_euler_prod_le {f q : ℕ} [NeZero f] (ψ : DirichletCharacter ℂ f)
    {s : ℂ} (hs : -1 / 2 ≤ s.re) :
    ‖∏ p ∈ q.primeFactors, (1 - ψ p * (p : ℂ) ^ (-s))‖ ≤
      ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ ((1 : ℝ) / 2)) := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hp => ?_
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hp_ge1 : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
  have hψ : ‖ψ p‖ ≤ 1 := by
    by_cases hu : IsUnit (p : ZMod f)
    · rcases hu with ⟨u, hu⟩
      have hpow : (ψ p) ^ Fintype.card (ZMod f)ˣ = 1 := by
        rw [← hu, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
      have hnorm_pow : ‖ψ p‖ ^ Fintype.card (ZMod f)ˣ = 1 := by
        rw [← norm_pow, hpow, norm_one]
      have hpos : 0 < Fintype.card (ZMod f)ˣ := Fintype.card_pos
      have h1 : ‖ψ p‖ = 1 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have : ‖ψ p‖ ^ Fintype.card (ZMod f)ˣ < 1 ^ Fintype.card (ZMod f)ˣ :=
            pow_lt_pow_left₀ hlt (norm_nonneg _) (ne_of_gt hpos)
          rw [one_pow] at this; linarith
        · have : 1 ^ Fintype.card (ZMod f)ˣ < ‖ψ p‖ ^ Fintype.card (ZMod f)ˣ :=
            pow_lt_pow_left₀ hgt (by norm_num) (ne_of_gt hpos)
          rw [one_pow] at this; linarith
      linarith
    · rw [MulChar.map_nonunit _ hu, norm_zero]; norm_num
  have hcpow : ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by norm_cast,
        Complex.norm_cpow_eq_rpow_re_of_pos hp_pos, Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hp_ge1 (by linarith)
  calc ‖(1 : ℂ) - ψ p * (p : ℂ) ^ (-s)‖
      ≤ ‖(1 : ℂ)‖ + ‖ψ p * (p : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ = 1 + ‖ψ p‖ * ‖(p : ℂ) ^ (-s)‖ := by rw [norm_one, norm_mul]
    _ ≤ 1 + 1 * (p : ℝ) ^ ((1 : ℝ) / 2) := by
        gcongr
    _ = 1 + (p : ℝ) ^ ((1 : ℝ) / 2) := by ring

private lemma norm_triv_euler_prod_le (q : ℕ) {s : ℂ} (hs : -1 / 2 ≤ s.re) :
    ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤
      ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ ((1 : ℝ) / 2)) := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hp => ?_
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hp_ge1 : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
  have hcpow : ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by norm_cast,
        Complex.norm_cpow_eq_rpow_re_of_pos hp_pos, Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hp_ge1 (by linarith)
  calc ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖
      ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 1 + (p : ℝ) ^ ((1 : ℝ) / 2) := by rw [norm_one]; linarith

private lemma conductor_ge_three_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : 3 ≤ χ.conductor := by
  have hne0 : χ.conductor ≠ 0 := χ.conductor_ne_zero
  have hne1 : χ.conductor ≠ 1 := by
    intro h1
    exact hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one (χ := χ)).mpr h1)
  have hne2 : χ.conductor ≠ 2 := by
    intro h2
    have hprim1 : χ.primitiveCharacter = 1 := by
      have : NeZero χ.conductor := ⟨hne0⟩
      ext u
      have hsub : Subsingleton (ZMod 2)ˣ := by
        refine ⟨fun a b => ?_⟩
        fin_cases a
        fin_cases b
        rfl
      have hsub' : Subsingleton (ZMod χ.conductor)ˣ := h2 ▸ hsub
      have hu1 : u = 1 := Subsingleton.elim u 1
      rw [hu1, Units.val_one, map_one, map_one]
    have h1 : χ = 1 := by
      rw [← χ.changeLevel_primitiveCharacter, hprim1, DirichletCharacter.changeLevel_one]
    exact hχ h1
  omega

private lemma norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  unfold Complex.GammaIntegral
  calc ‖∫ x in Ioi (0 : ℝ), (Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)‖
      ≤ ∫ x in Ioi (0 : ℝ), ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (z.re - 1) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        have hxpos : (0 : ℝ) < x := hx
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _)),
            Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.sub_re, Complex.one_re]

private lemma norm_cos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos]
  have h1 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; simp
  calc ‖(Complex.exp (z * I) + Complex.exp (-z * I)) / 2‖
      = ‖Complex.exp (z * I) + Complex.exp (-z * I)‖ / 2 := by
        rw [norm_div, Complex.norm_ofNat]
    _ ≤ (‖Complex.exp (z * I)‖ + ‖Complex.exp (-z * I)‖) / 2 := by
        gcongr; exact norm_add_le _ _
    _ = (Real.exp (-z.im) + Real.exp z.im) / 2 := by rw [h1, h2]
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 := by
        gcongr
        · exact neg_le_abs z.im
        · exact le_abs_self z.im
    _ = Real.exp |z.im| := by ring

private lemma real_Gamma_bdd_on_half_three_halves :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → Real.Gamma x ≤ M := by
  have hcomp : IsCompact (Icc (1 / 2 : ℝ) (3 / 2)) := isCompact_Icc
  have hcont : ContinuousOn Real.Gamma (Icc (1 / 2 : ℝ) (3 / 2)) := by
    intro x hx
    exact (Real.differentiableAt_Gamma (fun m => by linarith [hx.1])).continuousAt.continuousWithinAt
  rcases hcomp.exists_bound_of_continuousOn hcont with ⟨M, hM⟩
  refine ⟨max M 1, by positivity, fun x hx1 hx2 => ?_⟩
  have h1 := hM x ⟨hx1, hx2⟩
  rw [Real.norm_eq_abs] at h1
  exact le_trans (le_abs_self _) (le_trans h1 (le_max_left _ _))

/-! ### Main theorem -/

theorem solution {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ s : ℂ,
      -δ ≤ s.re → s.re ≤ 1 + δ →
      ‖regularPart χ s‖ ≤ C * Real.exp (|s.im| ^ c) := by
  by_cases hχ : χ = 1
  · -- Case 1: Principal character χ = 1
    subst hχ
    have hfun : regularPart (1 : DirichletCharacter ℂ q) =
        dslope (DirichletCharacter.LFunctionTrivChar₁ q) 1 := by
      funext s; unfold regularPart; simp
    rw [hfun]
    -- Step 1a: Continuity on the compact box [-δ, 1 + δ] × [-1, 1]
    have hdiff : Differentiable ℂ (DirichletCharacter.LFunctionTrivChar₁ q) :=
      DirichletCharacter.differentiable_LFunctionTrivChar₁ q
    have hcont_dslope : Continuous (dslope (DirichletCharacter.LFunctionTrivChar₁ q) 1) := by
      rw [continuous_iff_continuousAt]
      intro z
      exact (continuousAt_dslope_same.mpr hdiff.differentiableAt) |> fun h1 => by
        by_cases hz : z = 1
        · subst hz; exact h1
        · exact (continuousAt_dslope_of_ne hz).mpr hdiff.continuous.continuousAt
    set K : Set ℂ := {s : ℂ | -δ ≤ s.re ∧ s.re ≤ 1 + δ ∧ -1 ≤ s.im ∧ s.im ≤ 1}
    have hK_comp : IsCompact K := by
      have hK_eq : K = Complex.equivRealProdCLM.symm '' (Icc (-δ) (1 + δ) ×ˢ Icc (-1 : ℝ) 1) := by
        ext s
        simp only [K, mem_ofPred_eq, mem_image, mem_prod, mem_Icc, Prod.exists]
        constructor
        · intro ⟨h1, h2, h3, h4⟩
          refine ⟨s.re, s.im, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ?_⟩
          apply Complex.ext <;> simp
        · rintro ⟨a, b, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl⟩
          simp [h1, h2, h3, h4]
      rw [hK_eq]
      exact (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous
    rcases hK_comp.exists_bound_of_continuousOn hcont_dslope.continuousOn with ⟨M0, hM0⟩
    -- Step 1b: Gamma bound on [1/2, 3/2]
    rcases real_Gamma_bdd_on_half_three_halves with ⟨MΓ, hMΓ_pos, hMΓ⟩
    set Ce : ℝ := ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ ((1 : ℝ) / 2))
    have hCe_pos : 0 < Ce := Finset.prod_pos fun p hp => by positivity
    set c1 : ℝ := ‖DirichletCharacter.LFunctionTrivChar₁ q 1‖
    set C_right : ℝ := Ce * 4.5 + c1
    set C_left : ℝ := Ce * (2 * (2 * Real.pi) ^ ((1 : ℝ) / 2) * MΓ * 4.5 * Real.exp 9) + c1
    refine ⟨max (max M0 1) (max C_right C_left), 2, by positivity, by norm_num, fun s hs1 hs2 => ?_⟩
    set C : ℝ := max (max M0 1) (max C_right C_left)
    have hC_M0 : M0 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
    have hC_right : C_right ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
    have hC_left : C_left ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
    have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (le_trans (le_max_right M0 1) (le_max_left _ _))
    have hexp_ge1 : 1 ≤ Real.exp (|s.im| ^ (2 : ℝ)) :=
      Real.one_le_exp (Real.rpow_nonneg (abs_nonneg _) _)
    by_cases him : |s.im| ≤ 1
    · have hsK : s ∈ K := ⟨hs1, hs2, (abs_le.mp him).1, (abs_le.mp him).2⟩
      calc ‖dslope (DirichletCharacter.LFunctionTrivChar₁ q) 1 s‖
          ≤ M0 := hM0 s hsK
        _ ≤ C := hC_M0
        _ ≤ C * Real.exp (|s.im| ^ (2 : ℝ)) := le_mul_of_one_le_right (le_of_lt hC_pos) hexp_ge1
    · push Not at him
      have hs_ne1 : s ≠ 1 := by
        intro h; rw [h] at him; simp at him; linarith
      have hs_sub1_ge1 : 1 ≤ ‖s - 1‖ := by
        have h1 : |s.im| = |(s - 1).im| := by simp
        rw [h1] at him
        exact le_trans (le_of_lt him) (Complex.abs_im_le_norm (s - 1))
      have hdslope_eq : dslope (DirichletCharacter.LFunctionTrivChar₁ q) 1 s =
          DirichletCharacter.LFunctionTrivChar q s -
            DirichletCharacter.LFunctionTrivChar₁ q 1 / (s - 1) := by
        rw [dslope_of_ne _ hs_ne1, slope_def_field]
        have hupd : DirichletCharacter.LFunctionTrivChar₁ q s =
            (s - 1) * DirichletCharacter.LFunctionTrivChar q s := by
          unfold DirichletCharacter.LFunctionTrivChar₁
          exact Function.update_of_ne hs_ne1 _ _
        rw [hupd, sub_div, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs_ne1)]
      have htri : ‖dslope (DirichletCharacter.LFunctionTrivChar₁ q) 1 s‖ ≤
          Ce * ‖riemannZeta s‖ + c1 := by
        rw [hdslope_eq]
        have h1 : ‖DirichletCharacter.LFunctionTrivChar q s‖ ≤ Ce * ‖riemannZeta s‖ := by
          rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs_ne1, norm_mul]
          exact mul_le_mul_of_nonneg_right (norm_triv_euler_prod_le q (by linarith)) (norm_nonneg _)
        have h2 : ‖DirichletCharacter.LFunctionTrivChar₁ q 1 / (s - 1)‖ ≤ c1 := by
          rw [norm_div]
          exact div_le_self (norm_nonneg _) hs_sub1_ge1
        calc ‖DirichletCharacter.LFunctionTrivChar q s -
                DirichletCharacter.LFunctionTrivChar₁ q 1 / (s - 1)‖
            ≤ ‖DirichletCharacter.LFunctionTrivChar q s‖ +
                ‖DirichletCharacter.LFunctionTrivChar₁ q 1 / (s - 1)‖ := norm_sub_le _ _
          _ ≤ Ce * ‖riemannZeta s‖ + c1 := add_le_add h1 h2
      have hsq_rpow : |s.im| ^ (2 : ℝ) = |s.im| ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have ht_le_exp : |s.im| ≤ Real.exp (|s.im| ^ (2 : ℝ)) := by
        rw [hsq_rpow]
        have h1 : |s.im| ≤ |s.im| ^ 2 := by nlinarith
        linarith [Real.add_one_le_exp (|s.im| ^ 2)]
      by_cases hre : (1 / 2 : ℝ) ≤ s.re
      · have hzeta := Zeta23.RvM.riemannZeta_linear_growth (by norm_num : (0 : ℝ) < 1 / 2) hre (le_of_lt him)
        have hzeta' : ‖riemannZeta s‖ ≤ 4.5 * |s.im| := by norm_num at hzeta; linarith
        calc ‖dslope (DirichletCharacter.LFunctionTrivChar₁ q) 1 s‖
            ≤ Ce * ‖riemannZeta s‖ + c1 := htri
          _ ≤ Ce * (4.5 * |s.im|) + c1 := by gcongr
          _ ≤ Ce * (4.5 * Real.exp (|s.im| ^ (2 : ℝ))) + c1 * Real.exp (|s.im| ^ (2 : ℝ)) := by
              have h1 : c1 ≤ c1 * Real.exp (|s.im| ^ (2 : ℝ)) :=
                le_mul_of_one_le_right (norm_nonneg _) hexp_ge1
              have h2 : Ce * (4.5 * |s.im|) ≤ Ce * (4.5 * Real.exp (|s.im| ^ (2 : ℝ))) := by gcongr
              linarith
          _ = C_right * Real.exp (|s.im| ^ (2 : ℝ)) := by dsimp [C_right]; ring
          _ ≤ C * Real.exp (|s.im| ^ (2 : ℝ)) := by gcongr
      · push Not at hre
        -- Functional equation at w = 1 - s
        set w : ℂ := 1 - s
        have hw_re1 : (1 / 2 : ℝ) ≤ w.re := by dsimp [w]; simp; linarith
        have hw_re2 : w.re ≤ 3 / 2 := by dsimp [w]; simp; linarith
        have hw_im : |w.im| = |s.im| := by dsimp [w]; simp
        have hw_ne_neg_nat : ∀ n : ℕ, w ≠ -n := by
          intro n hn
          have him0 : w.im = 0 := by rw [hn]; simp
          rw [him0, abs_zero] at hw_im; linarith
        have hw_ne1 : w ≠ 1 := by
          intro h1
          have him0 : w.im = 0 := by rw [h1]; simp
          rw [him0, abs_zero] at hw_im; linarith
        have hfe := riemannZeta_one_sub hw_ne_neg_nat hw_ne1
        have h1w : 1 - w = s := by dsimp [w]; ring
        rw [h1w] at hfe
        have hcpow_2pi : ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ (2 * Real.pi) ^ ((1 : ℝ) / 2) := by
          have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
          have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
          have heq : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
          rw [heq, Complex.norm_cpow_eq_rpow_re_of_pos h2pi_pos, Complex.neg_re]
          exact Real.rpow_le_rpow_of_exponent_le h2pi_ge1 (by linarith)
        have hGamma_le : ‖Complex.Gamma w‖ ≤ MΓ :=
          le_trans (norm_Gamma_le_Gamma_re (by linarith)) (hMΓ w.re hw_re1 hw_re2)
        have hcos_le : ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ ≤ Real.exp (Real.pi / 2 * |s.im|) := by
          have h1 := norm_cos_le_exp_abs_im ((Real.pi : ℂ) * w / 2)
          have him_eq : |((Real.pi : ℂ) * w / 2).im| = Real.pi / 2 * |s.im| := by
            have : ((Real.pi : ℂ) * w / 2).im = Real.pi / 2 * w.im := by
              rw [show (Real.pi : ℂ) * w / 2 = ((Real.pi / 2 : ℝ) : ℂ) * w by push_cast; ring]
              simp
            rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 2), hw_im]
          rwa [him_eq] at h1
        have hzeta_w : ‖riemannZeta w‖ ≤ 4.5 * |s.im| := by
          have hz := Zeta23.RvM.riemannZeta_linear_growth (by norm_num : (0 : ℝ) < 1 / 2) hw_re1
            (by rw [hw_im]; exact le_of_lt him)
          rw [hw_im] at hz; norm_num at hz; linarith
        have hcomb_exp : Real.exp (Real.pi / 2 * |s.im|) * |s.im| ≤
            Real.exp 9 * Real.exp (|s.im| ^ (2 : ℝ)) := by
          rw [hsq_rpow, ← Real.exp_add]
          have h1 : |s.im| ≤ Real.exp |s.im| := by linarith [Real.add_one_le_exp |s.im|]
          calc Real.exp (Real.pi / 2 * |s.im|) * |s.im|
              ≤ Real.exp (Real.pi / 2 * |s.im|) * Real.exp |s.im| :=
                mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos _))
            _ = Real.exp ((Real.pi / 2 + 1) * |s.im|) := by rw [← Real.exp_add]; ring_nf
            _ ≤ Real.exp (9 + |s.im| ^ 2) := by
                apply Real.exp_le_exp.mpr
                have hpi : Real.pi < 4 := Real.pi_lt_four
                nlinarith [sq_nonneg (|s.im| - 3)]
        have hzeta_s : ‖riemannZeta s‖ ≤
            (2 * (2 * Real.pi) ^ ((1 : ℝ) / 2) * MΓ * 4.5 * Real.exp 9) * Real.exp (|s.im| ^ (2 : ℝ)) := by
          rw [hfe, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
          calc 2 * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ * ‖Complex.Gamma w‖ *
                ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ * ‖riemannZeta w‖
              ≤ 2 * (2 * Real.pi) ^ ((1 : ℝ) / 2) * MΓ *
                Real.exp (Real.pi / 2 * |s.im|) * (4.5 * |s.im|) := by gcongr
            _ = (2 * (2 * Real.pi) ^ ((1 : ℝ) / 2) * MΓ * 4.5) *
                (Real.exp (Real.pi / 2 * |s.im|) * |s.im|) := by ring
            _ ≤ (2 * (2 * Real.pi) ^ ((1 : ℝ) / 2) * MΓ * 4.5) *
                (Real.exp 9 * Real.exp (|s.im| ^ (2 : ℝ))) := by gcongr
            _ = (2 * (2 * Real.pi) ^ ((1 : ℝ) / 2) * MΓ * 4.5 * Real.exp 9) *
                Real.exp (|s.im| ^ (2 : ℝ)) := by ring
        calc ‖dslope (DirichletCharacter.LFunctionTrivChar₁ q) 1 s‖
            ≤ Ce * ‖riemannZeta s‖ + c1 := htri
          _ ≤ Ce * ((2 * (2 * Real.pi) ^ ((1 : ℝ) / 2) * MΓ * 4.5 * Real.exp 9) *
                Real.exp (|s.im| ^ (2 : ℝ))) + c1 * Real.exp (|s.im| ^ (2 : ℝ)) := by
              have h1 : c1 ≤ c1 * Real.exp (|s.im| ^ (2 : ℝ)) :=
                le_mul_of_one_le_right (norm_nonneg _) hexp_ge1
              have h2 := mul_le_mul_of_nonneg_left hzeta_s (le_of_lt hCe_pos)
              linarith
          _ = C_left * Real.exp (|s.im| ^ (2 : ℝ)) := by dsimp [C_left]; ring
          _ ≤ C * Real.exp (|s.im| ^ (2 : ℝ)) := by gcongr
  · -- Case 2: Non-principal character χ ≠ 1
    have hfun : regularPart χ = χ.LFunction := by
      funext s; unfold regularPart; rw [if_neg hχ]
    rw [hfun]
    set f : ℕ := χ.conductor
    have hf3 : 3 ≤ f := conductor_ge_three_of_ne_one hχ
    have : NeZero f := ⟨by omega⟩
    set χ₀ : DirichletCharacter ℂ f := χ.primitiveCharacter
    have hprim : χ₀.IsPrimitive := χ.primitiveCharacter_isPrimitive
    have hχ₀_ne1 : χ₀ ≠ 1 := by
      intro h1
      have : χ = 1 := by
        rw [← χ.changeLevel_primitiveCharacter]
        change DirichletCharacter.changeLevel χ.conductor_dvd_level χ₀ = 1
        rw [h1, DirichletCharacter.changeLevel_one]
      exact hχ this
    set Ce : ℝ := ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ ((1 : ℝ) / 2))
    have hCe_pos : 0 < Ce := Finset.prod_pos fun p hp => by positivity
    set Z32 : ℝ := max (riemannZeta (3 / 2)).re 1
    have hZ32_pos : 0 < Z32 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    set A : ℝ := (f : ℝ) / (2 * Real.pi)
    have hA_pos : 0 < A := by dsimp [A]; positivity
    set C : ℝ := Ce * Z32 * (1 + 3 * A)
    refine ⟨C, 1, by positivity, by norm_num, fun s hs1 hs2 => ?_⟩
    have hs_re1 : -1 / 2 ≤ s.re := by linarith
    have hs_re2 : s.re ≤ 3 / 2 := by linarith
    have hL_eq : χ.LFunction s =
        χ₀.LFunction s * ∏ p ∈ q.primeFactors, (1 - χ₀ p * (p : ℂ) ^ (-s)) := by
      conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
      exact DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ₀ (.inl hχ₀_ne1)
    have hrad := QRHLittlewood.rademacher_convexity f hf3 χ₀ hprim s hs_re1 hs_re2
    have hbase_nn : 0 ≤ (f : ℝ) * ‖1 + s‖ / (2 * Real.pi) := by positivity
    have hexp_nn : 0 ≤ (3 / 2 - s.re) / 2 := by linarith
    have hexp_le1 : (3 / 2 - s.re) / 2 ≤ 1 := by linarith
    have hrpow_le : ((f : ℝ) * ‖1 + s‖ / (2 * Real.pi)) ^ ((3 / 2 - s.re) / 2) ≤
        1 + (f : ℝ) * ‖1 + s‖ / (2 * Real.pi) := by
      by_cases h1 : (f : ℝ) * ‖1 + s‖ / (2 * Real.pi) ≤ 1
      · have := Real.rpow_le_one hbase_nn h1 hexp_nn
        linarith
      · push Not at h1
        have := Real.rpow_le_rpow_of_exponent_le (le_of_lt h1) hexp_le1
        rw [Real.rpow_one] at this
        linarith
    have hnorm1s : ‖1 + s‖ ≤ 3 + |s.im| := by
      have h1 : ‖1 + s‖ ≤ |(1 + s).re| + |(1 + s).im| := Complex.norm_le_abs_re_add_abs_im (1 + s)
      have hre_abs : |(1 + s).re| ≤ 3 := by
        simp only [Complex.add_re, Complex.one_re]
        rw [abs_le]; constructor <;> linarith
      have him_abs : |(1 + s).im| = |s.im| := by simp
      linarith
    have hlin : 1 + (f : ℝ) * ‖1 + s‖ / (2 * Real.pi) ≤ (1 + 3 * A) * Real.exp (|s.im| ^ (1 : ℝ)) := by
      rw [Real.rpow_one]
      have h1 : (f : ℝ) * ‖1 + s‖ / (2 * Real.pi) ≤ A * (3 + |s.im|) := by
        have : (f : ℝ) * ‖1 + s‖ / (2 * Real.pi) = A * ‖1 + s‖ := by dsimp [A]; ring
        rw [this]; exact mul_le_mul_of_nonneg_left hnorm1s (le_of_lt hA_pos)
      have hexp : 1 + |s.im| ≤ Real.exp |s.im| := by linarith [Real.add_one_le_exp |s.im|]
      have hexp1 : 1 ≤ Real.exp |s.im| := Real.one_le_exp (abs_nonneg _)
      nlinarith
    have hrad' : ‖χ₀.LFunction s‖ ≤ Z32 * (1 + 3 * A) * Real.exp (|s.im| ^ (1 : ℝ)) := by
      calc ‖χ₀.LFunction s‖
          ≤ (riemannZeta (3 / 2)).re * ((f : ℝ) * ‖1 + s‖ / (2 * Real.pi)) ^ ((3 / 2 - s.re) / 2) := hrad
        _ ≤ Z32 * ((f : ℝ) * ‖1 + s‖ / (2 * Real.pi)) ^ ((3 / 2 - s.re) / 2) := by
            gcongr; exact le_max_left _ _
        _ ≤ Z32 * (1 + (f : ℝ) * ‖1 + s‖ / (2 * Real.pi)) := by gcongr
        _ ≤ Z32 * ((1 + 3 * A) * Real.exp (|s.im| ^ (1 : ℝ))) := by gcongr
        _ = Z32 * (1 + 3 * A) * Real.exp (|s.im| ^ (1 : ℝ)) := by ring
    rw [hL_eq, norm_mul]
    calc ‖χ₀.LFunction s‖ * ‖∏ p ∈ q.primeFactors, (1 - χ₀ p * (p : ℂ) ^ (-s))‖
        ≤ (Z32 * (1 + 3 * A) * Real.exp (|s.im| ^ (1 : ℝ))) * Ce :=
          mul_le_mul hrad' (norm_euler_prod_le χ₀ hs_re1) (norm_nonneg _) (by positivity)
      _ = C * Real.exp (|s.im| ^ (1 : ℝ)) := by dsimp [C]; ring
