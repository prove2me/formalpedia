-- Prove2me | solution 1 for ImprovedLinBandits.OFUL.oful_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T12:35:56.06086+00:00
-- url     : https://prove2.me/submissions/028e111f-382d-40d0-8008-127228d5e6cf

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_ImprovedLinBandits_OFUL_confidenceSet
import Definitions.Def_ImprovedLinBandits_OFUL_IsOFULRun
import Definitions.Def_ImprovedLinBandits_OFUL_pseudoRegret

set_option autoImplicit false
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_symm_dot {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = A) (v w : Fin d → ℝ) :
    v ⬝ᵥ A *ᵥ w = w ⬝ᵥ A *ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_vecMulVec_mulVec {d : ℕ} (x u : Fin d → ℝ) :
    vecMulVec x x *ᵥ u = (x ⬝ᵥ u) • x := by
  ext i
  simp [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_comm, mul_left_comm]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_posdef_transpose {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) : Vᵀ = V := by
  have := hV.isHermitian
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  exact this

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_inv_transpose {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) : (V⁻¹)ᵀ = V⁻¹ := by
  rw [transpose_nonsing_inv, e5_posdef_transpose hV]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_det_unit {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) : IsUnit V.det :=
  isUnit_iff_ne_zero.mpr hV.det_pos.ne'

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_mulVec_inv {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : IsUnit V.det) (v : Fin d → ℝ) :
    V *ᵥ (V⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, mul_nonsing_inv _ hV, one_mulVec]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_inv_mulVec {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : IsUnit V.det) (v : Fin d → ℝ) :
    V⁻¹ *ᵥ (V *ᵥ v) = v := by
  rw [mulVec_mulVec, nonsing_inv_mul _ hV, one_mulVec]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_a_nonneg {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) (x : Fin d → ℝ) :
    0 ≤ x ⬝ᵥ V⁻¹ *ᵥ x := by
  have := hV.inv.posSemidef.dotProduct_mulVec_nonneg x
  simpa using this

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_det_step {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) (x : Fin d → ℝ) :
    (V + vecMulVec x x).det = V.det * (1 + x ⬝ᵥ V⁻¹ *ᵥ x) := by
  rw [vecMulVec_eq Unit, det_add_replicateCol_mul_replicateRow (e5_det_unit hV)]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply,
    replicateCol_apply, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_quad_step {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) (x S : Fin d → ℝ)
    (e : ℝ) :
    (S + e • x) ⬝ᵥ (V + vecMulVec x x)⁻¹ *ᵥ (S + e • x) =
      S ⬝ᵥ V⁻¹ *ᵥ S + (2 * e * (x ⬝ᵥ V⁻¹ *ᵥ S) + e ^ 2 * (x ⬝ᵥ V⁻¹ *ᵥ x)
        - (x ⬝ᵥ V⁻¹ *ᵥ S) ^ 2) / (1 + x ⬝ᵥ V⁻¹ *ᵥ x) := by
  set a := x ⬝ᵥ V⁻¹ *ᵥ x with ha_def
  set b := x ⬝ᵥ V⁻¹ *ᵥ S with hb_def
  have ha : 0 ≤ a := e5_a_nonneg hV x
  have h1a : (1 + a) ≠ 0 := by positivity
  have hdet : IsUnit V.det := e5_det_unit hV
  have hdet' : IsUnit (V + vecMulVec x x).det := by
    rw [e5_det_step hV]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero hV.det_pos.ne' h1a)
  set u := V⁻¹ *ᵥ S with hu
  set w := V⁻¹ *ᵥ x with hw
  set cc := (e - b) / (1 + a) with hcc
  have hxu : x ⬝ᵥ u = b := rfl
  have hxw : x ⬝ᵥ w = a := rfl
  have hSw : S ⬝ᵥ w = b := by
    rw [hw, hb_def, e5_symm_dot (e5_inv_transpose hV)]
  have h1 : (V + vecMulVec x x) *ᵥ (u + cc • w) = S + e • x := by
    rw [add_mulVec, e5_vecMulVec_mulVec, mulVec_add, mulVec_smul, hu, hw, e5_mulVec_inv hdet,
      e5_mulVec_inv hdet, ← hu, ← hw, dotProduct_add, dotProduct_smul, hxu, hxw, smul_eq_mul,
      add_assoc, ← add_smul]
    congr 2
    rw [hcc]
    field_simp
    ring
  have key : (V + vecMulVec x x)⁻¹ *ᵥ (S + e • x) = u + cc • w := by
    rw [← h1, e5_inv_mulVec hdet']
  rw [key, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct, dotProduct_smul,
    dotProduct_smul, smul_dotProduct, hSw, hxu, hxw]
  simp only [smul_eq_mul]
  rw [hcc]
  field_simp
  ring

open MeasureTheory ProbabilityTheory Matrix NNReal in
/-- Cauchy–Schwarz for a positive semidefinite symmetric form. -/
lemma e5_cs_psd {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosSemidef) (p q : Fin d → ℝ) :
    (p ⬝ᵥ V *ᵥ q) ^ 2 ≤ (p ⬝ᵥ V *ᵥ p) * (q ⬝ᵥ V *ᵥ q) := by
  have hT : Vᵀ = V := by
    have := hV.isHermitian
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hnn : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ V *ᵥ v := fun v => by
    simpa using hV.dotProduct_mulVec_nonneg v
  have h : ∀ τ : ℝ, 0 ≤ (q ⬝ᵥ V *ᵥ q) * (τ * τ) + (2 * (p ⬝ᵥ V *ᵥ q)) * τ + (p ⬝ᵥ V *ᵥ p) := by
    intro τ
    have := hnn (p + τ • q)
    rw [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_dotProduct, dotProduct_smul, e5_symm_dot hT q p] at this
    simp only [smul_eq_mul] at this
    nlinarith [this]
  have := discrim_le_zero h
  rw [discrim] at this
  nlinarith [this]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_cs {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) (x w : Fin d → ℝ) :
    x ⬝ᵥ w ≤ Real.sqrt (x ⬝ᵥ V⁻¹ *ᵥ x) * Real.sqrt (w ⬝ᵥ V *ᵥ w) := by
  have hdet := e5_det_unit hV
  set u := V⁻¹ *ᵥ x with hu
  have hx : x = V *ᵥ u := (e5_mulVec_inv hdet x).symm
  have hA : x ⬝ᵥ V⁻¹ *ᵥ x = u ⬝ᵥ V *ᵥ u := by
    rw [← hu, ← hx, dotProduct_comm]
  have hC : x ⬝ᵥ w = u ⬝ᵥ V *ᵥ w := by
    rw [hx, e5_symm_dot (e5_posdef_transpose hV), dotProduct_comm, ← hx]
  rw [hA, hC]
  have hcs := e5_cs_psd hV.posSemidef u w
  have h1 : 0 ≤ u ⬝ᵥ V *ᵥ u := by simpa using hV.posSemidef.dotProduct_mulVec_nonneg u
  have h2 : 0 ≤ w ⬝ᵥ V *ᵥ w := by simpa using hV.posSemidef.dotProduct_mulVec_nonneg w
  rw [← Real.sqrt_mul h1]
  exact Real.le_sqrt_of_sq_le hcs

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_norm_sub {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosSemidef) (p q : Fin d → ℝ) :
    Real.sqrt ((p - q) ⬝ᵥ V *ᵥ (p - q)) ≤
      Real.sqrt (p ⬝ᵥ V *ᵥ p) + Real.sqrt (q ⬝ᵥ V *ᵥ q) := by
  have hT : Vᵀ = V := by
    have := hV.isHermitian
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have h1 : 0 ≤ p ⬝ᵥ V *ᵥ p := by simpa using hV.dotProduct_mulVec_nonneg p
  have h2 : 0 ≤ q ⬝ᵥ V *ᵥ q := by simpa using hV.dotProduct_mulVec_nonneg q
  have hcs := e5_cs_psd hV p q
  have hexp : (p - q) ⬝ᵥ V *ᵥ (p - q) =
      p ⬝ᵥ V *ᵥ p - 2 * (p ⬝ᵥ V *ᵥ q) + q ⬝ᵥ V *ᵥ q := by
    rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, e5_symm_dot hT q p]
    ring
  have hsq : Real.sqrt (p ⬝ᵥ V *ᵥ p) * Real.sqrt (q ⬝ᵥ V *ᵥ q) ≥ -(p ⬝ᵥ V *ᵥ q) := by
    rw [← Real.sqrt_mul h1]
    have : |p ⬝ᵥ V *ᵥ q| ≤ Real.sqrt ((p ⬝ᵥ V *ᵥ p) * (q ⬝ᵥ V *ᵥ q)) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hcs
    linarith [neg_abs_le (p ⬝ᵥ V *ᵥ q)]
  rw [Real.sqrt_le_left]
  · rw [hexp, add_sq, Real.sq_sqrt h1, Real.sq_sqrt h2]
    nlinarith [hsq]
  · positivity

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_inv_bound {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) {lam : ℝ}
    (hlam : 0 < lam) (hlow : ∀ u : Fin d → ℝ, lam * (u ⬝ᵥ u) ≤ u ⬝ᵥ V *ᵥ u) (x : Fin d → ℝ) :
    x ⬝ᵥ V⁻¹ *ᵥ x ≤ (x ⬝ᵥ x) / lam := by
  have hdet := e5_det_unit hV
  set u := V⁻¹ *ᵥ x with hu
  have hx : x = V *ᵥ u := (e5_mulVec_inv hdet x).symm
  have hq : x ⬝ᵥ u = u ⬝ᵥ V *ᵥ u := by rw [← hx, dotProduct_comm]
  have hlow' := hlow u
  have hcs := e5_cs_psd (PosSemidef.one (n := Fin d) (R := ℝ)) x u
  simp only [one_mulVec] at hcs
  have huu : 0 ≤ u ⬝ᵥ u := by
    have := (PosSemidef.one (n := Fin d) (R := ℝ)).dotProduct_mulVec_nonneg u
    simpa using this
  have hxx : 0 ≤ x ⬝ᵥ x := by
    have := (PosSemidef.one (n := Fin d) (R := ℝ)).dotProduct_mulVec_nonneg x
    simpa using this
  rw [le_div_iff₀ hlam]
  rw [← hq] at hlow'
  have hq0 : 0 ≤ x ⬝ᵥ u := le_trans (by positivity) hlow'
  have h1 : (lam * (x ⬝ᵥ u)) * (x ⬝ᵥ u) ≤ (x ⬝ᵥ x) * (x ⬝ᵥ u) := by
    nlinarith [mul_le_mul_of_nonneg_left hlow' hxx]
  rcases eq_or_lt_of_le hq0 with h | h
  · rw [← h]; simpa using hxx
  · have := le_of_mul_le_mul_right h1 h
    linarith

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_amgm {d : ℕ} (hd : 0 < d) (z : Fin d → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∏ i, z i ≤ ((∑ i, z i) / d) ^ d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => ((d : ℝ))⁻¹) z
    (fun _ _ => by positivity) (by simp [Finset.sum_const, Finset.card_univ]; field_simp)
    (fun i _ => hz i)
  calc ∏ i, z i = ∏ i, (z i ^ ((d : ℝ))⁻¹) ^ d := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Real.rpow_inv_natCast_pow (hz i) hd.ne']
    _ = (∏ i, z i ^ ((d : ℝ))⁻¹) ^ d := Finset.prod_pow _ _ _
    _ ≤ (∑ i, ((d : ℝ))⁻¹ * z i) ^ d :=
        pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hz i) _) h d
    _ = ((∑ i, z i) / d) ^ d := by rw [← Finset.mul_sum, div_eq_inv_mul]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_det_le_trace {d : ℕ} (hd : 0 < d) {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) :
    V.det ≤ (V.trace / d) ^ d := by
  rw [hV.isHermitian.det_eq_prod_eigenvalues, hV.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  exact e5_amgm hd _ fun i => (hV.eigenvalues_pos i).le


open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_gauss (p q r C : ℝ) (hp : 0 < p) (hC : 0 ≤ C) :
    ∫⁻ x : ℝ, ENNReal.ofReal (C * Real.exp (-p * x ^ 2 + q * x + r)) =
      ENNReal.ofReal (C * Real.sqrt (Real.pi / p) * Real.exp (q ^ 2 / (4 * p) + r)) := by
  have hfun : ∀ x : ℝ, C * Real.exp (-p * x ^ 2 + q * x + r) =
      (C * Real.exp (q ^ 2 / (4 * p) + r)) * Real.exp (-p * (x - q / (2 * p)) ^ 2) := by
    intro x
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  have hint : Integrable (fun x : ℝ =>
      (C * Real.exp (q ^ 2 / (4 * p) + r)) * Real.exp (-p * (x - q / (2 * p)) ^ 2)) :=
    ((integrable_exp_neg_mul_sq hp).comp_sub_right (q / (2 * p))).const_mul _
  simp_rw [hfun]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => by positivity)]
  congr 1
  rw [integral_const_mul, integral_sub_right_eq_self (fun x => Real.exp (-p * x ^ 2)),
    integral_gaussian]
  ring

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_oneD {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [SFinite ν] {η : Ω' → ℝ}
    (hη : Measurable η) {c : ℝ} (hc : 0 < c)
    (hmgf : ∀ t : ℝ, ∫⁻ y, ENNReal.ofReal (Real.exp (t * η y)) ∂ν ≤
      ENNReal.ofReal (Real.exp (c * t ^ 2 / 2)))
    {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp ((2 * η y * b + η y ^ 2 * a - b ^ 2) / (2 * c * (1 + a)))
      / Real.sqrt (1 + a)) ∂ν ≤ 1 := by
  have h1a : 0 < 1 + a := by linarith
  set k := Real.sqrt (a / (c * (1 + a))) with hk
  have hk2 : k ^ 2 = a / (c * (1 + a)) := Real.sq_sqrt (by positivity)
  have hck : c * k ^ 2 = a / (1 + a) := by rw [hk2]; field_simp
  set γ := b / (c * (1 + a)) with hγ
  set C1 := Real.exp (-b ^ 2 / (2 * c * (1 + a))) / Real.sqrt (1 + a) / Real.sqrt (2 * Real.pi)
    with hC1
  have hC1nn : 0 ≤ C1 := by positivity
  -- Step 1: Gaussian representation of the integrand
  have hrep : ∀ e : ℝ, ENNReal.ofReal (Real.exp ((2 * e * b + e ^ 2 * a - b ^ 2) /
      (2 * c * (1 + a))) / Real.sqrt (1 + a)) =
      ∫⁻ ξ : ℝ, ENNReal.ofReal (C1 * Real.exp (-(1 / 2) * ξ ^ 2 + (k * e) * ξ + γ * e)) := by
    intro e
    rw [e5_gauss (1 / 2) (k * e) (γ * e) C1 (by norm_num) hC1nn]
    congr 1
    have hpi : Real.sqrt (Real.pi / (1 / 2)) = Real.sqrt (2 * Real.pi) := by
      congr 1; ring
    rw [hpi, hC1]
    have hs2 : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    have hs1 : Real.sqrt (1 + a) ≠ 0 := by positivity
    field_simp
    rw [← Real.exp_add]
    congr 1
    rw [hk2, hγ]
    field_simp
    ring
  simp_rw [hrep]
  -- Step 2: swap the integrals
  have hmeas : Measurable (Function.uncurry fun (y : Ω') (ξ : ℝ) =>
      ENNReal.ofReal (C1 * Real.exp (-(1 / 2) * ξ ^ 2 + (k * η y) * ξ + γ * η y))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.const_mul
    apply Real.measurable_exp.comp
    fun_prop
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  -- Step 3: bound the inner integral with the mgf bound
  have hinner : ∀ ξ : ℝ, ∫⁻ y, ENNReal.ofReal (C1 * Real.exp (-(1 / 2) * ξ ^ 2 +
      (k * η y) * ξ + γ * η y)) ∂ν ≤
      ENNReal.ofReal (C1 * Real.exp (-((1 - c * k ^ 2) / 2) * ξ ^ 2 + (c * k * γ) * ξ
        + c * γ ^ 2 / 2)) := by
    intro ξ
    have hsplit : ∀ y, ENNReal.ofReal (C1 * Real.exp (-(1 / 2) * ξ ^ 2 + (k * η y) * ξ + γ * η y))
        = ENNReal.ofReal (C1 * Real.exp (-(1 / 2) * ξ ^ 2)) *
          ENNReal.ofReal (Real.exp ((k * ξ + γ) * η y)) := by
      intro y
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [mul_assoc C1, ← Real.exp_add]
      congr 2
      ring
    simp_rw [hsplit]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (C1 * Real.exp (-(1 / 2) * ξ ^ 2)) *
          ∫⁻ y, ENNReal.ofReal (Real.exp ((k * ξ + γ) * η y)) ∂ν
        ≤ ENNReal.ofReal (C1 * Real.exp (-(1 / 2) * ξ ^ 2)) *
          ENNReal.ofReal (Real.exp (c * (k * ξ + γ) ^ 2 / 2)) := by gcongr; exact hmgf _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [mul_assoc C1, ← Real.exp_add]
        congr 2
        ring
  have hp' : 0 < (1 - c * k ^ 2) / 2 := by
    rw [hck]
    have : a / (1 + a) < 1 := by rw [div_lt_one h1a]; linarith
    linarith
  calc ∫⁻ ξ : ℝ, ∫⁻ y, ENNReal.ofReal (C1 * Real.exp (-(1 / 2) * ξ ^ 2 + (k * η y) * ξ
        + γ * η y)) ∂ν
      ≤ ∫⁻ ξ : ℝ, ENNReal.ofReal (C1 * Real.exp (-((1 - c * k ^ 2) / 2) * ξ ^ 2
        + (c * k * γ) * ξ + c * γ ^ 2 / 2)) := lintegral_mono hinner
    _ = ENNReal.ofReal (C1 * Real.sqrt (Real.pi / ((1 - c * k ^ 2) / 2)) *
          Real.exp ((c * k * γ) ^ 2 / (4 * ((1 - c * k ^ 2) / 2)) + c * γ ^ 2 / 2)) :=
        e5_gauss _ _ _ _ hp' hC1nn
    _ = 1 := by
        rw [← ENNReal.ofReal_one]
        congr 1
        have h1ck : 1 - c * k ^ 2 = 1 / (1 + a) := by rw [hck]; field_simp; ring
        have hsq : (c * k * γ) ^ 2 = c * (c * k ^ 2) * γ ^ 2 := by ring
        rw [hsq, h1ck, hck]
        have hpi : Real.sqrt (Real.pi / (1 / (1 + a) / 2)) =
            Real.sqrt (2 * Real.pi) * Real.sqrt (1 + a) := by
          rw [← Real.sqrt_mul (by positivity)]
          congr 1
          field_simp
        rw [hpi, hC1]
        have hs2 : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
        have hs1 : Real.sqrt (1 + a) ≠ 0 := by positivity
        field_simp
        rw [← Real.exp_add]
        rw [Real.exp_eq_one_iff]
        rw [hγ]
        field_simp
        ring

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_kcl {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ) {η : Ω → ℝ} (hη : Measurable η)
    {R2 : ℝ≥0} {c : ℝ} (hc : 0 < c) (hRc : (R2 : ℝ) ≤ c)
    (hsg : HasCondSubgaussianMGF m hm η R2 P) {g : Ω → ENNReal} (hg : Measurable[m] g)
    {a b : Ω → ℝ} (ha : Measurable[m] a) (hb : Measurable[m] b) (ha0 : ∀ ω, 0 ≤ a ω) :
    ∫⁻ ω, g ω * ENNReal.ofReal (Real.exp ((2 * η ω * b ω + η ω ^ 2 * a ω - b ω ^ 2) /
      (2 * c * (1 + a ω))) / Real.sqrt (1 + a ω)) ∂P ≤ ∫⁻ ω, g ω ∂P := by
  set φ : ℝ × ℝ × ℝ → ℝ := fun p => Real.exp ((2 * p.2.2 * p.2.1 + p.2.2 ^ 2 * p.1 - p.2.1 ^ 2) /
      (2 * c * (1 + p.1))) / Real.sqrt (1 + p.1) with hφ
  have hφm : Measurable φ := by
    rw [hφ]; fun_prop
  set F : Ω × Ω → ENNReal := fun p => g p.1 * ENNReal.ofReal (φ (a p.1, b p.1, η p.2)) with hF
  have hF_meas : @Measurable (Ω × Ω) ENNReal (m.prod mΩ) _ F := by
    have h1 : @Measurable (Ω × Ω) Ω (m.prod mΩ) m Prod.fst := @measurable_fst Ω Ω m mΩ
    have h2 : @Measurable (Ω × Ω) Ω (m.prod mΩ) mΩ Prod.snd := @measurable_snd Ω Ω m mΩ
    have h3 : @Measurable (Ω × Ω) (ℝ × ℝ × ℝ) (m.prod mΩ) _
        (fun p : Ω × Ω => (a p.1, b p.1, η p.2)) :=
      (ha.comp h1).prodMk ((hb.comp h1).prodMk (hη.comp h2))
    exact (hg.comp h1).mul (ENNReal.measurable_ofReal.comp (hφm.comp h3))
  have hdiag : @Measurable Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag :=
    (measurable_id'' hm).prodMk measurable_id
  have hlhs : ∫⁻ ω, g ω * ENNReal.ofReal (Real.exp ((2 * η ω * b ω + η ω ^ 2 * a ω - b ω ^ 2) /
      (2 * c * (1 + a ω))) / Real.sqrt (1 + a ω)) ∂P = ∫⁻ ω, F (Function.diag ω) ∂P := rfl
  rw [hlhs, ← @lintegral_map Ω (Ω × Ω) mΩ (m.prod mΩ) P F Function.diag hF_meas hdiag,
    ← compProd_trim_condExpKernel hm, Measure.lintegral_compProd hF_meas,
    ← lintegral_trim hm hg]
  refine lintegral_mono_ae ?_
  filter_upwards [hsg.mgf_le, Kernel.HasSubgaussianMGF.ae_forall_integrable_exp_mul hsg]
    with ω hmgf hint
  have hmgf' : ∀ t : ℝ, ∫⁻ y, ENNReal.ofReal (Real.exp (t * η y)) ∂(condExpKernel P m ω) ≤
      ENNReal.ofReal (Real.exp (c * t ^ 2 / 2)) := by
    intro t
    rw [← ofReal_integral_eq_lintegral_ofReal (hint t) (ae_of_all _ fun y => (Real.exp_pos _).le)]
    apply ENNReal.ofReal_le_ofReal
    refine (hmgf t).trans ?_
    apply Real.exp_le_exp.mpr
    have : 0 ≤ t ^ 2 := sq_nonneg t
    nlinarith
  simp only [hF]
  rw [lintegral_const_mul]
  · calc g ω * ∫⁻ y, ENNReal.ofReal (φ (a ω, b ω, η y)) ∂(condExpKernel P m ω)
        ≤ g ω * 1 := by
          gcongr
          exact e5_oneD (condExpKernel P m ω) hη hc hmgf' (ha0 ω) (b ω)
      _ = g ω := mul_one _
  · exact ENNReal.measurable_ofReal.comp (hφm.comp
      (measurable_const.prodMk (measurable_const.prodMk hη)))

open MeasureTheory ProbabilityTheory Matrix NNReal in
/-- A Ville-type maximal inequality obtained from a one-step supermartingale inequality. -/
lemma e5_ville {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (Z : ℕ → Ω → ℝ) (hZm : ∀ t, Measurable[ℱ t] (Z t))
    (hZ0 : ∀ ω, Z 0 ω = 1)
    (hstep : ∀ t (A : Set Ω), MeasurableSet[ℱ t] A →
      ∫⁻ ω in A, ENNReal.ofReal (Z (t + 1) ω) ∂P ≤ ∫⁻ ω in A, ENNReal.ofReal (Z t ω) ∂P)
    {δ : ℝ} (hδ : 0 < δ) :
    P {ω | ∃ t, 1 / δ < Z t ω} ≤ ENNReal.ofReal δ := by
  set G : ℕ → Set Ω := fun t => {ω | ∀ s, s < t → Z s ω ≤ 1 / δ} with hG
  set E : ℕ → Set Ω := fun t => {ω | (∀ s, s < t → Z s ω ≤ 1 / δ) ∧ 1 / δ < Z t ω} with hE
  have hZm' : ∀ s t, s ≤ t → Measurable[ℱ t] (Z s) := fun s t hst =>
    (hZm s).mono (ℱ.mono hst) le_rfl
  have hGm : ∀ t, MeasurableSet[ℱ t] (G (t + 1)) := by
    intro t
    have : G (t + 1) = ⋂ s ∈ Finset.range (t + 1), (Z s) ⁻¹' Set.Iic (1 / δ) := by
      ext ω; simp [hG]
    rw [this]
    exact Finset.measurableSet_biInter _ fun s hs =>
      hZm' s t (by simpa [Nat.lt_succ_iff] using hs) measurableSet_Iic
  have hGm' : ∀ t, MeasurableSet (G (t + 1)) := fun t => ℱ.le t _ (hGm t)
  have hEm : ∀ t, MeasurableSet (E t) := by
    intro t
    have : E t = (⋂ s ∈ Finset.range t, (Z s) ⁻¹' Set.Iic (1 / δ)) ∩ (Z t) ⁻¹' Set.Ioi (1 / δ) := by
      ext ω; simp [hE]
    rw [this]
    refine MeasurableSet.inter (Finset.measurableSet_biInter _ fun s hs =>
      ℱ.le t _ (hZm' s t (by simp at hs; omega) measurableSet_Iic)) ?_
    exact ℱ.le t _ (hZm t measurableSet_Ioi)
  have hsplit : ∀ t, G t = E t ∪ G (t + 1) := by
    intro t
    ext ω
    simp only [hG, hE, Set.mem_union]
    constructor
    · intro h
      by_cases hz : 1 / δ < Z t ω
      · exact Or.inl ⟨h, hz⟩
      · refine Or.inr fun s hs => ?_
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
        · exact h s hs
        · rw [hs]; exact le_of_not_gt hz
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact fun s hs => h s (Nat.lt_succ_of_lt hs)
  have hdisj : ∀ t, Disjoint (E t) (G (t + 1)) := by
    intro t
    rw [Set.disjoint_left]
    intro ω h1 h2
    exact absurd (h2 t (Nat.lt_succ_self t)) (not_le.mpr h1.2)
  have hclaim : ∀ t, (∑ s ∈ Finset.range t, ∫⁻ ω in E s, ENNReal.ofReal (Z s ω) ∂P) +
      ∫⁻ ω in G t, ENNReal.ofReal (Z t ω) ∂P ≤ 1 := by
    intro t
    induction t with
    | zero =>
      have : G 0 = Set.univ := by ext ω; simp [hG]
      simp [this, hZ0]
    | succ t ih =>
      rw [Finset.sum_range_succ]
      have hu : ∫⁻ ω in G t, ENNReal.ofReal (Z t ω) ∂P =
          ∫⁻ ω in E t, ENNReal.ofReal (Z t ω) ∂P + ∫⁻ ω in G (t + 1), ENNReal.ofReal (Z t ω) ∂P := by
        rw [hsplit t]
        exact lintegral_union (hGm' t) (hdisj t)
      calc (∑ s ∈ Finset.range t, ∫⁻ ω in E s, ENNReal.ofReal (Z s ω) ∂P) +
            ∫⁻ ω in E t, ENNReal.ofReal (Z t ω) ∂P +
            ∫⁻ ω in G (t + 1), ENNReal.ofReal (Z (t + 1) ω) ∂P
          ≤ (∑ s ∈ Finset.range t, ∫⁻ ω in E s, ENNReal.ofReal (Z s ω) ∂P) +
            ∫⁻ ω in E t, ENNReal.ofReal (Z t ω) ∂P +
            ∫⁻ ω in G (t + 1), ENNReal.ofReal (Z t ω) ∂P := by
            exact add_le_add le_rfl (hstep t _ (hGm t))
        _ = (∑ s ∈ Finset.range t, ∫⁻ ω in E s, ENNReal.ofReal (Z s ω) ∂P) +
            ∫⁻ ω in G t, ENNReal.ofReal (Z t ω) ∂P := by rw [hu, add_assoc]
        _ ≤ 1 := ih
  have hPE : ∀ t, P (E t) ≤ ENNReal.ofReal δ * ∫⁻ ω in E t, ENNReal.ofReal (Z t ω) ∂P := by
    intro t
    have h1 : ENNReal.ofReal (1 / δ) * P (E t) ≤ ∫⁻ ω in E t, ENNReal.ofReal (Z t ω) ∂P := by
      rw [← setLIntegral_const]
      exact setLIntegral_mono' (hEm t) fun ω hω => ENNReal.ofReal_le_ofReal hω.2.le
    calc P (E t) = ENNReal.ofReal δ * (ENNReal.ofReal (1 / δ) * P (E t)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hδ.le, mul_one_div_cancel hδ.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ _ := by gcongr
  have hsub : {ω | ∃ t, 1 / δ < Z t ω} ⊆ ⋃ t, E t := by
    intro ω hω
    classical
    have hex : ∃ t, 1 / δ < Z t ω := hω
    refine Set.mem_iUnion.mpr ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
    intro s hs
    exact le_of_not_gt (Nat.find_min hex hs)
  calc P {ω | ∃ t, 1 / δ < Z t ω} ≤ P (⋃ t, E t) := measure_mono hsub
    _ ≤ ∑' t, P (E t) := measure_iUnion_le _
    _ = ⨆ n, ∑ t ∈ Finset.range n, P (E t) := ENNReal.tsum_eq_iSup_nat
    _ ≤ ENNReal.ofReal δ := by
        refine iSup_le fun n => ?_
        calc ∑ t ∈ Finset.range n, P (E t)
            ≤ ∑ t ∈ Finset.range n, ENNReal.ofReal δ * ∫⁻ ω in E t, ENNReal.ofReal (Z t ω) ∂P :=
              Finset.sum_le_sum fun t _ => hPE t
          _ = ENNReal.ofReal δ * ∑ t ∈ Finset.range n, ∫⁻ ω in E t, ENNReal.ofReal (Z t ω) ∂P := by
              rw [Finset.mul_sum]
          _ ≤ ENNReal.ofReal δ * 1 := by
              gcongr
              exact le_trans le_self_add (hclaim n)
          _ = ENNReal.ofReal δ := mul_one _

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_V_succ {Ω : Type*} (d : ℕ) (lam : ℝ) (X : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) :
    BanditAlgorithm.regularizedDesignMatrix d lam X (t + 1) ω =
      BanditAlgorithm.regularizedDesignMatrix d lam X t ω + vecMulVec (X (t + 1) ω) (X (t + 1) ω) := by
  unfold BanditAlgorithm.regularizedDesignMatrix
  rw [Finset.sum_range_succ, add_assoc]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_V_zero {Ω : Type*} (d : ℕ) (lam : ℝ) (X : ℕ → Ω → Fin d → ℝ) (ω : Ω) :
    BanditAlgorithm.regularizedDesignMatrix d lam X 0 ω = lam • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  unfold BanditAlgorithm.regularizedDesignMatrix
  simp

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_S_succ {Ω : Type*} (d : ℕ) (η : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) :
    BanditAlgorithm.selfNormalizedSum d η X (t + 1) ω =
      BanditAlgorithm.selfNormalizedSum d η X t ω + η (t + 1) ω • X (t + 1) ω := by
  unfold BanditAlgorithm.selfNormalizedSum
  rw [Finset.sum_range_succ]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_S_zero {Ω : Type*} (d : ℕ) (η : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin d → ℝ) (ω : Ω) :
    BanditAlgorithm.selfNormalizedSum d η X 0 ω = 0 := by
  unfold BanditAlgorithm.selfNormalizedSum
  simp

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_V_quad {Ω : Type*} (d : ℕ) (lam : ℝ) (X : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω)
    (u : Fin d → ℝ) :
    u ⬝ᵥ BanditAlgorithm.regularizedDesignMatrix d lam X t ω *ᵥ u =
      lam * (u ⬝ᵥ u) + ∑ s ∈ Finset.range t, (X (s + 1) ω ⬝ᵥ u) ^ 2 := by
  induction t with
  | zero =>
    rw [e5_V_zero]
    simp [smul_mulVec]
  | succ t ih =>
    rw [e5_V_succ, add_mulVec, dotProduct_add, ih, e5_vecMulVec_mulVec, dotProduct_smul,
      Finset.sum_range_succ, smul_eq_mul, dotProduct_comm u (X (t + 1) ω)]
    ring

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_V_transpose {Ω : Type*} (d : ℕ) (lam : ℝ) (X : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) :
    (BanditAlgorithm.regularizedDesignMatrix d lam X t ω)ᵀ =
      BanditAlgorithm.regularizedDesignMatrix d lam X t ω := by
  induction t with
  | zero => rw [e5_V_zero]; simp
  | succ t ih => rw [e5_V_succ, transpose_add, ih, transpose_vecMulVec]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_dot_self_nonneg {d : ℕ} (u : Fin d → ℝ) : 0 ≤ u ⬝ᵥ u :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_V_posdef {Ω : Type*} (d : ℕ) {lam : ℝ} (hlam : 0 < lam) (X : ℕ → Ω → Fin d → ℝ)
    (t : ℕ) (ω : Ω) : (BanditAlgorithm.regularizedDesignMatrix d lam X t ω).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, e5_V_transpose]
  · intro u hu
    rw [star_trivial, e5_V_quad]
    have h1 : 0 < u ⬝ᵥ u := by
      rcases (e5_dot_self_nonneg u).lt_or_eq with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.mp h.symm) hu
    have h2 : 0 ≤ ∑ s ∈ Finset.range t, (X (s + 1) ω ⬝ᵥ u) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_V_low {Ω : Type*} (d : ℕ) (lam : ℝ) (X : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω)
    (u : Fin d → ℝ) :
    lam * (u ⬝ᵥ u) ≤ u ⬝ᵥ BanditAlgorithm.regularizedDesignMatrix d lam X t ω *ᵥ u := by
  rw [e5_V_quad]
  have : 0 ≤ ∑ s ∈ Finset.range t, (X (s + 1) ω ⬝ᵥ u) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_V_trace {Ω : Type*} (d : ℕ) (lam : ℝ) (X : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) :
    (BanditAlgorithm.regularizedDesignMatrix d lam X t ω).trace =
      lam * d + ∑ s ∈ Finset.range t, X (s + 1) ω ⬝ᵥ X (s + 1) ω := by
  induction t with
  | zero => rw [e5_V_zero]; simp
  | succ t ih =>
    rw [e5_V_succ, trace_add, ih, Finset.sum_range_succ]
    have : (vecMulVec (X (t + 1) ω) (X (t + 1) ω)).trace = X (t + 1) ω ⬝ᵥ X (t + 1) ω := by
      simp [Matrix.trace, vecMulVec_apply, dotProduct]
    rw [this]
    ring

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_V_det {Ω : Type*} (d : ℕ) {lam : ℝ} (hlam : 0 < lam) (X : ℕ → Ω → Fin d → ℝ)
    (t : ℕ) (ω : Ω) :
    (BanditAlgorithm.regularizedDesignMatrix d lam X t ω).det = lam ^ d *
      ∏ s ∈ Finset.range t, (1 + X (s + 1) ω ⬝ᵥ
        (BanditAlgorithm.regularizedDesignMatrix d lam X s ω)⁻¹ *ᵥ X (s + 1) ω) := by
  induction t with
  | zero => rw [e5_V_zero]; simp
  | succ t ih =>
    rw [e5_V_succ, e5_det_step (e5_V_posdef d hlam X t ω), ih, Finset.prod_range_succ, mul_assoc]

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_meas_det {Ω : Type*} [MeasurableSpace Ω] {n : Type*} [Fintype n] [DecidableEq n]
    {M : Ω → Matrix n n ℝ} (hM : ∀ i j, Measurable fun ω => M ω i j) :
    Measurable fun ω => (M ω).det := by
  simp_rw [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact Finset.measurable_sum _ fun σ _ =>
    measurable_const.mul (Finset.measurable_prod _ fun i _ => hM _ _)

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_meas_inv {Ω : Type*} [MeasurableSpace Ω] {n : Type*} [Fintype n] [DecidableEq n]
    {M : Ω → Matrix n n ℝ} (hM : ∀ i j, Measurable fun ω => M ω i j) (i j : n) :
    Measurable fun ω => (M ω)⁻¹ i j := by
  simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
    Matrix.adjugate_apply]
  refine (e5_meas_det hM).inv.mul (e5_meas_det fun k l => ?_)
  simp only [updateRow_apply]
  by_cases h : k = j
  · simp only [h, if_true]; exact measurable_const
  · simp only [h, if_false]; exact hM k l

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_meas_quad {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {M : Ω → Matrix (Fin d) (Fin d) ℝ} (hM : ∀ i j, Measurable fun ω => M ω i j)
    {v w : Ω → Fin d → ℝ} (hv : Measurable v) (hw : Measurable w) :
    Measurable fun ω => v ω ⬝ᵥ M ω *ᵥ w ω := by
  simp only [dotProduct, mulVec]
  refine Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hv).mul ?_
  exact Finset.measurable_sum _ fun j _ => (hM i j).mul ((measurable_pi_apply j).comp hw)

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_meas_V {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (lam : ℝ) (X : ℕ → Ω → Fin d → ℝ)
    (t : ℕ) (hX : ∀ s, s < t → Measurable (X (s + 1))) (i j : Fin d) :
    Measurable fun ω => BanditAlgorithm.regularizedDesignMatrix d lam X t ω i j := by
  simp only [BanditAlgorithm.regularizedDesignMatrix, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sum_apply, vecMulVec_apply, smul_eq_mul]
  refine measurable_const.add (Finset.measurable_sum _ fun s hs => ?_)
  have hs' : s < t := Finset.mem_range.mp hs
  exact ((measurable_pi_apply i).comp (hX s hs')).mul ((measurable_pi_apply j).comp (hX s hs'))

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_meas_S {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (η : ℕ → Ω → ℝ)
    (X : ℕ → Ω → Fin d → ℝ) (t : ℕ) (hX : ∀ s, s < t → Measurable (X (s + 1)))
    (hη : ∀ s, s < t → Measurable (η (s + 1))) :
    Measurable fun ω => BanditAlgorithm.selfNormalizedSum d η X t ω := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [BanditAlgorithm.selfNormalizedSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun s hs => ?_
  have hs' : s < t := Finset.mem_range.mp hs
  exact (hη s hs').mul ((measurable_pi_apply i).comp (hX s hs'))

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_Z_succ {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) (x S : Fin d → ℝ)
    (e c K : ℝ) (hc : 0 < c) :
    Real.exp (((S + e • x) ⬝ᵥ (V + vecMulVec x x)⁻¹ *ᵥ (S + e • x)) / (2 * c)) /
        (Real.sqrt (V + vecMulVec x x).det * K) =
      Real.exp ((S ⬝ᵥ V⁻¹ *ᵥ S) / (2 * c)) / (Real.sqrt V.det * K) *
        (Real.exp ((2 * e * (x ⬝ᵥ V⁻¹ *ᵥ S) + e ^ 2 * (x ⬝ᵥ V⁻¹ *ᵥ x) - (x ⬝ᵥ V⁻¹ *ᵥ S) ^ 2) /
          (2 * c * (1 + x ⬝ᵥ V⁻¹ *ᵥ x))) / Real.sqrt (1 + x ⬝ᵥ V⁻¹ *ᵥ x)) := by
  have ha := e5_a_nonneg hV x
  have hdet := hV.det_pos
  rw [e5_det_step hV, e5_quad_step hV, Real.sqrt_mul hdet.le]
  have h1 : (S ⬝ᵥ V⁻¹ *ᵥ S + (2 * e * (x ⬝ᵥ V⁻¹ *ᵥ S) + e ^ 2 * (x ⬝ᵥ V⁻¹ *ᵥ x) -
      (x ⬝ᵥ V⁻¹ *ᵥ S) ^ 2) / (1 + x ⬝ᵥ V⁻¹ *ᵥ x)) / (2 * c) =
      (S ⬝ᵥ V⁻¹ *ᵥ S) / (2 * c) + (2 * e * (x ⬝ᵥ V⁻¹ *ᵥ S) + e ^ 2 * (x ⬝ᵥ V⁻¹ *ᵥ x) -
      (x ⬝ᵥ V⁻¹ *ᵥ S) ^ 2) / (2 * c * (1 + x ⬝ᵥ V⁻¹ *ᵥ x)) := by
    field_simp
  rw [h1, Real.exp_add]
  ring

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_lsq {Ω : Type*} (d : ℕ) {lam : ℝ} (hlam : 0 < lam) (X : ℕ → Ω → Fin d → ℝ)
    (η Y : ℕ → Ω → ℝ) (θstar : Fin d → ℝ)
    (hY : ∀ (t : ℕ) (ω : Ω), Y (t + 1) ω = X (t + 1) ω ⬝ᵥ θstar + η (t + 1) ω) (t : ℕ) (ω : Ω) :
    BanditAlgorithm.regularizedLeastSquares d lam X Y t ω - θstar =
      (BanditAlgorithm.regularizedDesignMatrix d lam X t ω)⁻¹ *ᵥ
        (BanditAlgorithm.selfNormalizedSum d η X t ω - lam • θstar) := by
  have hdet := e5_det_unit (e5_V_posdef d hlam X t ω)
  set V := BanditAlgorithm.regularizedDesignMatrix d lam X t ω with hV
  have hVθ : V *ᵥ θstar = lam • θstar +
      ∑ s ∈ Finset.range t, (X (s + 1) ω ⬝ᵥ θstar) • X (s + 1) ω := by
    rw [hV, BanditAlgorithm.regularizedDesignMatrix, add_mulVec, smul_mulVec, one_mulVec,
      sum_mulVec]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [e5_vecMulVec_mulVec]
  have hsum : ∑ s ∈ Finset.range t, Y (s + 1) ω • X (s + 1) ω =
      V *ᵥ θstar + (BanditAlgorithm.selfNormalizedSum d η X t ω - lam • θstar) := by
    rw [hVθ, BanditAlgorithm.selfNormalizedSum]
    simp only [hY, add_smul, Finset.sum_add_distrib]
    abel
  rw [BanditAlgorithm.regularizedLeastSquares, ← hV, hsum, mulVec_add, e5_inv_mulVec hdet]
  abel

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_det_ge {Ω : Type*} (d : ℕ) {lam : ℝ} (hlam : 0 < lam) (X : ℕ → Ω → Fin d → ℝ)
    (t : ℕ) (ω : Ω) :
    (lam • (1 : Matrix (Fin d) (Fin d) ℝ)).det ≤
      (BanditAlgorithm.regularizedDesignMatrix d lam X t ω).det := by
  induction t with
  | zero => rw [e5_V_zero]
  | succ t ih =>
    rw [e5_V_succ, e5_det_step (e5_V_posdef d hlam X t ω)]
    have h1 := e5_a_nonneg (e5_V_posdef d hlam X t ω) (X (t + 1) ω)
    have h2 := (e5_V_posdef d hlam X t ω).det_pos
    nlinarith

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_link {Ω : Type*} {d : ℕ} (X : ℕ → Ω → Fin d → ℝ) (η Y : ℕ → Ω → ℝ)
    (θstar : Fin d → ℝ) (R : ℝ≥0) {S lam δ : ℝ} (hlam : 1 ≤ lam)
    (hS : Real.sqrt (θstar ⬝ᵥ θstar) ≤ S)
    (hY : ∀ (t : ℕ) (ω : Ω), Y (t + 1) ω = X (t + 1) ω ⬝ᵥ θstar + η (t + 1) ω)
    (hδ : 0 < δ) (hδ1 : δ < 1) (t : ℕ) (ω : Ω)
    (hbad : θstar ∉ ImprovedLinBandits.OFUL.confidenceSet d R S lam δ X Y t ω) :
    ∃ m : ℕ, 1 / δ < Real.exp ((BanditAlgorithm.selfNormalizedSum d η X t ω ⬝ᵥ
        (BanditAlgorithm.regularizedDesignMatrix d lam X t ω)⁻¹ *ᵥ
          BanditAlgorithm.selfNormalizedSum d η X t ω) / (2 * ((R : ℝ) ^ 2 + 1 / ((m : ℝ) + 1)))) /
      (Real.sqrt (BanditAlgorithm.regularizedDesignMatrix d lam X t ω).det *
        (Real.sqrt (lam • (1 : Matrix (Fin d) (Fin d) ℝ)).det)⁻¹) := by
  have hlam0 : 0 < lam := by linarith
  have hVpd := e5_V_posdef d hlam0 X t ω
  have hdet := e5_det_unit hVpd
  have hS0 : 0 ≤ S := le_trans (Real.sqrt_nonneg _) hS
  set V := BanditAlgorithm.regularizedDesignMatrix d lam X t ω with hV
  set Sn := BanditAlgorithm.selfNormalizedSum d η X t ω with hSn
  set Q := Sn ⬝ᵥ V⁻¹ *ᵥ Sn with hQ
  have hQ0 : 0 ≤ Q := e5_a_nonneg hVpd Sn
  have hdl : (lam • (1 : Matrix (Fin d) (Fin d) ℝ)).det = lam ^ d := by simp
  have hdl0 : 0 < (lam • (1 : Matrix (Fin d) (Fin d) ℝ)).det := by rw [hdl]; positivity
  have hge := e5_det_ge d hlam0 X t ω
  rw [← hV] at hge
  set qq := Real.sqrt V.det * (Real.sqrt (lam • (1 : Matrix (Fin d) (Fin d) ℝ)).det)⁻¹ with hqq
  have hsq0 : 0 < Real.sqrt (lam • (1 : Matrix (Fin d) (Fin d) ℝ)).det := Real.sqrt_pos.mpr hdl0
  have hqq1 : 1 ≤ qq := by
    rw [hqq, ← div_eq_mul_inv, le_div_iff₀ hsq0, one_mul]
    exact Real.sqrt_le_sqrt hge
  have hqq0 : 0 < qq := by linarith
  -- unpack the failure of membership
  simp only [ImprovedLinBandits.OFUL.confidenceSet, Set.mem_ofPred_eq, not_le,
    ImprovedLinBandits.OFUL.confidenceRadius] at hbad
  rw [e5_lsq d hlam0 X η Y θstar hY t ω, ← hV, ← hSn, mulVec_sub, mulVec_smul] at hbad
  rw [← hqq] at hbad
  have htri := e5_norm_sub hVpd.posSemidef (V⁻¹ *ᵥ Sn) (lam • V⁻¹ *ᵥ θstar)
  have hp : (V⁻¹ *ᵥ Sn) ⬝ᵥ V *ᵥ (V⁻¹ *ᵥ Sn) = Q := by
    rw [e5_mulVec_inv hdet, dotProduct_comm]
  have hq : (lam • V⁻¹ *ᵥ θstar) ⬝ᵥ V *ᵥ (lam • V⁻¹ *ᵥ θstar) ≤ lam * S ^ 2 := by
    rw [mulVec_smul, e5_mulVec_inv hdet, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, dotProduct_comm]
    have hb := e5_inv_bound hVpd hlam0 (e5_V_low d lam X t ω) θstar
    have hθ0 := e5_dot_self_nonneg θstar
    have hθS : θstar ⬝ᵥ θstar ≤ S ^ 2 := by
      calc θstar ⬝ᵥ θstar = Real.sqrt (θstar ⬝ᵥ θstar) ^ 2 := (Real.sq_sqrt hθ0).symm
        _ ≤ S ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hS 2
    have h1 : lam * (lam * (θstar ⬝ᵥ V⁻¹ *ᵥ θstar)) ≤ lam * (lam * ((θstar ⬝ᵥ θstar) / lam)) := by
      gcongr
    have h2 : lam * (lam * ((θstar ⬝ᵥ θstar) / lam)) = lam * (θstar ⬝ᵥ θstar) := by
      field_simp
    nlinarith
  have hqs : Real.sqrt ((lam • V⁻¹ *ᵥ θstar) ⬝ᵥ V *ᵥ (lam • V⁻¹ *ᵥ θstar)) ≤ Real.sqrt lam * S := by
    calc _ ≤ Real.sqrt (lam * S ^ 2) := Real.sqrt_le_sqrt hq
      _ = Real.sqrt lam * S := by rw [Real.sqrt_mul hlam0.le, Real.sqrt_sq hS0]
  rw [hp] at htri
  -- so R * sqrt(2 ℓ) < sqrt Q
  set ℓ := Real.log (qq / δ) with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hlt : (R : ℝ) * Real.sqrt (2 * ℓ) < Real.sqrt Q := by linarith
  have hlt2 : (R : ℝ) ^ 2 * (2 * ℓ) < Q := by
    have h := pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hQ0] at h
    exact h
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < (Q - (R : ℝ) ^ 2 * (2 * ℓ)) / (2 * ℓ) by
    apply div_pos <;> linarith)
  refine ⟨m, ?_⟩
  have hc : 0 < (R : ℝ) ^ 2 + 1 / ((m : ℝ) + 1) := by positivity
  have hkey : ℓ < Q / (2 * ((R : ℝ) ^ 2 + 1 / ((m : ℝ) + 1))) := by
    rw [lt_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hm
    nlinarith
  have hexp : qq / δ < Real.exp (Q / (2 * ((R : ℝ) ^ 2 + 1 / ((m : ℝ) + 1)))) := by
    calc qq / δ = Real.exp ℓ := (Real.exp_log (by positivity)).symm
      _ < _ := Real.exp_lt_exp.mpr hkey
  rw [lt_div_iff₀ hqq0]
  calc 1 / δ * qq = qq / δ := by ring
    _ < _ := hexp

open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma e5_regret {Ω : Type*} {d : ℕ} (D : ℕ → Ω → Set (Fin d → ℝ))
    (X : ℕ → Ω → Fin d → ℝ) (Y : ℕ → Ω → ℝ) (θtilde : ℕ → Ω → Fin d → ℝ) (θstar : Fin d → ℝ)
    (R : ℝ≥0) {S lam L δ : ℝ} (hd : 0 < d)
    (hS : Real.sqrt (θstar ⬝ᵥ θstar) ≤ S)
    (hL : ∀ (t : ℕ) (ω : Ω), Real.sqrt (X (t + 1) ω ⬝ᵥ X (t + 1) ω) ≤ L)
    (hlam_one : 1 ≤ lam) (hlam_L : L ^ 2 ≤ lam)
    (hD : ∀ (t : ℕ) (ω : Ω), (D (t + 1) ω).Nonempty)
    (hrun : ImprovedLinBandits.OFUL.IsOFULRun d R S lam δ D X Y θtilde)
    (hδ : 0 < δ) (ω : Ω)
    (hgood : ∀ t, θstar ∈ ImprovedLinBandits.OFUL.confidenceSet d R S lam δ X Y t ω) (n : ℕ) :
    ImprovedLinBandits.OFUL.pseudoRegret d D X θstar n ω ≤
      4 * Real.sqrt ((n : ℝ) * d * Real.log (lam + (n : ℝ) * L ^ 2 / d)) *
            (Real.sqrt lam * S + (R : ℝ) * Real.sqrt (2 * Real.log (1 / δ)
              + (d : ℝ) * Real.log (1 + (n : ℝ) * L ^ 2 / (lam * d)))) := by
  have hlam : 0 < lam := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hL0 : 0 ≤ L := le_trans (Real.sqrt_nonneg _) (hL 0 ω)
  have hS0 : 0 ≤ S := le_trans (Real.sqrt_nonneg _) hS
  have hR0 : (0 : ℝ) ≤ R := R.2
  have hVpd : ∀ t, (BanditAlgorithm.regularizedDesignMatrix d lam X t ω).PosDef :=
    fun t => e5_V_posdef d hlam X t ω
  set a : ℕ → ℝ := fun t => X (t + 1) ω ⬝ᵥ
    (BanditAlgorithm.regularizedDesignMatrix d lam X t ω)⁻¹ *ᵥ X (t + 1) ω with hadef
  have ha0 : ∀ t, 0 ≤ a t := fun t => e5_a_nonneg (hVpd t) _
  have hxx : ∀ t, X (t + 1) ω ⬝ᵥ X (t + 1) ω ≤ L ^ 2 := by
    intro t
    have h := hL t ω
    have h0 := e5_dot_self_nonneg (X (t + 1) ω)
    calc X (t + 1) ω ⬝ᵥ X (t + 1) ω = Real.sqrt (X (t + 1) ω ⬝ᵥ X (t + 1) ω) ^ 2 :=
          (Real.sq_sqrt h0).symm
      _ ≤ L ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  have ha1 : ∀ t, a t ≤ 1 := by
    intro t
    have := e5_inv_bound (hVpd t) hlam (e5_V_low d lam X t ω) (X (t + 1) ω)
    calc a t ≤ (X (t + 1) ω ⬝ᵥ X (t + 1) ω) / lam := this
      _ ≤ L ^ 2 / lam := by gcongr; exact hxx t
      _ ≤ 1 := by rw [div_le_one hlam]; exact hlam_L
  set ℓ1 := Real.log (1 + (n : ℝ) * L ^ 2 / (lam * d)) with hℓ1
  set ℓ2 := Real.log (lam + (n : ℝ) * L ^ 2 / d) with hℓ2
  have hy0 : 0 ≤ (n : ℝ) * L ^ 2 / d := by positivity
  have hy1 : 0 ≤ (n : ℝ) * L ^ 2 / (lam * d) := by positivity
  have hℓ1nn : 0 ≤ ℓ1 := Real.log_nonneg (by linarith)
  have hℓ12 : ℓ1 ≤ ℓ2 := by
    apply Real.log_le_log (by positivity)
    have h1 : (n : ℝ) * L ^ 2 / (lam * d) = ((n : ℝ) * L ^ 2 / d) / lam := by
      field_simp
    rw [h1]
    have : ((n : ℝ) * L ^ 2 / d) / lam ≤ (n : ℝ) * L ^ 2 / d := div_le_self hy0 hlam_one
    linarith
  -- determinant bound
  have hdetle : ∀ t, t ≤ n → (BanditAlgorithm.regularizedDesignMatrix d lam X t ω).det ≤
      lam ^ d * (1 + (n : ℝ) * L ^ 2 / (lam * d)) ^ d := by
    intro t ht
    have h1 := e5_det_le_trace hd (hVpd t)
    have htr : (BanditAlgorithm.regularizedDesignMatrix d lam X t ω).trace ≤
        lam * d + n * L ^ 2 := by
      rw [e5_V_trace]
      have hs : ∑ s ∈ Finset.range t, X (s + 1) ω ⬝ᵥ X (s + 1) ω ≤
          ∑ s ∈ Finset.range t, L ^ 2 := Finset.sum_le_sum fun s _ => hxx s
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
      have htn : (t : ℝ) ≤ n := by exact_mod_cast ht
      have : (t : ℝ) * L ^ 2 ≤ n * L ^ 2 := mul_le_mul_of_nonneg_right htn (sq_nonneg L)
      linarith
    have htr0 : 0 ≤ (BanditAlgorithm.regularizedDesignMatrix d lam X t ω).trace :=
      (hVpd t).posSemidef.trace_nonneg
    have h2 : (BanditAlgorithm.regularizedDesignMatrix d lam X t ω).trace / d ≤
        lam * (1 + (n : ℝ) * L ^ 2 / (lam * d)) := by
      rw [div_le_iff₀ hdR]
      have : lam * (1 + (n : ℝ) * L ^ 2 / (lam * d)) * d = lam * d + n * L ^ 2 := by
        field_simp
      rw [this]; exact htr
    calc _ ≤ _ := h1
      _ ≤ (lam * (1 + (n : ℝ) * L ^ 2 / (lam * d))) ^ d :=
          pow_le_pow_left₀ (div_nonneg htr0 hdR.le) h2 d
      _ = _ := mul_pow _ _ _
  have hlogdet : ∀ t, t ≤ n →
      Real.log ((BanditAlgorithm.regularizedDesignMatrix d lam X t ω).det / lam ^ d) ≤ d * ℓ1 := by
    intro t ht
    have hDpos := (hVpd t).det_pos
    rw [hℓ1, ← Real.log_pow]
    apply Real.log_le_log (div_pos hDpos (pow_pos hlam d))
    rw [div_le_iff₀ (pow_pos hlam d)]
    linarith [hdetle t ht]
  -- per-round bound
  set B := Real.sqrt lam * S + (R : ℝ) * Real.sqrt (2 * Real.log (1 / δ) + (d : ℝ) * ℓ1) with hB
  have hB0 : 0 ≤ B := by positivity
  have hβ : ∀ t, t ≤ n → ImprovedLinBandits.OFUL.confidenceRadius d R S lam δ X t ω ≤ B := by
    intro t ht
    have hDpos := (hVpd t).det_pos
    have hdl : (lam • (1 : Matrix (Fin d) (Fin d) ℝ)).det = lam ^ d := by simp
    simp only [ImprovedLinBandits.OFUL.confidenceRadius, hB, hdl]
    set qq := Real.sqrt (BanditAlgorithm.regularizedDesignMatrix d lam X t ω).det *
      (Real.sqrt (lam ^ d))⁻¹ with hqq
    have hqq0 : 0 < qq := by positivity
    have hqq2 : qq ^ 2 = (BanditAlgorithm.regularizedDesignMatrix d lam X t ω).det / lam ^ d := by
      rw [hqq, mul_pow, inv_pow, Real.sq_sqrt hDpos.le, Real.sq_sqrt (by positivity),
        div_eq_mul_inv]
    have hlog : 2 * Real.log (qq / δ) =
        Real.log ((BanditAlgorithm.regularizedDesignMatrix d lam X t ω).det / lam ^ d) +
          2 * Real.log (1 / δ) := by
      rw [Real.log_div hqq0.ne' hδ.ne', one_div, Real.log_inv, ← hqq2, Real.log_pow]
      push_cast
      ring
    have h1 : 2 * Real.log (qq / δ) ≤ 2 * Real.log (1 / δ) + (d : ℝ) * ℓ1 := by
      rw [hlog]; linarith [hlogdet t ht]
    have h2 : (R : ℝ) * Real.sqrt (2 * Real.log (qq / δ)) ≤
        (R : ℝ) * Real.sqrt (2 * Real.log (1 / δ) + (d : ℝ) * ℓ1) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) hR0
    linarith
  have hr : ∀ t, sSup ((fun x => x ⬝ᵥ θstar) '' D (t + 1) ω) - X (t + 1) ω ⬝ᵥ θstar ≤
      2 * ImprovedLinBandits.OFUL.confidenceRadius d R S lam δ X t ω * Real.sqrt (a t) := by
    intro t
    obtain ⟨hXD, hθt, hopt⟩ := hrun ω t
    have hθs := hgood t
    have hsup : sSup ((fun x => x ⬝ᵥ θstar) '' D (t + 1) ω) ≤
        X (t + 1) ω ⬝ᵥ θtilde (t + 1) ω := by
      apply csSup_le ((hD t ω).image _)
      rintro _ ⟨x, hx, rfl⟩
      exact hopt x hx θstar hθs
    simp only [ImprovedLinBandits.OFUL.confidenceSet, Set.mem_ofPred_eq] at hθt hθs
    set θh := BanditAlgorithm.regularizedLeastSquares d lam X Y t ω with hθh
    set β := ImprovedLinBandits.OFUL.confidenceRadius d R S lam δ X t ω with hβdef
    set V := BanditAlgorithm.regularizedDesignMatrix d lam X t ω with hV
    have hsa : 0 ≤ Real.sqrt (a t) := Real.sqrt_nonneg _
    have h1 : X (t + 1) ω ⬝ᵥ (θtilde (t + 1) ω - θh) ≤ Real.sqrt (a t) * β := by
      calc _ ≤ Real.sqrt (a t) * Real.sqrt ((θtilde (t + 1) ω - θh) ⬝ᵥ V *ᵥ
            (θtilde (t + 1) ω - θh)) := e5_cs (hVpd t) _ _
        _ = Real.sqrt (a t) * Real.sqrt ((θh - θtilde (t + 1) ω) ⬝ᵥ V *ᵥ
            (θh - θtilde (t + 1) ω)) := by
            rw [← neg_sub θh, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
        _ ≤ Real.sqrt (a t) * β := mul_le_mul_of_nonneg_left hθt hsa
    have h2 : X (t + 1) ω ⬝ᵥ (θh - θstar) ≤ Real.sqrt (a t) * β := by
      calc _ ≤ Real.sqrt (a t) * Real.sqrt ((θh - θstar) ⬝ᵥ V *ᵥ (θh - θstar)) :=
            e5_cs (hVpd t) _ _
        _ ≤ Real.sqrt (a t) * β := mul_le_mul_of_nonneg_left hθs hsa
    have h3 : X (t + 1) ω ⬝ᵥ θtilde (t + 1) ω - X (t + 1) ω ⬝ᵥ θstar =
        X (t + 1) ω ⬝ᵥ (θtilde (t + 1) ω - θh) + X (t + 1) ω ⬝ᵥ (θh - θstar) := by
      rw [dotProduct_sub, dotProduct_sub]; ring
    linarith
  -- elliptical potential
  have hsum_a : ∑ t ∈ Finset.range n, a t ≤ 2 * d * ℓ1 := by
    have hlog1 : ∀ t, a t ≤ 2 * Real.log (1 + a t) := by
      intro t
      have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + a t by linarith [ha0 t])
      have h' : 1 - (1 + a t)⁻¹ = a t / (1 + a t) := by
        have : (1 + a t) ≠ 0 := by linarith [ha0 t]
        field_simp
        ring
      have h'' : a t / 2 ≤ a t / (1 + a t) :=
        div_le_div_of_nonneg_left (ha0 t) (by linarith [ha0 t]) (by linarith [ha1 t])
      linarith
    have hprod : ∏ t ∈ Finset.range n, (1 + a t) =
        (BanditAlgorithm.regularizedDesignMatrix d lam X n ω).det / lam ^ d := by
      rw [e5_V_det d hlam X n ω, eq_div_iff (pow_pos hlam d).ne']
      ring
    calc ∑ t ∈ Finset.range n, a t ≤ ∑ t ∈ Finset.range n, 2 * Real.log (1 + a t) :=
          Finset.sum_le_sum fun t _ => hlog1 t
      _ = 2 * Real.log (∏ t ∈ Finset.range n, (1 + a t)) := by
          rw [← Finset.mul_sum, Real.log_prod]
          intro t _
          linarith [ha0 t]
      _ ≤ 2 * (d * ℓ1) := by
          rw [hprod]
          linarith [hlogdet n le_rfl]
      _ = 2 * d * ℓ1 := by ring
  have hsqrt : ∑ t ∈ Finset.range n, Real.sqrt (a t) ≤
      2 * Real.sqrt ((n : ℝ) * d * ℓ2) := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range n) (fun _ => (1 : ℝ))
      (fun t => Real.sqrt (a t))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      at hcs
    have hsa : ∑ t ∈ Finset.range n, Real.sqrt (a t) ^ 2 = ∑ t ∈ Finset.range n, a t :=
      Finset.sum_congr rfl fun t _ => Real.sq_sqrt (ha0 t)
    rw [hsa, ← Real.sqrt_mul (Nat.cast_nonneg n)] at hcs
    have h4 : Real.sqrt (4 * ((n : ℝ) * d * ℓ2)) = 2 * Real.sqrt ((n : ℝ) * d * ℓ2) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [← h4]
    refine hcs.trans (Real.sqrt_le_sqrt ?_)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : (n : ℝ) * (2 * d * ℓ1) ≤ (n : ℝ) * (4 * d * ℓ2) := by
      apply mul_le_mul_of_nonneg_left _ hn0
      nlinarith
    calc (n : ℝ) * ∑ t ∈ Finset.range n, a t ≤ (n : ℝ) * (2 * d * ℓ1) :=
          mul_le_mul_of_nonneg_left hsum_a hn0
      _ ≤ (n : ℝ) * (4 * d * ℓ2) := this
      _ = 4 * ((n : ℝ) * d * ℓ2) := by ring
  -- assemble
  unfold ImprovedLinBandits.OFUL.pseudoRegret
  calc ∑ t ∈ Finset.range n, (sSup ((fun x => x ⬝ᵥ θstar) '' D (t + 1) ω) -
        X (t + 1) ω ⬝ᵥ θstar)
      ≤ ∑ t ∈ Finset.range n, 2 * B * Real.sqrt (a t) := by
        refine Finset.sum_le_sum fun t ht => (hr t).trans ?_
        have := hβ t (Finset.mem_range.mp ht).le
        have hsa : 0 ≤ Real.sqrt (a t) := Real.sqrt_nonneg _
        nlinarith
    _ = 2 * B * ∑ t ∈ Finset.range n, Real.sqrt (a t) := by rw [Finset.mul_sum]
    _ ≤ 2 * B * (2 * Real.sqrt ((n : ℝ) * d * ℓ2)) := by gcongr
    _ = 4 * Real.sqrt ((n : ℝ) * d * ℓ2) * B := by ring

open MeasureTheory ProbabilityTheory Matrix NNReal ImprovedLinBandits.OFUL in
theorem solution
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (D : ℕ → Ω → Set (Fin d → ℝ))
    (X : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (θtilde : ℕ → Ω → Fin d → ℝ) (θstar : Fin d → ℝ)
    (R : ℝ≥0) {S lam L δ : ℝ}
    (hd : 0 < d)
    (hX : ∀ t : ℕ, Measurable[ℱ t] (X (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) (R ^ 2) P)
    (hY : ∀ (t : ℕ) (ω : Ω), Y (t + 1) ω = X (t + 1) ω ⬝ᵥ θstar + η (t + 1) ω)
    (hS : Real.sqrt (θstar ⬝ᵥ θstar) ≤ S)
    (hL : ∀ (t : ℕ) (ω : Ω), Real.sqrt (X (t + 1) ω ⬝ᵥ X (t + 1) ω) ≤ L)
    (hlam_one : 1 ≤ lam) (hlam_L : L ^ 2 ≤ lam)
    (hD : ∀ (t : ℕ) (ω : Ω), (D (t + 1) ω).Nonempty)
    (hrew : ∀ (t : ℕ) (ω : Ω), ∀ x ∈ D (t + 1) ω, x ⬝ᵥ θstar ∈ Set.Icc (-1 : ℝ) 1)
    (hrun : IsOFULRun d R S lam δ D X Y θtilde)
    (hδ : 0 < δ) :
    P {ω | ∃ n : ℕ,
        4 * Real.sqrt ((n : ℝ) * d * Real.log (lam + (n : ℝ) * L ^ 2 / d)) *
            (Real.sqrt lam * S + (R : ℝ) * Real.sqrt (2 * Real.log (1 / δ)
              + (d : ℝ) * Real.log (1 + (n : ℝ) * L ^ 2 / (lam * d))))
          < pseudoRegret d D X θstar n ω}
      ≤ ENNReal.ofReal δ := by
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · calc _ ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hδ1
  have hlam0 : 0 < lam := by linarith
  set cm : ℕ → ℝ := fun m => (R : ℝ) ^ 2 + 1 / ((m : ℝ) + 1) with hcm
  have hcm_pos : ∀ m, 0 < cm m := fun m => by simp only [hcm]; positivity
  set Z : ℕ → ℕ → Ω → ℝ := fun m t ω =>
    Real.exp ((BanditAlgorithm.selfNormalizedSum d η X t ω ⬝ᵥ
        (BanditAlgorithm.regularizedDesignMatrix d lam X t ω)⁻¹ *ᵥ
          BanditAlgorithm.selfNormalizedSum d η X t ω) / (2 * cm m)) /
      (Real.sqrt (BanditAlgorithm.regularizedDesignMatrix d lam X t ω).det *
        (Real.sqrt (lam • (1 : Matrix (Fin d) (Fin d) ℝ)).det)⁻¹) with hZ
  have hdl0 : 0 < (lam • (1 : Matrix (Fin d) (Fin d) ℝ)).det := by simp; positivity
  have hsq0 : 0 < Real.sqrt (lam • (1 : Matrix (Fin d) (Fin d) ℝ)).det := Real.sqrt_pos.mpr hdl0
  -- measurability of the ingredients w.r.t. `ℱ t`
  have hXm : ∀ t s, s < t → Measurable[ℱ t] (X (s + 1)) := fun t s hs =>
    (hX s).mono (ℱ.mono (by omega)) le_rfl
  have hXm' : ∀ t s, s < t + 1 → Measurable[ℱ t] (X (s + 1)) := fun t s hs =>
    (hX s).mono (ℱ.mono (by omega)) le_rfl
  have hηm : ∀ t s, s < t → Measurable[ℱ t] (η (s + 1)) := fun t s hs =>
    (hη s).mono (ℱ.mono (by omega)) le_rfl
  have hVm : ∀ t i j, Measurable[ℱ t]
      (fun ω => BanditAlgorithm.regularizedDesignMatrix d lam X t ω i j) := fun t i j =>
    @e5_meas_V Ω (ℱ t) d lam X t (hXm t) i j
  have hVim : ∀ t i j, Measurable[ℱ t]
      (fun ω => (BanditAlgorithm.regularizedDesignMatrix d lam X t ω)⁻¹ i j) := fun t i j =>
    @e5_meas_inv Ω (ℱ t) (Fin d) _ _ _ (hVm t) i j
  have hSm : ∀ t, Measurable[ℱ t] (fun ω => BanditAlgorithm.selfNormalizedSum d η X t ω) :=
    fun t => @e5_meas_S Ω (ℱ t) d η X t (hXm t) (hηm t)
  have hZm : ∀ m t, Measurable[ℱ t] (Z m t) := by
    intro m t
    have hQ := @e5_meas_quad Ω (ℱ t) d _ (hVim t) _ _ (hSm t) (hSm t)
    have hD' := @e5_meas_det Ω (ℱ t) (Fin d) _ _ _ (hVm t)
    exact (Real.measurable_exp.comp (hQ.div_const _)).div
      ((Real.continuous_sqrt.measurable.comp hD').mul_const _)
  have hZnn : ∀ m t ω, 0 ≤ Z m t ω := fun m t ω => by
    simp only [hZ]; positivity
  have hZ0 : ∀ m ω, Z m 0 ω = 1 := by
    intro m ω
    simp only [hZ]
    rw [e5_S_zero, e5_V_zero]
    simp only [zero_dotProduct, zero_div, Real.exp_zero]
    rw [mul_inv_cancel₀ hsq0.ne', div_one]
  have hstep : ∀ m t (A : Set Ω), MeasurableSet[ℱ t] A →
      ∫⁻ ω in A, ENNReal.ofReal (Z m (t + 1) ω) ∂P ≤
        ∫⁻ ω in A, ENNReal.ofReal (Z m t ω) ∂P := by
    intro m t A hA
    have hA' : MeasurableSet A := ℱ.le t _ hA
    have hrec : ∀ ω, Z m (t + 1) ω = Z m t ω *
        (Real.exp ((2 * η (t + 1) ω * (X (t + 1) ω ⬝ᵥ
            (BanditAlgorithm.regularizedDesignMatrix d lam X t ω)⁻¹ *ᵥ
              BanditAlgorithm.selfNormalizedSum d η X t ω) +
          η (t + 1) ω ^ 2 * (X (t + 1) ω ⬝ᵥ
            (BanditAlgorithm.regularizedDesignMatrix d lam X t ω)⁻¹ *ᵥ X (t + 1) ω) -
          (X (t + 1) ω ⬝ᵥ (BanditAlgorithm.regularizedDesignMatrix d lam X t ω)⁻¹ *ᵥ
              BanditAlgorithm.selfNormalizedSum d η X t ω) ^ 2) /
          (2 * cm m * (1 + X (t + 1) ω ⬝ᵥ
            (BanditAlgorithm.regularizedDesignMatrix d lam X t ω)⁻¹ *ᵥ X (t + 1) ω))) /
        Real.sqrt (1 + X (t + 1) ω ⬝ᵥ
            (BanditAlgorithm.regularizedDesignMatrix d lam X t ω)⁻¹ *ᵥ X (t + 1) ω)) := by
      intro ω
      simp only [hZ]
      rw [e5_V_succ, e5_S_succ]
      exact e5_Z_succ (e5_V_posdef d hlam0 X t ω) _ _ _ _ _ (hcm_pos m)
    have hg : Measurable[ℱ t] (A.indicator fun ω => ENNReal.ofReal (Z m t ω)) :=
      (ENNReal.measurable_ofReal.comp (hZm m t)).indicator hA
    have ha : Measurable[ℱ t] (fun ω => X (t + 1) ω ⬝ᵥ
        (BanditAlgorithm.regularizedDesignMatrix d lam X t ω)⁻¹ *ᵥ X (t + 1) ω) :=
      @e5_meas_quad Ω (ℱ t) d _ (hVim t) _ _ (hX t) (hX t)
    have hb : Measurable[ℱ t] (fun ω => X (t + 1) ω ⬝ᵥ
        (BanditAlgorithm.regularizedDesignMatrix d lam X t ω)⁻¹ *ᵥ
          BanditAlgorithm.selfNormalizedSum d η X t ω) :=
      @e5_meas_quad Ω (ℱ t) d _ (hVim t) _ _ (hX t) (hSm t)
    have hηt : Measurable (η (t + 1)) := (hη t).mono (ℱ.le (t + 1)) le_rfl
    have hRc : ((R ^ 2 : ℝ≥0) : ℝ) ≤ cm m := by
      simp only [hcm]; push_cast
      have : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
      linarith
    have hk := e5_kcl (ℱ.le t) hηt (hcm_pos m) hRc (hsg t) hg ha hb
      (fun ω => e5_a_nonneg (e5_V_posdef d hlam0 X t ω) _)
    calc ∫⁻ ω in A, ENNReal.ofReal (Z m (t + 1) ω) ∂P
        = ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Z m (t + 1) ω)) ω ∂P :=
          (lintegral_indicator hA' _).symm
      _ = _ := by
          refine lintegral_congr fun ω => ?_
          by_cases h : ω ∈ A
          · simp only [Set.indicator_of_mem h]
            rw [hrec ω, ENNReal.ofReal_mul (hZnn m t ω)]
          · simp only [Set.indicator_of_notMem h, zero_mul]
      _ ≤ ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Z m t ω)) ω ∂P := hk
      _ = ∫⁻ ω in A, ENNReal.ofReal (Z m t ω) ∂P := lintegral_indicator hA' _
  -- the bad events
  set B : ℕ → Set Ω := fun m => {ω | ∃ t, 1 / δ < Z m t ω} with hB
  have hPB : ∀ m, P (B m) ≤ ENNReal.ofReal δ := fun m =>
    e5_ville ℱ (Z m) (hZm m) (hZ0 m) (hstep m) hδ
  have hmono : Monotone B := by
    refine monotone_nat_of_le_succ fun m => ?_
    rintro ω ⟨t, ht⟩
    refine ⟨t, lt_of_lt_of_le ht ?_⟩
    simp only [hZ]
    have hQ0 := e5_a_nonneg (e5_V_posdef d hlam0 X t ω)
      (BanditAlgorithm.selfNormalizedSum d η X t ω)
    have hc : cm (m + 1) ≤ cm m := by
      simp only [hcm]; push_cast
      have : 1 / ((m : ℝ) + 1 + 1) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_left hQ0 (by linarith [hcm_pos (m + 1)])
    linarith
  have hsub : {ω | ∃ n : ℕ,
        4 * Real.sqrt ((n : ℝ) * d * Real.log (lam + (n : ℝ) * L ^ 2 / d)) *
            (Real.sqrt lam * S + (R : ℝ) * Real.sqrt (2 * Real.log (1 / δ)
              + (d : ℝ) * Real.log (1 + (n : ℝ) * L ^ 2 / (lam * d))))
          < pseudoRegret d D X θstar n ω} ⊆ ⋃ m, B m := by
    intro ω hω
    by_contra hnot
    have hnot' : ∀ m t, Z m t ω ≤ 1 / δ := by
      intro m t
      by_contra hlt
      exact hnot (Set.mem_iUnion.mpr ⟨m, t, lt_of_not_ge hlt⟩)
    have hgood : ∀ t, θstar ∈ confidenceSet d R S lam δ X Y t ω := by
      intro t
      by_contra hbad
      obtain ⟨m, hm⟩ := e5_link X η Y θstar R hlam_one hS hY hδ hδ1 t ω hbad
      exact absurd (hnot' m t) (not_le.mpr hm)
    obtain ⟨n, hn⟩ := hω
    exact absurd (e5_regret D X Y θtilde θstar R hd hS hL hlam_one hlam_L hD hrun hδ ω hgood n)
      (not_le.mpr hn)
  calc _ ≤ P (⋃ m, B m) := measure_mono hsub
    _ = ⨆ m, P (B m) := hmono.measure_iUnion
    _ ≤ ENNReal.ofReal δ := iSup_le hPB
