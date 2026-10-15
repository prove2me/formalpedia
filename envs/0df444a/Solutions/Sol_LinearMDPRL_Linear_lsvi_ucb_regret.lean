-- Prove2me | solution 1 for LinearMDPRL.Linear.lsvi_ucb_regret
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T03:26:03.410977+00:00
-- url     : https://prove2.me/submissions/7baeb05c-82a8-465d-bfb8-60adc48aeeac

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB
import Definitions.Def_LinearMDPRL_Linear_LinearMDP

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


open MeasureTheory ProbabilityTheory in
lemma kcl_rect {Ω T S : Type*} {G : MeasurableSpace Ω} {m : MeasurableSpace Ω} [MeasurableSpace T]
    [MeasurableSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hG : G ≤ m)
    (κ : Kernel T S) [IsMarkovKernel κ] (Y : Ω → T) (X : Ω → S)
    (hY : Measurable[G] Y) (hX : Measurable[m] X)
    (htrans : ∀ B : Set S, MeasurableSet B →
      μ[(X ⁻¹' B).indicator (fun _ => (1 : ℝ)) | G] =ᵐ[μ] fun ω => (κ (Y ω) B).toReal)
    {A : Set Ω} (hA : MeasurableSet[G] A) {B : Set S} (hB : MeasurableSet B) :
    μ (A ∩ X ⁻¹' B) = ∫⁻ ω in A, κ (Y ω) B ∂μ := by
  have hAm : MeasurableSet[m] A := hG _ hA
  have hXB : MeasurableSet (X ⁻¹' B) := hX hB
  have hind : Integrable ((X ⁻¹' B).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hXB
  have h1 := setIntegral_condExp hG hind hA
  have h2 : ∫ ω in A, μ[(X ⁻¹' B).indicator (fun _ => (1 : ℝ)) | G] ω ∂μ =
      ∫ ω in A, (κ (Y ω) B).toReal ∂μ :=
    integral_congr_ae (ae_restrict_of_ae (htrans B hB))
  have h3 : ∫ ω in A, (X ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω ∂μ = (μ (A ∩ X ⁻¹' B)).toReal := by
    rw [setIntegral_indicator hXB, setIntegral_const]
    simp [Measure.real, Set.inter_comm]
  have hmeasκ : Measurable fun ω => κ (Y ω) B :=
    (Kernel.measurable_coe κ hB).comp (hY.mono hG le_rfl)
  have h4 : ∫ ω in A, (κ (Y ω) B).toReal ∂μ = (∫⁻ ω in A, κ (Y ω) B ∂μ).toReal := by
    rw [integral_toReal hmeasκ.aemeasurable (ae_of_all _ fun ω => measure_lt_top _ _)]
  have hfin1 : μ (A ∩ X ⁻¹' B) ≠ ⊤ := measure_ne_top _ _
  have hfin2 : ∫⁻ ω in A, κ (Y ω) B ∂μ ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun _ => 1) fun ω => prob_le_one) ?_)
    simp
  rw [← ENNReal.toReal_eq_toReal_iff' hfin1 hfin2, ← h3, ← h4, ← h2, h1]


open MeasureTheory ProbabilityTheory in
lemma kcl {Ω T S : Type*} {G : MeasurableSpace Ω} {m : MeasurableSpace Ω} [mS : MeasurableSpace S]
    [MeasurableSpace T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hG : G ≤ m)
    (κ : Kernel T S) [IsMarkovKernel κ] (Y : Ω → T) (X : Ω → S)
    (hY : Measurable[G] Y) (hX : Measurable[m] X)
    (htrans : ∀ B : Set S, MeasurableSet B →
      μ[(X ⁻¹' B).indicator (fun _ => (1 : ℝ)) | G] =ᵐ[μ] fun ω => (κ (Y ω) B).toReal)
    (F : Ω → S → ENNReal) (hF : Measurable[G.prod mS] (fun p : Ω × S => F p.1 p.2)) :
    ∫⁻ ω, F ω (X ω) ∂μ = ∫⁻ ω, ∫⁻ y, F ω y ∂(κ (Y ω)) ∂μ := by
  have hle : G.prod mS ≤ m.prod mS := by
    unfold MeasurableSpace.prod
    exact sup_le_sup (MeasurableSpace.comap_mono hG) le_rfl
  have hYm : Measurable[m] Y := hY.mono hG le_rfl
  set κ' : Kernel Ω S := κ.comap Y hYm with hκ'
  set Φ : Measure (Ω × S) := μ.map (fun ω => (ω, X ω)) with hΦ
  set Ψ : Measure (Ω × S) := μ ⊗ₘ κ' with hΨ
  have hmap : Measurable[m, m.prod mS] (fun ω => (ω, X ω)) := measurable_id.prodMk hX
  haveI : IsProbabilityMeasure Φ := Measure.isProbabilityMeasure_map hmap.aemeasurable
  haveI : IsProbabilityMeasure Ψ := inferInstance
  have hAB : ∀ {A : Set Ω} (hA : MeasurableSet[G] A) {B : Set S} (hB : MeasurableSet B),
      Φ (A ×ˢ B) = Ψ (A ×ˢ B) := by
    intro A hA B hB
    have hAm : MeasurableSet[m] A := hG _ hA
    have hAB' : MeasurableSet[m.prod mS] (A ×ˢ B) := hAm.prod hB
    rw [hΦ, Measure.map_apply hmap hAB', hΨ, Measure.compProd_apply_prod hAm hB]
    have : (fun ω => (ω, X ω)) ⁻¹' (A ×ˢ B) = A ∩ X ⁻¹' B := by
      ext ω; simp
    rw [this, kcl_rect μ hG κ Y X hY hX htrans hA hB]
    simp [hκ', Kernel.comap_apply]
  have hgen : G.prod mS = MeasurableSpace.generateFrom
      (Set.image2 (· ×ˢ ·) {A : Set Ω | MeasurableSet[G] A} {B : Set S | MeasurableSet B}) := by
    have hC : IsCountablySpanning {A : Set Ω | MeasurableSet[G] A} :=
      ⟨fun _ => Set.univ, fun _ => @MeasurableSet.univ _ G, Set.iUnion_const _⟩
    have hD : IsCountablySpanning {B : Set S | MeasurableSet B} :=
      ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ, Set.iUnion_const _⟩
    have := generateFrom_prod_eq hC hD
    rw [@MeasurableSpace.generateFrom_measurableSet _ G, MeasurableSpace.generateFrom_measurableSet] at this
    exact this
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·) {A : Set Ω | MeasurableSet[G] A}
      {B : Set S | MeasurableSet B}) :=
    IsPiSystem.prod (@MeasurableSpace.isPiSystem_measurableSet _ G) MeasurableSpace.isPiSystem_measurableSet
  have hset : ∀ E : Set (Ω × S), MeasurableSet[G.prod mS] E → Φ E = Ψ E := by
    intro E hE
    refine @MeasurableSpace.induction_on_inter _ (G.prod mS) (fun E _ => Φ E = Ψ E) _ hgen hpi
      ?_ ?_ ?_ ?_ E hE
    · simp
    · rintro t ⟨A, hA, B, hB, rfl⟩
      exact hAB hA hB
    · intro t htm ih
      have htm' : MeasurableSet[m.prod mS] t := hle _ htm
      rw [prob_compl_eq_one_sub htm', prob_compl_eq_one_sub htm', ih]
    · intro f hdisj hfm ih
      have hfm' : ∀ i, MeasurableSet[m.prod mS] (f i) := fun i => hle _ (hfm i)
      rw [measure_iUnion hdisj hfm', measure_iUnion hdisj hfm']
      exact tsum_congr ih
  have htrim : Φ.trim hle = Ψ.trim hle :=
    @Measure.ext _ (G.prod mS) _ _ fun E hE => by
      rw [trim_measurableSet_eq hle hE, trim_measurableSet_eq hle hE]
      exact hset E hE
  have hF' : Measurable[m.prod mS] (fun p : Ω × S => F p.1 p.2) := hF.mono hle le_rfl
  calc ∫⁻ ω, F ω (X ω) ∂μ = ∫⁻ p, F p.1 p.2 ∂Φ := by rw [hΦ, lintegral_map hF' hmap]
    _ = ∫⁻ p, F p.1 p.2 ∂(Φ.trim hle) := (lintegral_trim hle hF).symm
    _ = ∫⁻ p, F p.1 p.2 ∂(Ψ.trim hle) := by rw [htrim]
    _ = ∫⁻ p, F p.1 p.2 ∂Ψ := lintegral_trim hle hF
    _ = ∫⁻ ω, ∫⁻ y, F ω y ∂κ (Y ω) ∂μ := by
        rw [hΨ, Measure.lintegral_compProd hF']
        simp [hκ', Kernel.comap_apply]


open MeasureTheory ProbabilityTheory Matrix in
lemma c2_posdef {d : ℕ} (u : ℕ → Fin d → ℝ) (n : ℕ) :
    (1 + ∑ t ∈ Finset.range n, vecMulVec (u t) (u t)).PosDef := by
  induction n with
  | zero => simpa using (PosDef.one : (1 : Matrix (Fin d) (Fin d) ℝ).PosDef)
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc]
    have h := posSemidef_vecMulVec_self_star (u n)
    rw [star_trivial] at h
    exact ih.add_posSemidef h


open MeasureTheory ProbabilityTheory in
lemma c2_hoeffding {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    {f : S → ℝ} (hf : Measurable f) {H : ℝ} (hH : 0 < H) (hf0 : ∀ y, f y ∈ Set.Icc 0 H)
    (t : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (t * (f y - ∫ z, f z ∂ν))) ∂ν ≤
      ENNReal.ofReal (Real.exp (H ^ 2 / 4 * t ^ 2 / 2)) := by
  have hs := hasSubgaussianMGF_of_mem_Icc (μ := ν) hf.aemeasurable (ae_of_all _ hf0)
  rw [← ofReal_integral_eq_lintegral_ofReal (hs.integrable_exp_mul t)
    (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  apply ENNReal.ofReal_le_ofReal
  have h1 := hs.mgf_le t
  have hc : (((‖H - 0‖₊ / 2) ^ 2 : NNReal) : ℝ) = H ^ 2 / 4 := by
    simp only [sub_zero, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos hH]
    norm_num
    ring
  rw [hc] at h1
  exact h1


open MeasureTheory ProbabilityTheory Matrix in
lemma c2_meas_all {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (u : ℕ → Ω → Fin d → ℝ)
    (η : ℕ → Ω → ℝ) (c : ℝ) (n : ℕ) (hu : ∀ t, t ≤ n → Measurable (u t))
    (hη : ∀ t, t < n → Measurable (η t)) :
    Measurable (fun ω => Real.exp (((∑ t ∈ Finset.range n, η t ω • u t ω) ⬝ᵥ
        (1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω))⁻¹ *ᵥ
          (∑ t ∈ Finset.range n, η t ω • u t ω)) / (2 * c)) /
        (Real.sqrt (1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω)).det * 1)) ∧
    Measurable (fun ω => u n ω ⬝ᵥ
        (1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω))⁻¹ *ᵥ u n ω) ∧
    Measurable (fun ω => u n ω ⬝ᵥ
        (1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω))⁻¹ *ᵥ
          (∑ t ∈ Finset.range n, η t ω • u t ω)) := by
  have hV : ∀ i j, Measurable fun ω =>
      (1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω)) i j := by
    intro i j
    simp only [Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply]
    refine measurable_const.add (Finset.measurable_sum _ fun t ht => ?_)
    have ht' : t ≤ n := (Finset.mem_range.mp ht).le
    exact ((measurable_pi_apply i).comp (hu t ht')).mul ((measurable_pi_apply j).comp (hu t ht'))
  have hS : Measurable fun ω => ∑ t ∈ Finset.range n, η t ω • u t ω := by
    refine measurable_pi_iff.mpr fun i => ?_
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.measurable_sum _ fun t ht => ?_
    have ht' : t < n := Finset.mem_range.mp ht
    exact (hη t ht').mul ((measurable_pi_apply i).comp (hu t ht'.le))
  have hinv := e5_meas_inv
    (M := fun ω => 1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω)) hV
  refine ⟨?_, e5_meas_quad hinv (hu n le_rfl) (hu n le_rfl), e5_meas_quad hinv (hu n le_rfl) hS⟩
  refine (Real.measurable_exp.comp ((e5_meas_quad hinv hS hS).div_const _)).div ?_
  exact (Real.continuous_sqrt.measurable.comp
    (e5_meas_det (M := fun ω => 1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω)) hV)).mul
    measurable_const


open MeasureTheory ProbabilityTheory Matrix in
lemma c2_meas_Z {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (u : ℕ → Ω → Fin d → ℝ)
    (η : ℕ → Ω → ℝ) (c : ℝ) (n : ℕ) (hu : ∀ t, t < n → Measurable (u t))
    (hη : ∀ t, t < n → Measurable (η t)) :
    Measurable (fun ω => Real.exp (((∑ t ∈ Finset.range n, η t ω • u t ω) ⬝ᵥ
        (1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω))⁻¹ *ᵥ
          (∑ t ∈ Finset.range n, η t ω • u t ω)) / (2 * c)) /
        (Real.sqrt (1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω)).det * 1)) := by
  have hV : ∀ i j, Measurable fun ω =>
      (1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω)) i j := by
    intro i j
    simp only [Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply]
    refine measurable_const.add (Finset.measurable_sum _ fun t ht => ?_)
    have ht' : t < n := Finset.mem_range.mp ht
    exact ((measurable_pi_apply i).comp (hu t ht')).mul ((measurable_pi_apply j).comp (hu t ht'))
  have hS : Measurable fun ω => ∑ t ∈ Finset.range n, η t ω • u t ω := by
    refine measurable_pi_iff.mpr fun i => ?_
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.measurable_sum _ fun t ht => ?_
    have ht' : t < n := Finset.mem_range.mp ht
    exact (hη t ht').mul ((measurable_pi_apply i).comp (hu t ht'))
  have hinv := e5_meas_inv
    (M := fun ω => 1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω)) hV
  refine (Real.measurable_exp.comp ((e5_meas_quad hinv hS hS).div_const _)).div ?_
  exact (Real.continuous_sqrt.measurable.comp
    (e5_meas_det (M := fun ω => 1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω)) hV)).mul
    measurable_const


open MeasureTheory ProbabilityTheory in
lemma c2_meas_F {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] {Z a b M : Ω → ℝ}
    {f : S → ℝ} (hZ : Measurable Z) (ha : Measurable a) (hb : Measurable b) (hM : Measurable M)
    (hf : Measurable f) (c : ℝ) :
    Measurable (fun p : Ω × S => ENNReal.ofReal (Z p.1) *
      ENNReal.ofReal (Real.exp ((2 * (f p.2 - M p.1) * b p.1 + (f p.2 - M p.1) ^ 2 * a p.1
        - b p.1 ^ 2) / (2 * c * (1 + a p.1))) / Real.sqrt (1 + a p.1))) := by
  have h1 : Measurable fun p : Ω × S => Z p.1 := hZ.comp measurable_fst
  have h2 : Measurable fun p : Ω × S => a p.1 := ha.comp measurable_fst
  have h3 : Measurable fun p : Ω × S => b p.1 := hb.comp measurable_fst
  have h4 : Measurable fun p : Ω × S => M p.1 := hM.comp measurable_fst
  have h5 : Measurable fun p : Ω × S => f p.2 := hf.comp measurable_snd
  refine (ENNReal.measurable_ofReal.comp h1).mul (ENNReal.measurable_ofReal.comp ?_)
  refine (Real.measurable_exp.comp ?_).div (Real.continuous_sqrt.measurable.comp ?_)
  · exact ((((measurable_const.mul (h5.sub h4)).mul h3).add (((h5.sub h4).pow_const 2).mul h2)).sub
      (h3.pow_const 2)).div (measurable_const.mul (measurable_const.add h2))
  · exact measurable_const.add h2


lemma c2_real (H D δ Q : ℝ) (hH : 0 < H) (hD : 0 < D) (hδ : 0 < δ)
    (h : H ^ 2 / 2 * Real.log (D / δ) < Q) :
    1 / δ < Real.exp (Q / (2 * (H ^ 2 / 4))) / (D * 1) := by
  have hH2 : 0 < H ^ 2 / 2 := by positivity
  have h1 : Real.log (D / δ) < Q / (2 * (H ^ 2 / 4)) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have h2 : D / δ < Real.exp (Q / (2 * (H ^ 2 / 4))) :=
    (Real.log_lt_iff_lt_exp (by positivity)).mp h1
  rw [mul_one, lt_div_iff₀ hD]
  calc 1 / δ * D = D / δ := by ring
    _ < _ := h2


open MeasureTheory ProbabilityTheory Matrix in
/-- C2: self-normalized concentration for bounded transitions (Markov-kernel form; fixed time) -/
theorem c2_selfnorm_markov {Ω T S : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    [MeasurableSpace S] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Filtration ℕ ‹MeasurableSpace Ω›) (κ : Kernel T S) [IsMarkovKernel κ]
    {d : ℕ} (u : ℕ → Ω → Fin d → ℝ) (Y : ℕ → Ω → T) (X : ℕ → Ω → S) (n : ℕ)
    (hu : ∀ t, t < n → Measurable[G t] (u t)) (hY : ∀ t, t < n → Measurable[G t] (Y t))
    (hX : ∀ t, t < n → Measurable[G (t + 1)] (X t))
    (htrans : ∀ t, t < n → ∀ (B : Set S), MeasurableSet B →
      μ[(X t ⁻¹' B).indicator (fun _ => (1 : ℝ)) | G t] =ᵐ[μ] fun ω => (κ (Y t ω) B).toReal)
    (f : S → ℝ) (hf : Measurable f) (H : ℝ) (hH : 0 < H) (hf0 : ∀ y, f y ∈ Set.Icc 0 H)
    (δ : ℝ) (hδ : 0 < δ) :
    μ {ω | H ^ 2 / 2 * Real.log (Real.sqrt
          (1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω)).det / δ) <
        (∑ t ∈ Finset.range n, (f (X t ω) - ∫ y, f y ∂(κ (Y t ω))) • u t ω) ⬝ᵥ
          ((1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω))⁻¹ *ᵥ
            (∑ t ∈ Finset.range n, (f (X t ω) - ∫ y, f y ∂(κ (Y t ω))) • u t ω))}
      ≤ ENNReal.ofReal δ := by
  classical
  have hc : (0 : ℝ) < H ^ 2 / 4 := by positivity
  obtain ⟨m, hm⟩ : ∃ m : ℕ → Ω → ℝ, m = fun t ω => ∫ y, f y ∂(κ (Y t ω)) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℕ → Ω → ℝ, η = fun t ω => f (X t ω) - m t ω := ⟨_, rfl⟩
  obtain ⟨Vm, hVm⟩ : ∃ Vm : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ,
      Vm = fun n ω => 1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω) := ⟨_, rfl⟩
  obtain ⟨Sm, hSm⟩ : ∃ Sm : ℕ → Ω → Fin d → ℝ,
      Sm = fun n ω => ∑ t ∈ Finset.range n, η t ω • u t ω := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ → Ω → ℝ, Z = fun n ω =>
      Real.exp ((Sm n ω ⬝ᵥ (Vm n ω)⁻¹ *ᵥ Sm n ω) / (2 * (H ^ 2 / 4))) /
        (Real.sqrt (Vm n ω).det * 1) := ⟨_, rfl⟩
  have hpd : ∀ n ω, (Vm n ω).PosDef := fun n ω => by
    rw [hVm]; exact c2_posdef (fun t => u t ω) n
  have hZnn : ∀ n ω, 0 ≤ Z n ω := fun n ω => by rw [hZ]; positivity
  have hK : Measurable fun y : T => ∫ z, f z ∂(κ y) :=
    (hf.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  have hmG : ∀ t, t < n → Measurable[G t] (m t) := fun t htn => by
    rw [hm]; exact hK.comp (hY t htn)
  have hηG : ∀ t j, t < j → j ≤ n → Measurable[G j] (η t) := fun t j htn hjn => by
    rw [hη]
    have h1 : Measurable[G j] (X t) := (hX t (by omega)).mono (G.mono htn) le_rfl
    have h2 : Measurable[G j] (m t) := (hmG t (by omega)).mono (G.mono htn.le) le_rfl
    exact (hf.comp h1).sub h2
  have huG : ∀ t j, t ≤ j → t < n → Measurable[G j] (u t) := fun t j h htn =>
    (hu t htn).mono (G.mono h) le_rfl
  have hmeasn : ∀ j, j < n → Measurable[G j] (Z j) ∧
      Measurable[G j] (fun ω => u j ω ⬝ᵥ (Vm j ω)⁻¹ *ᵥ u j ω) ∧
      Measurable[G j] (fun ω => u j ω ⬝ᵥ (Vm j ω)⁻¹ *ᵥ Sm j ω) := by
    intro j hj
    have h := @c2_meas_all Ω (G j) d u η (H ^ 2 / 4) j (fun t ht => huG t j ht (by omega))
      (fun t ht => hηG t j ht hj.le)
    subst hZ hSm hVm
    exact h
  have hZnm : Measurable[G n] (Z n) := by
    have h := @c2_meas_Z Ω (G n) d u η (H ^ 2 / 4) n (fun t ht => huG t n ht.le ht)
      (fun t ht => hηG t n ht le_rfl)
    subst hZ hSm hVm
    exact h
  have hint : ∀ j, j ≤ n → ∫⁻ ω, ENNReal.ofReal (Z j ω) ∂μ ≤ 1 := by
    intro j
    induction j with
    | zero =>
      intro _
      have h0 : ∀ ω, Z 0 ω = 1 := by
        intro ω; subst hZ hSm hVm; simp
      simp [h0]
    | succ j ih =>
      intro hjn
      have hj : j < n := hjn
      refine le_trans ?_ (ih hj.le)
      obtain ⟨hZn, ha, hb⟩ := hmeasn j hj
      set a : Ω → ℝ := fun ω => u j ω ⬝ᵥ (Vm j ω)⁻¹ *ᵥ u j ω with ha_def
      set b : Ω → ℝ := fun ω => u j ω ⬝ᵥ (Vm j ω)⁻¹ *ᵥ Sm j ω with hb_def
      have ha0 : ∀ ω, 0 ≤ a ω := fun ω => e5_a_nonneg (hpd j ω) (u j ω)
      have hstep : ∀ ω, Z (j + 1) ω = Z j ω *
          (Real.exp ((2 * η j ω * b ω + η j ω ^ 2 * a ω - b ω ^ 2) /
            (2 * (H ^ 2 / 4) * (1 + a ω))) / Real.sqrt (1 + a ω)) := by
        intro ω
        have hV1 : Vm (j + 1) ω = Vm j ω + vecMulVec (u j ω) (u j ω) := by
          rw [hVm]; simp only [Finset.sum_range_succ, add_assoc]
        have hS1 : Sm (j + 1) ω = Sm j ω + η j ω • u j ω := by
          rw [hSm]; simp only [Finset.sum_range_succ]
        have hZ1 : Z (j + 1) ω = Real.exp ((Sm (j + 1) ω ⬝ᵥ (Vm (j + 1) ω)⁻¹ *ᵥ Sm (j + 1) ω) /
            (2 * (H ^ 2 / 4))) / (Real.sqrt (Vm (j + 1) ω).det * 1) := by rw [hZ]
        have hZ0 : Z j ω = Real.exp ((Sm j ω ⬝ᵥ (Vm j ω)⁻¹ *ᵥ Sm j ω) /
            (2 * (H ^ 2 / 4))) / (Real.sqrt (Vm j ω).det * 1) := by rw [hZ]
        rw [hZ1, hZ0, hV1, hS1]
        exact e5_Z_succ (hpd j ω) (u j ω) (Sm j ω) (η j ω) (H ^ 2 / 4) 1 hc
      have hF := @c2_meas_F Ω S (G j) _ (Z j) a b (m j) f hZn ha hb (hmG j hj) hf (H ^ 2 / 4)
      have hk := kcl μ (G.le j) κ (Y j) (X j) (hY j hj) ((hX j hj).mono (G.le (j + 1)) le_rfl)
        (htrans j hj)
        (fun ω y => ENNReal.ofReal (Z j ω) *
          ENNReal.ofReal (Real.exp ((2 * (f y - m j ω) * b ω + (f y - m j ω) ^ 2 * a ω
            - b ω ^ 2) / (2 * (H ^ 2 / 4) * (1 + a ω))) / Real.sqrt (1 + a ω))) hF
      calc ∫⁻ ω, ENNReal.ofReal (Z (j + 1) ω) ∂μ
          = ∫⁻ ω, ENNReal.ofReal (Z j ω) *
              ENNReal.ofReal (Real.exp ((2 * (f (X j ω) - m j ω) * b ω +
                (f (X j ω) - m j ω) ^ 2 * a ω - b ω ^ 2) / (2 * (H ^ 2 / 4) * (1 + a ω))) /
                  Real.sqrt (1 + a ω)) ∂μ := by
            refine lintegral_congr fun ω => ?_
            have hηn : η j ω = f (X j ω) - m j ω := by rw [hη]
            rw [hstep ω, ENNReal.ofReal_mul (hZnn j ω), hηn]
        _ = _ := hk
        _ ≤ ∫⁻ ω, ENNReal.ofReal (Z j ω) ∂μ := by
            refine lintegral_mono fun ω => ?_
            beta_reduce
            rw [lintegral_const_mul _ (by fun_prop)]
            have hmgf : ∀ t : ℝ, ∫⁻ y, ENNReal.ofReal (Real.exp (t * (f y - m j ω)))
                ∂(κ (Y j ω)) ≤ ENNReal.ofReal (Real.exp (H ^ 2 / 4 * t ^ 2 / 2)) := by
              intro t
              have hmn : m j ω = ∫ z, f z ∂(κ (Y j ω)) := by rw [hm]
              rw [hmn]
              exact c2_hoeffding (κ (Y j ω)) hf hH hf0 t
            have hone := e5_oneD (κ (Y j ω)) (η := fun y => f y - m j ω)
              (hf.sub_const (m j ω)) hc hmgf (ha0 ω) (b ω)
            calc ENNReal.ofReal (Z j ω) * _ ≤ ENNReal.ofReal (Z j ω) * 1 := by gcongr
              _ = _ := mul_one _
  have hZm : Measurable (Z n) := hZnm.mono (G.le n) le_rfl
  have hsub : {ω | H ^ 2 / 2 * Real.log (Real.sqrt
          (1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω)).det / δ) <
        (∑ t ∈ Finset.range n, (f (X t ω) - ∫ y, f y ∂(κ (Y t ω))) • u t ω) ⬝ᵥ
          ((1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω))⁻¹ *ᵥ
            (∑ t ∈ Finset.range n, (f (X t ω) - ∫ y, f y ∂(κ (Y t ω))) • u t ω))} ⊆
      {ω | ENNReal.ofReal (1 / δ) ≤ ENNReal.ofReal (Z n ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    apply ENNReal.ofReal_le_ofReal
    have hD : 0 < Real.sqrt (Vm n ω).det := Real.sqrt_pos.mpr (hpd n ω).det_pos
    have hZe : Z n ω = Real.exp ((Sm n ω ⬝ᵥ (Vm n ω)⁻¹ *ᵥ Sm n ω) / (2 * (H ^ 2 / 4))) /
        (Real.sqrt (Vm n ω).det * 1) := by rw [hZ]
    have hVe : Vm n ω = 1 + ∑ t ∈ Finset.range n, vecMulVec (u t ω) (u t ω) := by rw [hVm]
    have hSe : Sm n ω = ∑ t ∈ Finset.range n, (f (X t ω) - ∫ y, f y ∂(κ (Y t ω))) • u t ω := by
      rw [hSm, hη, hm]
    rw [hZe, hVe, hSe]
    rw [hVe] at hD
    exact (c2_real H _ δ _ hH hD hδ hω).le
  have hne : ENNReal.ofReal (1 / δ) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  calc _ ≤ μ {ω | ENNReal.ofReal (1 / δ) ≤ ENNReal.ofReal (Z n ω)} := measure_mono hsub
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Z n ω) ∂μ) / ENNReal.ofReal (1 / δ) :=
        meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp hZm).aemeasurable hne
          ENNReal.ofReal_ne_top
    _ ≤ 1 / ENNReal.ofReal (1 / δ) := ENNReal.div_le_div_right (hint n le_rfl) _
    _ = ENNReal.ofReal δ := by
        rw [ENNReal.div_eq_inv_mul, mul_one, ← ENNReal.ofReal_inv_of_pos (by positivity)]
        congr 1
        field_simp


open MeasureTheory LinearMDPRL.Linear in
lemma c5b_greedy_iff {A : Type*} [Fintype A] [Nonempty A] [LinearOrder A] (q : A → ℝ) (a : A) :
    greedy q = a ↔ (∀ b, q b ≤ q a) ∧ ∀ a', (∀ b, q b ≤ q a') → a ≤ a' := by
  unfold greedy
  constructor
  · intro h
    rw [← h]
    refine ⟨?_, fun a' ha' => ?_⟩
    · have hm := Finset.min'_mem (Finset.univ.filter (fun a => ∀ b, q b ≤ q a)) (by
        obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ q Finset.univ_nonempty
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, fun b => ha b (Finset.mem_univ b)⟩⟩)
      exact (Finset.mem_filter.mp hm).2
    · apply Finset.min'_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha'⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm ?_ ?_
    · apply Finset.min'_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, h1⟩
    · apply Finset.le_min'
      intro a' ha'
      exact h2 a' (Finset.mem_filter.mp ha').2


open MeasureTheory LinearMDPRL.Linear in
lemma c5b_greedy_set {S A : Type*} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
    (Q : S → A → ℝ) (hQ : ∀ a, Measurable fun x => Q x a) (a : A) :
    MeasurableSet {x | greedy (Q x) = a} := by
  classical
  have h : {x | greedy (Q x) = a} =
      (⋂ b, {x | Q x b ≤ Q x a}) ∩
        ⋂ a', ({x | ∀ b, Q x b ≤ Q x a'}ᶜ ∪ {_x | a ≤ a'}) := by
    ext x
    simp only [Set.mem_setOf_eq, c5b_greedy_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_union, Set.mem_compl_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun a' => ?_⟩
      by_cases hc : ∀ b, Q x b ≤ Q x a'
      · exact Or.inr (h2 a' hc)
      · exact Or.inl hc
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun a' ha' => ?_⟩
      rcases h2 a' with h | h
      · exact absurd ha' h
      · exact h
  rw [h]
  have hle : ∀ b c, MeasurableSet {x | Q x b ≤ Q x c} := fun b c =>
    measurableSet_le (hQ b) (hQ c)
  refine (MeasurableSet.iInter fun b => hle b a).inter (MeasurableSet.iInter fun a' => ?_)
  refine (MeasurableSet.compl ?_).union (MeasurableSet.const _)
  have : {x | ∀ b, Q x b ≤ Q x a'} = ⋂ b, {x | Q x b ≤ Q x a'} := by ext x; simp
  rw [this]
  exact MeasurableSet.iInter fun b => hle b a'


open MeasureTheory in
lemma c3a_comp {Ω S A : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (F : S → A → ℝ) (hF : ∀ b, Measurable (fun x => F x b)) {X : Ω → S} (hX : Measurable X)
    {Aa : Ω → A} (hA : Measurable Aa) : Measurable (fun ω => F (X ω) (Aa ω)) := by
  classical
  have h : (fun ω => F (X ω) (Aa ω)) =
      fun ω => ∑ b : A, Set.indicator {ω | Aa ω = b} (fun ω => F (X ω) b) ω := by
    funext ω
    rw [Finset.sum_eq_single (Aa ω)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h]
  exact Finset.measurable_sum _ fun b _ =>
    ((hF b).comp hX).indicator (hA (measurableSet_singleton b))


open MeasureTheory in
lemma c3a_compv {Ω S A : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (hφ : ∀ b, Measurable (fun x => φ x b))
    {X : Ω → S} (hX : Measurable X) {Aa : Ω → A} (hA : Measurable Aa) :
    Measurable (fun ω => WithLp.ofLp (φ (X ω) (Aa ω))) :=
  measurable_pi_iff.mpr fun i => c3a_comp (fun x b => WithLp.ofLp (φ x b) i)
    (fun b => (measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 _).comp (hφ b))) hX hA


open MeasureTheory Matrix LinearMDPRL.Linear in
/-- Measurability of the LSVI-UCB backward pass in the data (generic sample space). -/
lemma c3a_Q_meas {Ω S A : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Fintype A]
    [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (hφ : ∀ b, Measurable (fun x => φ x b))
    (r : ℕ → S → A → ℝ) (hr : ∀ j b, Measurable (fun x => r j x b)) (lam : ℝ) (β : ℕ → ℝ)
    (H : ℕ) (x : ℕ → ℕ → Ω → S) (a : ℕ → ℕ → Ω → A) (k : ℕ)
    (hx : ∀ τ, 1 ≤ τ → τ < k → ∀ i, 1 ≤ i → i ≤ H + 1 → Measurable (x τ i))
    (ha : ∀ τ, 1 ≤ τ → τ < k → ∀ i, 1 ≤ i → i ≤ H → Measurable (a τ i)) :
    ∀ n, n ≤ H → ∀ (z : Ω → S), Measurable z → ∀ b,
      Measurable (fun ω => lsviQRem φ r lam β H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k n
        (z ω) b) := by
  intro n
  induction n with
  | zero => intro _ z _ b; simp only [lsviQRem]; exact measurable_const
  | succ m ih =>
    intro hm z hz b
    have hj1 : 1 ≤ H - m := by omega
    have hj2 : H - m ≤ H := by omega
    have hφτ : ∀ τ ∈ Finset.Ico 1 k,
        Measurable (fun ω => WithLp.ofLp (φ (x τ (H - m) ω) (a τ (H - m) ω))) := by
      intro τ hτ
      obtain ⟨hτ1, hτk⟩ := Finset.mem_Ico.mp hτ
      exact c3a_compv φ hφ (hx τ hτ1 hτk _ hj1 (by omega)) (ha τ hτ1 hτk _ hj1 hj2)
    have hG : ∀ i j, Measurable (fun ω =>
        LinearMDPRL.Linear.gram φ lam (fun τ i => x τ i ω) (fun τ i => a τ i ω) k (H - m) i j) := by
      intro i j
      simp only [LinearMDPRL.Linear.gram, Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply,
        Matrix.smul_apply]
      refine (Finset.measurable_sum _ fun τ hτ => ?_).add measurable_const
      exact ((measurable_pi_apply i).comp (hφτ τ hτ)).mul ((measurable_pi_apply j).comp (hφτ τ hτ))
    have hinv := e5_meas_inv (M := fun ω =>
      LinearMDPRL.Linear.gram φ lam (fun τ i => x τ i ω) (fun τ i => a τ i ω) k (H - m)) hG
    have hVn : ∀ τ ∈ Finset.Ico 1 k, Measurable (fun ω => Finset.univ.sup' Finset.univ_nonempty
        (fun c => lsviQRem φ r lam β H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k m
          (x τ (H - m + 1) ω) c)) := by
      intro τ hτ
      obtain ⟨hτ1, hτk⟩ := Finset.mem_Ico.mp hτ
      have hz' := hx τ hτ1 hτk (H - m + 1) (by omega) (by omega)
      have h := Finset.measurable_sup' (s := Finset.univ) Finset.univ_nonempty
        (f := fun c ω => lsviQRem φ r lam β H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k m
          (x τ (H - m + 1) ω) c) fun c _ => ih (by omega) _ hz' c
      have e : (Finset.univ.sup' Finset.univ_nonempty (fun c ω => lsviQRem φ r lam β H
          (fun τ i => x τ i ω) (fun τ i => a τ i ω) k m (x τ (H - m + 1) ω) c)) =
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun c => lsviQRem φ r lam β H
            (fun τ i => x τ i ω) (fun τ i => a τ i ω) k m (x τ (H - m + 1) ω) c) := by
        funext ω; rw [Finset.sup'_apply]
      rw [e] at h
      exact h
    have hw : Measurable (fun ω => WithLp.ofLp (ridgeW φ r lam (fun τ i => x τ i ω)
        (fun τ i => a τ i ω) k (H - m) (fun y => Finset.univ.sup' Finset.univ_nonempty
          (fun c => lsviQRem φ r lam β H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k m y c)))) := by
      simp only [ridgeW, WithLp.ofLp_toLp]
      refine measurable_pi_iff.mpr fun i => ?_
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.measurable_sum _ fun j _ => (hinv i j).mul ?_
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.measurable_sum _ fun τ hτ => ?_
      obtain ⟨hτ1, hτk⟩ := Finset.mem_Ico.mp hτ
      exact ((c3a_comp (r (H - m)) (hr (H - m)) (hx τ hτ1 hτk _ hj1 (by omega))
        (ha τ hτ1 hτk _ hj1 hj2)).add (hVn τ hτ)).mul ((measurable_pi_apply j).comp (hφτ τ hτ))
    have hφz : Measurable (fun ω => WithLp.ofLp (φ (z ω) b)) :=
      (WithLp.measurable_ofLp 2 _).comp ((hφ b).comp hz)
    simp only [lsviQRem, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    refine Measurable.min ?_ measurable_const
    refine Measurable.add ?_ (measurable_const.mul ?_)
    · simp only [dotProduct]
      exact Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp hw).mul ((measurable_pi_apply i).comp hφz)
    · exact Real.continuous_sqrt.measurable.comp (e5_meas_quad hinv hφz hφz)


lemma c3a_tIdx_le (H τ i k h : ℕ) (hτ1 : 1 ≤ τ) (hτk : τ < k) (hi : i ≤ H + 1) :
    LinearMDPRL.Linear.tIdx H τ i ≤ LinearMDPRL.Linear.tIdx H k h := by
  unfold LinearMDPRL.Linear.tIdx
  have h1 : (τ - 1) * (H + 1) + (H + 1) ≤ (k - 1) * (H + 1) := by
    have : (τ - 1) + 1 ≤ k - 1 := by omega
    calc (τ - 1) * (H + 1) + (H + 1) = ((τ - 1) + 1) * (H + 1) := by ring
      _ ≤ (k - 1) * (H + 1) := Nat.mul_le_mul_right _ this
  omega


open MeasureTheory Matrix LinearMDPRL.Linear in
/-- C3a: in an LSVI-UCB run, the action `a^k_h` is `𝓕_{t(k,h)}`-measurable. -/
theorem c3a_actions {Ω S A : Type*} [MeasurableSpace S] [Fintype A] [Nonempty A]
    [LinearOrder A] [MeasurableSpace A] [DiscreteMeasurableSpace A] {d : ℕ}
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (𝓕 : Filtration ℕ mΩ) (M : EpisodicMDP S A)
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (hφ : ∀ b, Measurable (fun x => φ x b))
    (lam : ℝ) (β : ℕ → ℝ) (H K : ℕ) (x : ℕ → ℕ → Ω → S) (a : ℕ → ℕ → Ω → A)
    (hrun : IsLSVIUCBRun μ 𝓕 M φ lam β H K x a) :
    ∀ k, 1 ≤ k → k ≤ K → ∀ h, 1 ≤ h → h ≤ H → Measurable[𝓕 (tIdx H k h)] (a k h) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hkK h hh1 hhH
    have hfun : a k h = fun ω => greedy (fun b => lsviQ φ M.r lam β H (fun τ i => x τ i ω)
        (fun τ i => a τ i ω) k h (x k h ω) b) := by
      funext ω
      exact hrun.actions ω k (Finset.mem_Icc.mpr ⟨hk1, hkK⟩) h (Finset.mem_Icc.mpr ⟨hh1, hhH⟩)
    have hxk : Measurable[𝓕 (tIdx H k h)] (x k h) :=
      hrun.adapted k (Finset.mem_Icc.mpr ⟨hk1, hkK⟩) h (Finset.mem_Icc.mpr ⟨hh1, by omega⟩)
    have hQ : ∀ b, Measurable[𝓕 (tIdx H k h)] (fun ω => lsviQ φ M.r lam β H
        (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h (x k h ω) b) := by
      intro b
      simp only [lsviQ, if_pos (And.intro hh1 hhH)]
      refine @c3a_Q_meas Ω S A (𝓕 (tIdx H k h)) _ _ _ _ _ d φ hφ M.r (fun j b => M.r_meas j b)
        lam β H x a k ?_ ?_ (H + 1 - h) (by omega) (x k h) hxk b
      · intro τ hτ1 hτk i hi1 hi2
        exact (hrun.adapted τ (Finset.mem_Icc.mpr ⟨hτ1, by omega⟩) i
          (Finset.mem_Icc.mpr ⟨hi1, hi2⟩)).mono (𝓕.mono (c3a_tIdx_le H τ i k h hτ1 hτk hi2)) le_rfl
      · intro τ hτ1 hτk i hi1 hi2
        exact (ih τ hτk hτ1 (by omega) i hi1 hi2).mono
          (𝓕.mono (c3a_tIdx_le H τ i k h hτ1 hτk (by omega))) le_rfl
    rw [hfun]
    refine @measurable_to_countable' A Ω _ _ (𝓕 (tIdx H k h)) _ fun b0 => ?_
    exact @c5b_greedy_set Ω A (𝓕 (tIdx H k h)) _ _ _ _ hQ b0


open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
/-- C3c: fixed-function self-normalized bound along an LSVI-UCB run (fixed episode k, step h). -/
theorem c3c_fixed {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
    [MeasurableSpace A] [DiscreteMeasurableSpace A] {d : ℕ}
    {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝓕 : Filtration ℕ mΩ) (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d))
    (hφ : ∀ b, Measurable (fun x => φ x b)) (β : ℕ → ℝ) (H K : ℕ)
    (x : ℕ → ℕ → Ω → S) (a : ℕ → ℕ → Ω → A) (hrun : IsLSVIUCBRun μ 𝓕 M φ 1 β H K x a)
    (k h : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ K) (hh1 : 1 ≤ h) (hhH : h ≤ H)
    (f : S → ℝ) (hf : Measurable f) (Hr : ℝ) (hHr : 0 < Hr) (hf0 : ∀ y, f y ∈ Set.Icc 0 Hr)
    (δ : ℝ) (hδ : 0 < δ) :
    μ {ω | Hr ^ 2 / 2 * Real.log (Real.sqrt
          (LinearMDPRL.Linear.gram φ 1 (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h).det / δ) <
        (∑ τ ∈ Finset.Ico 1 k, (f (x τ (h + 1) ω) - ∫ y, f y ∂(M.P h (x τ h ω, a τ h ω))) •
            WithLp.ofLp (φ (x τ h ω) (a τ h ω))) ⬝ᵥ
          ((LinearMDPRL.Linear.gram φ 1 (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h)⁻¹ *ᵥ
            (∑ τ ∈ Finset.Ico 1 k, (f (x τ (h + 1) ω) - ∫ y, f y ∂(M.P h (x τ h ω, a τ h ω))) •
              WithLp.ofLp (φ (x τ h ω) (a τ h ω))))}
      ≤ ENNReal.ofReal δ := by
  haveI := M.isMarkov h
  have hmono : Monotone (fun t : ℕ => 𝓕 (tIdx H (t + 1) h)) := by
    intro i j hij
    refine 𝓕.mono ?_
    unfold tIdx
    have : i * (H + 1) ≤ j * (H + 1) := Nat.mul_le_mul_right _ hij
    simp only [Nat.add_sub_cancel]
    omega
  let G : Filtration ℕ mΩ := ⟨fun t => 𝓕 (tIdx H (t + 1) h), hmono, fun t => 𝓕.le _⟩
  have hGt : ∀ t, G t = 𝓕 (tIdx H (t + 1) h) := fun t => rfl
  have hact := c3a_actions μ 𝓕 M φ hφ 1 β H K x a hrun
  have hxm : ∀ t, t < k - 1 → Measurable[G t] (x (t + 1) h) := fun t ht => by
    rw [hGt]; exact hrun.adapted (t + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) h
      (Finset.mem_Icc.mpr ⟨hh1, by omega⟩)
  have ham : ∀ t, t < k - 1 → Measurable[G t] (a (t + 1) h) := fun t ht => by
    rw [hGt]; exact hact (t + 1) (by omega) (by omega) h hh1 hhH
  have hC2 := c2_selfnorm_markov μ G (M.P h)
    (fun t ω => WithLp.ofLp (φ (x (t + 1) h ω) (a (t + 1) h ω)))
    (fun t ω => (x (t + 1) h ω, a (t + 1) h ω)) (fun t ω => x (t + 1) (h + 1) ω) (k - 1)
    (fun t ht => @c3a_compv Ω S A (G t) _ _ _ _ d φ hφ _ (hxm t ht) _ (ham t ht))
    (fun t ht => (hxm t ht).prodMk (ham t ht))
    (fun t ht => by
      show Measurable[𝓕 (tIdx H (t + 1 + 1) h)] (x (t + 1) (h + 1))
      refine (hrun.adapted (t + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) (h + 1)
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).mono (𝓕.mono ?_) le_rfl
      unfold tIdx
      have : (t + 1 - 1) * (H + 1) + (H + 1) = (t + 1 + 1 - 1) * (H + 1) := by
        simp only [Nat.add_sub_cancel]; ring
      omega)
    (fun t ht B hB => hrun.transition (t + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) h
      (Finset.mem_Icc.mpr ⟨hh1, hhH⟩) B hB)
    f hf Hr hHr hf0 δ hδ
  refine le_trans (measure_mono ?_) hC2
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hS : ∑ t ∈ Finset.range (k - 1), (f (x (t + 1) (h + 1) ω) -
        ∫ y, f y ∂(M.P h (x (t + 1) h ω, a (t + 1) h ω))) •
          WithLp.ofLp (φ (x (t + 1) h ω) (a (t + 1) h ω)) =
      ∑ τ ∈ Finset.Ico 1 k, (f (x τ (h + 1) ω) - ∫ y, f y ∂(M.P h (x τ h ω, a τ h ω))) •
        WithLp.ofLp (φ (x τ h ω) (a τ h ω)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl fun t _ => by rw [add_comm 1 t]
  have hV : 1 + ∑ t ∈ Finset.range (k - 1), vecMulVec (WithLp.ofLp (φ (x (t + 1) h ω)
        (a (t + 1) h ω))) (WithLp.ofLp (φ (x (t + 1) h ω) (a (t + 1) h ω))) =
      LinearMDPRL.Linear.gram φ 1 (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h := by
    unfold LinearMDPRL.Linear.gram
    rw [Finset.sum_Ico_eq_sum_range, one_smul, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun t _ => by rw [add_comm 1 t]
  rw [hS, hV]
  exact hω


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
lemma c5b_meas_quad {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) {v : Ω → Fin d → ℝ} (hv : Measurable v) :
    Measurable fun ω => v ω ⬝ᵥ M *ᵥ v ω := by
  simp only [dotProduct, mulVec]
  refine Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hv).mul ?_
  exact Finset.measurable_sum _ fun j _ => measurable_const.mul ((measurable_pi_apply j).comp hv)


open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma c5b_lsviQ_meas {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A] {d : ℕ}
    (H : ℕ) (r : ℕ → S → A → ℝ) (φ : S → A → EuclideanSpace ℝ (Fin d))
    (hφ : ∀ a, Measurable (fun x => φ x a)) (lam : ℝ) (β : ℕ → ℝ)
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) (a : A) :
    Measurable (fun x => lsviQ φ r lam β H xs as k h x a) := by
  unfold lsviQ
  split_ifs with hh
  · rcases Nat.eq_zero_or_eq_succ_pred (H + 1 - h) with hn | hn
    · rw [hn]; simp only [lsviQRem]; exact measurable_const
    · rw [hn]
      simp only [lsviQRem]
      have hv : Measurable fun x => WithLp.ofLp (φ x a) :=
        (WithLp.measurable_ofLp 2 _).comp (hφ a)
      refine Measurable.min ?_ measurable_const
      refine ((hφ a).inner_const).add (measurable_const.mul ?_)
      exact Real.continuous_sqrt.measurable.comp (c5b_meas_quad _ hv)
  · exact measurable_const


open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma c4_gram_psd {S A : Type*} {d : ℕ} (φ : S → A → EuclideanSpace ℝ (Fin d))
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) :
    (∑ τ ∈ Finset.Ico 1 k, vecMulVec (WithLp.ofLp (φ (xs τ h) (as τ h)))
      (WithLp.ofLp (φ (xs τ h) (as τ h)))).PosSemidef := by
  refine posSemidef_sum _ fun τ _ => ?_
  have hh := posSemidef_vecMulVec_self_star (WithLp.ofLp (φ (xs τ h) (as τ h)))
  rwa [star_trivial] at hh


open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma c4_gram_pd {S A : Type*} {d : ℕ} (φ : S → A → EuclideanSpace ℝ (Fin d))
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) :
    (LinearMDPRL.Linear.gram φ 1 xs as k h).PosDef := by
  unfold LinearMDPRL.Linear.gram
  rw [one_smul, add_comm]
  exact PosDef.one.add_posSemidef (c4_gram_psd φ xs as k h)


open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma c4_gram_low {S A : Type*} {d : ℕ} (φ : S → A → EuclideanSpace ℝ (Fin d))
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) (u : Fin d → ℝ) :
    1 * (u ⬝ᵥ u) ≤ u ⬝ᵥ LinearMDPRL.Linear.gram φ 1 xs as k h *ᵥ u := by
  unfold LinearMDPRL.Linear.gram
  rw [one_smul, add_mulVec, one_mulVec, dotProduct_add, one_mul]
  have := (c4_gram_psd φ xs as k h).dotProduct_mulVec_nonneg u
  rw [star_trivial] at this
  linarith


open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma c4_lsviV_le {S A : Type*} [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (r : ℕ → S → A → ℝ) (lam : ℝ) (β : ℕ → ℝ) (H : ℕ)
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) (y : S) :
    lsviV φ r lam β H xs as k h y ≤ H := by
  unfold lsviV
  refine Finset.sup'_le _ _ fun a _ => ?_
  unfold lsviQ
  split_ifs
  · rcases Nat.eq_zero_or_eq_succ_pred (H + 1 - h) with hn | hn
    · rw [hn]; simp only [lsviQRem]; exact Nat.cast_nonneg _
    · rw [hn]; simp only [lsviQRem]; exact min_le_right _ _
  · exact Nat.cast_nonneg _


open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma c4_lsviV_meas {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A] {d : ℕ}
    (H : ℕ) (r : ℕ → S → A → ℝ) (φ : S → A → EuclideanSpace ℝ (Fin d))
    (hφ : ∀ a, Measurable (fun x => φ x a)) (lam : ℝ) (β : ℕ → ℝ)
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) :
    Measurable (lsviV φ r lam β H xs as k h) := by
  have : lsviV φ r lam β H xs as k h = Finset.univ.sup' Finset.univ_nonempty
      (fun a x => lsviQ φ r lam β H xs as k h x a) := by
    funext x; simp only [lsviV, Finset.sup'_apply]
  rw [this]
  exact Finset.measurable_sup' _ fun a _ => c5b_lsviQ_meas H r φ hφ lam β xs as k h a


lemma c4_abs_cs (x a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : x ^ 2 ≤ a * b) :
    |x| ≤ Real.sqrt a * Real.sqrt b := by
  rw [← Real.sqrt_mul ha]
  exact Real.abs_le_sqrt h



/-! C3b: deterministic covering lemmas for the clipped LSVI value class (3406357c). -/


open Matrix in
/-- The clipped LSVI value class `f_{w,A}(y) = max 0 (max_a min(⟨φ,w⟩ + b √(φᵀAφ), H))`. -/
noncomputable def c3F {S A : Type*} [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (H b : ℝ) (w : Fin d → ℝ)
    (Am : Matrix (Fin d) (Fin d) ℝ) (y : S) : ℝ :=
  max 0 (Finset.univ.sup' Finset.univ_nonempty (fun a =>
    min (WithLp.ofLp (φ y a) ⬝ᵥ w + b * Real.sqrt (WithLp.ofLp (φ y a) ⬝ᵥ (Am *ᵥ WithLp.ofLp (φ y a))))
      H))


lemma c3_sqrt_diff (a b : ℝ) : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a - b| := by
  have key : ∀ x y : ℝ, Real.sqrt x - Real.sqrt y ≤ Real.sqrt |x - y| := by
    intro x y
    rcases le_total y 0 with hy | hy
    · rw [Real.sqrt_eq_zero'.mpr hy, sub_zero]
      exact Real.sqrt_le_sqrt (le_trans (by linarith : x ≤ x - y) (le_abs_self _))
    · have h1 : Real.sqrt x ≤ Real.sqrt (y + |x - y|) :=
        Real.sqrt_le_sqrt (by linarith [le_abs_self (x - y)])
      have h2 : Real.sqrt (y + |x - y|) ≤ Real.sqrt y + Real.sqrt |x - y| := by
        rw [Real.sqrt_le_left (by positivity)]
        have := Real.sq_sqrt hy
        have := Real.sq_sqrt (abs_nonneg (x - y))
        nlinarith [Real.sqrt_nonneg y, Real.sqrt_nonneg |x - y|]
      linarith
  rw [abs_le]
  constructor
  · have := key b a; rw [abs_sub_comm] at this; linarith
  · exact key a b


lemma c3_dot_diff {d : ℕ} (p w w' : Fin d → ℝ) (hp : ∀ i, |p i| ≤ 1) :
    |p ⬝ᵥ w - p ⬝ᵥ w'| ≤ ∑ i, |w i - w' i| := by
  rw [← dotProduct_sub]
  unfold dotProduct
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Pi.sub_apply, abs_mul]
  calc |p i| * |w i - w' i| ≤ 1 * |w i - w' i| := by gcongr; exact hp i
    _ = _ := one_mul _


open Matrix in
lemma c3_quad_diff {d : ℕ} (p : Fin d → ℝ) (Am Am' : Matrix (Fin d) (Fin d) ℝ)
    (hp : ∀ i, |p i| ≤ 1) :
    |p ⬝ᵥ (Am *ᵥ p) - p ⬝ᵥ (Am' *ᵥ p)| ≤ ∑ i, ∑ j, |Am i j - Am' i j| := by
  have hexp : ∀ B : Matrix (Fin d) (Fin d) ℝ, p ⬝ᵥ (B *ᵥ p) = ∑ i, ∑ j, p i * B i j * p j := by
    intro B
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, hexp, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have e : p i * Am i j * p j - p i * Am' i j * p j = (p i * p j) * (Am i j - Am' i j) := by ring
  rw [e, abs_mul, abs_mul]
  have h1 := hp i
  have h2 := hp j
  have h3 : |p i| * |p j| ≤ 1 := by nlinarith [abs_nonneg (p i), abs_nonneg (p j)]
  nlinarith [abs_nonneg (Am i j - Am' i j), abs_nonneg (p i), abs_nonneg (p j)]


lemma c3_sup'_diff {A : Type*} [Fintype A] [Nonempty A] (f g : A → ℝ) (D : ℝ)
    (h : ∀ a, |f a - g a| ≤ D) :
    |Finset.univ.sup' Finset.univ_nonempty f - Finset.univ.sup' Finset.univ_nonempty g| ≤ D := by
  have k : ∀ f g : A → ℝ, (∀ a, |f a - g a| ≤ D) →
      Finset.univ.sup' Finset.univ_nonempty f ≤ Finset.univ.sup' Finset.univ_nonempty g + D := by
    intro f g h
    refine Finset.sup'_le _ _ fun a _ => ?_
    have h1 := (abs_le.mp (h a)).2
    have h2 := Finset.le_sup' g (Finset.mem_univ a)
    linarith
  rw [abs_le]
  constructor
  · have := k g f (fun a => by rw [abs_sub_comm]; exact h a); linarith
  · have := k f g h; linarith


lemma c3_clip_diff (u v H : ℝ) : |max 0 (min u H) - max 0 (min v H)| ≤ |u - v| := by
  rw [max_comm 0, max_comm 0]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp


open Matrix in
lemma c3F_diff {S A : Type*} [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (hφ : ∀ y a i, |WithLp.ofLp (φ y a) i| ≤ 1)
    (H b : ℝ) (hb : 0 ≤ b) (w w' : Fin d → ℝ) (Am Am' : Matrix (Fin d) (Fin d) ℝ) (y : S) :
    |c3F φ H b w Am y - c3F φ H b w' Am' y| ≤
      ∑ i, |w i - w' i| + b * Real.sqrt (∑ i, ∑ j, |Am i j - Am' i j|) := by
  unfold c3F
  have hmax : ∀ u v : ℝ, |max 0 u - max 0 v| ≤ |u - v| := by
    intro u v
    rw [max_comm 0, max_comm 0]
    exact abs_max_sub_max_le_abs _ _ _
  refine (hmax _ _).trans (c3_sup'_diff _ _ _ fun a => ?_)
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp only [sub_self, abs_zero]
  refine max_le ?_ (by positivity)
  have e1 := c3_dot_diff (WithLp.ofLp (φ y a)) w w' (hφ y a)
  have e2 := c3_sqrt_diff (WithLp.ofLp (φ y a) ⬝ᵥ (Am *ᵥ WithLp.ofLp (φ y a)))
    (WithLp.ofLp (φ y a) ⬝ᵥ (Am' *ᵥ WithLp.ofLp (φ y a)))
  have e3 := c3_quad_diff (WithLp.ofLp (φ y a)) Am Am' (hφ y a)
  have e4 : Real.sqrt |WithLp.ofLp (φ y a) ⬝ᵥ (Am *ᵥ WithLp.ofLp (φ y a)) -
      WithLp.ofLp (φ y a) ⬝ᵥ (Am' *ᵥ WithLp.ofLp (φ y a))| ≤
      Real.sqrt (∑ i, ∑ j, |Am i j - Am' i j|) := Real.sqrt_le_sqrt e3
  have e5 : |b * Real.sqrt (WithLp.ofLp (φ y a) ⬝ᵥ (Am *ᵥ WithLp.ofLp (φ y a))) -
      b * Real.sqrt (WithLp.ofLp (φ y a) ⬝ᵥ (Am' *ᵥ WithLp.ofLp (φ y a)))| ≤
      b * Real.sqrt (∑ i, ∑ j, |Am i j - Am' i j|) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hb]
    exact mul_le_mul_of_nonneg_left (e2.trans e4) hb
  calc _ = |(WithLp.ofLp (φ y a) ⬝ᵥ w - WithLp.ofLp (φ y a) ⬝ᵥ w') +
        (b * Real.sqrt (WithLp.ofLp (φ y a) ⬝ᵥ (Am *ᵥ WithLp.ofLp (φ y a))) -
          b * Real.sqrt (WithLp.ofLp (φ y a) ⬝ᵥ (Am' *ᵥ WithLp.ofLp (φ y a))))| := by
        congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add e1 e5)


/-- One-dimensional grid: `{-L + m ε | m ≤ M}` covers `[-L, L]` at mesh `ε`. -/
lemma c3_grid1 (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ Gr : Finset ℝ, (Gr.card : ℝ) ≤ 2 * L / ε + 1 ∧
      ∀ z, |z| ≤ L → ∃ g ∈ Gr, |z - g| ≤ ε := by
  classical
  set M : ℕ := ⌊2 * L / ε⌋₊ with hM
  refine ⟨(Finset.range (M + 1)).image (fun m : ℕ => -L + m * ε), ?_, ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Finset.card_range]
    push_cast
    have := Nat.floor_le (show 0 ≤ 2 * L / ε by positivity)
    linarith
  · intro z hz
    obtain ⟨hz1, hz2⟩ := abs_le.mp hz
    set m : ℕ := ⌊(z + L) / ε⌋₊ with hm
    have h0 : 0 ≤ (z + L) / ε := div_nonneg (by linarith) hε.le
    have hm1 : (m : ℝ) ≤ (z + L) / ε := Nat.floor_le h0
    have hm2 : (z + L) / ε < m + 1 := Nat.lt_floor_add_one _
    refine ⟨-L + m * ε, Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr ?_, rfl⟩, ?_⟩
    · have : m ≤ M := Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hε.le)
      omega
    · rw [le_div_iff₀ hε] at hm1
      rw [div_lt_iff₀ hε] at hm2
      rw [abs_le]; constructor <;> nlinarith


lemma c3_coord_le {d : ℕ} (u : Fin d → ℝ) (i : Fin d) : |u i| ≤ Real.sqrt (u ⬝ᵥ u) := by
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  unfold dotProduct
  calc u i ^ 2 = u i * u i := sq _
    _ ≤ ∑ j, u j * u j :=
      Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i)


open Matrix in
lemma c3_inv_vec_le {S A : Type*} {d : ℕ} (φ : S → A → EuclideanSpace ℝ (Fin d))
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) (v : Fin d → ℝ) :
    ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ v) ⬝ᵥ
      ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ v) ≤ v ⬝ᵥ v := by
  have hpd := c4_gram_pd φ xs as k h
  have hdet := e5_det_unit hpd
  have h1 := c4_gram_low φ xs as k h ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ v)
  rw [e5_mulVec_inv hdet, one_mul] at h1
  have h2 : ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ v) ⬝ᵥ v =
      v ⬝ᵥ (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ v := dotProduct_comm _ _
  have h3 := e5_inv_bound hpd one_pos (c4_gram_low φ xs as k h) v
  rw [div_one] at h3
  linarith


open Matrix in
lemma c3_inv_entry {S A : Type*} {d : ℕ} (φ : S → A → EuclideanSpace ℝ (Fin d))
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) (i j : Fin d) :
    |(LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ i j| ≤ 1 := by
  have hpd := c4_gram_pd φ xs as k h
  have hpsd := hpd.inv.posSemidef
  have he : ∀ a b : Fin d, (Pi.single a 1 : Fin d → ℝ) ⬝ᵥ
      (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ (Pi.single b 1 : Fin d → ℝ) =
      (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ a b := by
    intro a b; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hs : ∀ a : Fin d, (Pi.single a 1 : Fin d → ℝ) ⬝ᵥ (Pi.single a 1 : Fin d → ℝ) = 1 := by
    intro a; simp [dotProduct, Pi.single_apply]
  have hcs := e5_cs_psd hpsd (Pi.single i 1) (Pi.single j 1)
  have hii := e5_inv_bound hpd one_pos (c4_gram_low φ xs as k h) (Pi.single i 1)
  have hjj := e5_inv_bound hpd one_pos (c4_gram_low φ xs as k h) (Pi.single j 1)
  have hi0 := e5_a_nonneg hpd (Pi.single i 1)
  have hj0 := e5_a_nonneg hpd (Pi.single j 1)
  rw [he, he, he] at hcs
  rw [he, hs, div_one] at hii
  rw [he, hs, div_one] at hjj
  rw [he] at hi0 hj0
  have hsq : ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ i j) ^ 2 ≤ 1 := by nlinarith
  rw [abs_le]; constructor <;> nlinarith


open Matrix LinearMDPRL.Linear in
lemma c3_lsviV_eq {S A : Type*} [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (r : ℕ → S → A → ℝ) (β : ℕ → ℝ) (H : ℕ)
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h' : ℕ) (h1 : 1 ≤ h') (h2 : h' ≤ H)
    (hV0 : ∀ y, 0 ≤ lsviV φ r 1 β H xs as k h' y) :
    lsviV φ r 1 β H xs as k h' = c3F φ H (β k) (WithLp.ofLp (lsviW φ r 1 β H xs as k h'))
      (LinearMDPRL.Linear.gram φ 1 xs as k h')⁻¹ := by
  have hnext : (fun y => Finset.univ.sup' Finset.univ_nonempty
      (fun b => lsviQRem φ r 1 β H xs as k (H - h') y b)) = lsviV φ r 1 β H xs as k (h' + 1) := by
    funext y
    unfold lsviV lsviQ
    by_cases hc : h' + 1 ≤ H
    · have e : H + 1 - (h' + 1) = H - h' := by omega
      simp only [e, show 1 ≤ h' + 1 by omega, hc, and_self, if_true]
    · have e : H - h' = 0 := by omega
      simp only [e, lsviQRem, hc, and_false, if_false]
  have hW : lsviW φ r 1 β H xs as k h' =
      ridgeW φ r 1 xs as k h' (lsviV φ r 1 β H xs as k (h' + 1)) := by
    rw [lsviW, if_pos ⟨h1, h2⟩]
  have hval : ∀ y, lsviV φ r 1 β H xs as k h' y = Finset.univ.sup' Finset.univ_nonempty
      (fun a => min (WithLp.ofLp (φ y a) ⬝ᵥ WithLp.ofLp (lsviW φ r 1 β H xs as k h') +
        β k * Real.sqrt (WithLp.ofLp (φ y a) ⬝ᵥ
          ((LinearMDPRL.Linear.gram φ 1 xs as k h')⁻¹ *ᵥ WithLp.ofLp (φ y a)))) (H : ℝ)) := by
    intro y
    unfold lsviV
    refine Finset.sup'_congr _ rfl fun a _ => ?_
    unfold lsviQ
    rw [if_pos ⟨h1, h2⟩, show H + 1 - h' = (H - h') + 1 by omega, lsviQRem,
      show H - (H - h') = h' by omega, hnext, hW]
    beta_reduce
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      dotProduct_comm (WithLp.ofLp (ridgeW φ r 1 xs as k h' (lsviV φ r 1 β H xs as k (h' + 1))))]
  funext y
  unfold c3F
  rw [← hval y, max_eq_right (hV0 y)]


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


open Matrix in
lemma c3_vec_norm_le {d : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (v : ι → EuclideanSpace ℝ (Fin d)) (C : ℝ) (hc : ∀ i ∈ s, |c i| ≤ C)
    (hv : ∀ i ∈ s, ‖v i‖ ≤ 1) :
    Real.sqrt ((∑ i ∈ s, c i • WithLp.ofLp (v i)) ⬝ᵥ (∑ i ∈ s, c i • WithLp.ofLp (v i))) ≤
      s.card * C := by
  have hin : ∀ (u : EuclideanSpace ℝ (Fin d)), WithLp.ofLp u ⬝ᵥ WithLp.ofLp u = ‖u‖ ^ 2 := by
    intro u
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  have he : (∑ i ∈ s, c i • WithLp.ofLp (v i)) = WithLp.ofLp (∑ i ∈ s, c i • v i) := by
    simp [WithLp.ofLp_sum, WithLp.ofLp_smul]
  rw [he, hin, Real.sqrt_sq (norm_nonneg _)]
  calc ‖∑ i ∈ s, c i • v i‖ ≤ ∑ i ∈ s, ‖c i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, C := Finset.sum_le_sum fun i hi => by
        rw [norm_smul, Real.norm_eq_abs]
        calc |c i| * ‖v i‖ ≤ C * 1 :=
              mul_le_mul (hc i hi) (hv i hi) (norm_nonneg _) (le_trans (abs_nonneg _) (hc i hi))
          _ = C := mul_one C
    _ = s.card * C := by rw [Finset.sum_const, nsmul_eq_mul]


open Matrix LinearMDPRL.Linear in
lemma c3_w_bound {S A : Type*} [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (hφ : ∀ x a, ‖φ x a‖ ≤ 1)
    (r : ℕ → S → A → ℝ) (hr : ∀ j x a, r j x a ∈ Set.Icc (0 : ℝ) 1) (β : ℕ → ℝ) (H : ℕ)
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h' : ℕ) (h1 : 1 ≤ h') (h2 : h' ≤ H)
    (hV : ∀ y, lsviV φ r 1 β H xs as k (h' + 1) y ∈ Set.Icc (0 : ℝ) H) (i : Fin d) :
    |WithLp.ofLp (lsviW φ r 1 β H xs as k h') i| ≤ k * (1 + H) := by
  rw [lsviW, if_pos ⟨h1, h2⟩, ridgeW, WithLp.ofLp_toLp]
  refine (c3_coord_le _ i).trans ?_
  refine (Real.sqrt_le_sqrt (c3_inv_vec_le φ xs as k h' _)).trans ?_
  refine (c3_vec_norm_le (Finset.Ico 1 k)
    (fun τ => r h' (xs τ h') (as τ h') + lsviV φ r 1 β H xs as k (h' + 1) (xs τ (h' + 1)))
    (fun τ => φ (xs τ h') (as τ h')) (1 + H) ?_ ?_).trans ?_
  · intro τ _
    have e1 := hr h' (xs τ h') (as τ h')
    have e2 := hV (xs τ (h' + 1))
    rw [abs_le]; constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  · intro τ _; exact hφ _ _
  · rw [Nat.card_Ico]
    have hH : (0 : ℝ) ≤ 1 + H := by positivity
    have hk : ((k - 1 : ℕ) : ℝ) ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; simp
      · rw [Nat.cast_sub h0]; simp
    exact mul_le_mul_of_nonneg_right hk hH


open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma c3_perturb {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] {d : ℕ}
    (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)) (hφ : ∀ x a, ‖φ x a‖ ≤ 1)
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ)
    (V f : S → ℝ) (hV : Measurable V) (hf : Measurable f) (B ε : ℝ) (hε0 : 0 ≤ ε)
    (hVB : ∀ y, |V y| ≤ B) (hfB : ∀ y, |f y| ≤ B) (hε : ∀ y, |V y - f y| ≤ ε) :
    Real.sqrt ((∑ τ ∈ Finset.Ico 1 k, (V (xs τ (h + 1)) - ∫ y, V y ∂(M.P h (xs τ h, as τ h))) •
        WithLp.ofLp (φ (xs τ h) (as τ h))) ⬝ᵥ ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ
        (∑ τ ∈ Finset.Ico 1 k, (V (xs τ (h + 1)) - ∫ y, V y ∂(M.P h (xs τ h, as τ h))) •
          WithLp.ofLp (φ (xs τ h) (as τ h)))))
      ≤ Real.sqrt ((∑ τ ∈ Finset.Ico 1 k, (f (xs τ (h + 1)) -
            ∫ y, f y ∂(M.P h (xs τ h, as τ h))) • WithLp.ofLp (φ (xs τ h) (as τ h))) ⬝ᵥ
          ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ
          (∑ τ ∈ Finset.Ico 1 k, (f (xs τ (h + 1)) - ∫ y, f y ∂(M.P h (xs τ h, as τ h))) •
            WithLp.ofLp (φ (xs τ h) (as τ h)))))
        + 2 * ε * k := by
  haveI := M.isMarkov h
  have hpd := c4_gram_pd φ xs as k h
  have hipsd := hpd.inv.posSemidef
  obtain ⟨SV, hSV⟩ : ∃ v : Fin d → ℝ, v = ∑ τ ∈ Finset.Ico 1 k, (V (xs τ (h + 1)) -
      ∫ y, V y ∂(M.P h (xs τ h, as τ h))) • WithLp.ofLp (φ (xs τ h) (as τ h)) := ⟨_, rfl⟩
  obtain ⟨Sf, hSf⟩ : ∃ v : Fin d → ℝ, v = ∑ τ ∈ Finset.Ico 1 k, (f (xs τ (h + 1)) -
      ∫ y, f y ∂(M.P h (xs τ h, as τ h))) • WithLp.ofLp (φ (xs τ h) (as τ h)) := ⟨_, rfl⟩
  rw [← hSV, ← hSf]
  have hint : ∀ τ, |(∫ y, V y ∂(M.P h (xs τ h, as τ h))) - ∫ y, f y ∂(M.P h (xs τ h, as τ h))|
      ≤ ε := by
    intro τ
    have hVi : Integrable V (M.P h (xs τ h, as τ h)) :=
      Integrable.of_bound hV.aestronglyMeasurable B (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs]; exact hVB y)
    have hfi : Integrable f (M.P h (xs τ h, as τ h)) :=
      Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs]; exact hfB y)
    rw [← integral_sub hVi hfi, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := ε) (ae_of_all _ fun y => ?_)).trans ?_
    · rw [Real.norm_eq_abs]; exact hε y
    · simp
  have hΔ : SV - Sf = ∑ τ ∈ Finset.Ico 1 k, ((V (xs τ (h + 1)) - f (xs τ (h + 1))) -
      ((∫ y, V y ∂(M.P h (xs τ h, as τ h))) - ∫ y, f y ∂(M.P h (xs τ h, as τ h)))) •
        WithLp.ofLp (φ (xs τ h) (as τ h)) := by
    rw [hSV, hSf, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← sub_smul]
    congr 1
    ring
  have hnorm := c3_vec_norm_le (Finset.Ico 1 k) (fun τ => (V (xs τ (h + 1)) - f (xs τ (h + 1))) -
      ((∫ y, V y ∂(M.P h (xs τ h, as τ h))) - ∫ y, f y ∂(M.P h (xs τ h, as τ h))))
    (fun τ => φ (xs τ h) (as τ h)) (2 * ε) (fun τ _ => by
      have e1 := hε (xs τ (h + 1))
      have e2 := hint τ
      calc _ ≤ |V (xs τ (h + 1)) - f (xs τ (h + 1))| +
            |(∫ y, V y ∂(M.P h (xs τ h, as τ h))) - ∫ y, f y ∂(M.P h (xs τ h, as τ h))| :=
            abs_sub _ _
        _ ≤ 2 * ε := by linarith) (fun τ _ => hφ _ _)
  rw [← hΔ] at hnorm
  have htri := e5_norm_sub hipsd Sf (-(SV - Sf))
  have hsimp : Sf - -(SV - Sf) = SV := by abel
  rw [hsimp] at htri
  have hneg : (-(SV - Sf)) ⬝ᵥ (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ (-(SV - Sf)) =
      (SV - Sf) ⬝ᵥ (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ (SV - Sf) := by
    rw [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  rw [hneg] at htri
  have hib := e5_inv_bound hpd one_pos (c4_gram_low φ xs as k h) (SV - Sf)
  rw [div_one] at hib
  have hcard : ((Finset.Ico 1 k).card : ℝ) * (2 * ε) ≤ 2 * ε * k := by
    rw [Nat.card_Ico]
    have hk : ((k - 1 : ℕ) : ℝ) ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; simp
      · rw [Nat.cast_sub h0]; simp
    nlinarith
  calc _ ≤ _ := htri
    _ ≤ Real.sqrt (Sf ⬝ᵥ (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ Sf) +
          Real.sqrt ((SV - Sf) ⬝ᵥ (SV - Sf)) := by gcongr
    _ ≤ _ := by linarith


lemma c3_gridD {D : Type*} [Fintype D] [DecidableEq D] (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ Gr : Finset (D → ℝ), (Gr.card : ℝ) ≤ (2 * L / ε + 1) ^ Fintype.card D ∧
      ∀ z : D → ℝ, (∀ i, |z i| ≤ L) → ∃ g ∈ Gr, ∀ i, |z i - g i| ≤ ε := by
  obtain ⟨G1, hcard, hcov⟩ := c3_grid1 L ε hL hε
  refine ⟨Fintype.piFinset (fun _ => G1), ?_, ?_⟩
  · rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]
    push_cast
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcard _
  · intro z hz
    choose g hg using fun i => hcov (z i) (hz i)
    exact ⟨fun i => g i, Fintype.mem_piFinset.mpr fun i => (hg i).1, fun i => (hg i).2⟩


open Matrix in
lemma c3F_meas {S A : Type*} [MeasurableSpace S] [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (hφ : ∀ a, Measurable fun x => φ x a)
    (H b : ℝ) (w : Fin d → ℝ) (Am : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (c3F φ H b w Am) := by
  have e : c3F φ H b w Am = fun y => max 0 ((Finset.univ.sup' Finset.univ_nonempty
      (fun a y => min (WithLp.ofLp (φ y a) ⬝ᵥ w + b * Real.sqrt (WithLp.ofLp (φ y a) ⬝ᵥ
        (Am *ᵥ WithLp.ofLp (φ y a)))) H)) y) := by
    funext y; simp only [c3F, Finset.sup'_apply]
  rw [e]
  refine measurable_const.max (Finset.measurable_sup' _ fun a _ => ?_)
  have hv : Measurable fun y => WithLp.ofLp (φ y a) := (WithLp.measurable_ofLp 2 _).comp (hφ a)
  refine Measurable.min ?_ measurable_const
  refine Measurable.add ?_ (measurable_const.mul
    (Real.continuous_sqrt.measurable.comp (c5b_meas_quad Am hv)))
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hv).mul measurable_const


lemma c3F_mem {S A : Type*} [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (H b : ℝ) (hH : 0 ≤ H) (w : Fin d → ℝ)
    (Am : Matrix (Fin d) (Fin d) ℝ) (y : S) : c3F φ H b w Am y ∈ Set.Icc 0 H := by
  unfold c3F
  refine ⟨le_max_left _ _, max_le hH ?_⟩
  exact Finset.sup'_le _ _ fun a _ => min_le_right _ _


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
lemma c1_log_ge (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : a ≤ 2 * Real.log (1 + a) := by
  have h := Real.one_sub_inv_le_log_of_pos (x := 1 + a) (by linarith)
  have h2 : 1 - (1 + a)⁻¹ = a / (1 + a) := by field_simp; ring
  rw [h2] at h
  have h3 : a / 2 ≤ a / (1 + a) := by
    apply div_le_div_of_nonneg_left h0 (by linarith) (by linarith)
  linarith


open MeasureTheory ProbabilityTheory Matrix NNReal in
lemma c1_core {d : ℕ} (hd : 0 < d) (y : ℕ → Fin d → ℝ) (hy : ∀ t, y t ⬝ᵥ y t ≤ 1) (K : ℕ) :
    ∑ s ∈ Finset.range K, y (s + 1) ⬝ᵥ
        (BanditAlgorithm.regularizedDesignMatrix d 1 (fun s (_ : Unit) => y s) s ())⁻¹ *ᵥ y (s + 1)
      ≤ 2 * d * Real.log (1 + (K : ℝ) / d) := by
  set V : ℕ → Matrix (Fin d) (Fin d) ℝ :=
    fun s => BanditAlgorithm.regularizedDesignMatrix d 1 (fun s (_ : Unit) => y s) s () with hV
  have hpd : ∀ s, (V s).PosDef := fun s => e5_V_posdef d one_pos _ s ()
  set a : ℕ → ℝ := fun s => y (s + 1) ⬝ᵥ (V s)⁻¹ *ᵥ y (s + 1) with ha
  have ha0 : ∀ s, 0 ≤ a s := fun s => e5_a_nonneg (hpd s) _
  have ha1 : ∀ s, a s ≤ 1 := fun s => by
    have := e5_inv_bound (hpd s) one_pos (fun u => e5_V_low d 1 (fun s (_ : Unit) => y s) s () u)
      (y (s + 1))
    simp only [div_one] at this
    exact le_trans this (hy _)
  have hdet : (V K).det = ∏ s ∈ Finset.range K, (1 + a s) := by
    have := e5_V_det d one_pos (fun s (_ : Unit) => y s) K ()
    simpa using this
  have hpos : ∀ s, 0 < 1 + a s := fun s => by linarith [ha0 s]
  have hlog : Real.log (V K).det = ∑ s ∈ Finset.range K, Real.log (1 + a s) := by
    rw [hdet, Real.log_prod]
    intro s _; exact (hpos s).ne'
  have htr : (V K).trace ≤ d + K := by
    have := e5_V_trace d 1 (fun s (_ : Unit) => y s) K ()
    have h2 : ∑ s ∈ Finset.range K, y (s + 1) ⬝ᵥ y (s + 1) ≤ K := by
      calc _ ≤ ∑ s ∈ Finset.range K, (1 : ℝ) := Finset.sum_le_sum fun s _ => hy _
        _ = K := by simp
    simp only [hV]
    linarith
  have hdd : (0 : ℝ) < d := by exact_mod_cast hd
  have hdetle : (V K).det ≤ (1 + (K : ℝ) / d) ^ d := by
    refine le_trans (e5_det_le_trace hd (hpd K)) ?_
    gcongr
    · exact div_nonneg ((hpd K).posSemidef.trace_nonneg) hdd.le
    · rw [div_le_iff₀ hdd]; rw [add_mul, div_mul_cancel₀ _ hdd.ne']; linarith
  have hlogle : Real.log (V K).det ≤ d * Real.log (1 + (K : ℝ) / d) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (hpd K).det_pos hdetle
  calc ∑ s ∈ Finset.range K, a s ≤ ∑ s ∈ Finset.range K, 2 * Real.log (1 + a s) :=
        Finset.sum_le_sum fun s _ => c1_log_ge _ (ha0 s) (ha1 s)
    _ = 2 * Real.log (V K).det := by rw [hlog, Finset.mul_sum]
    _ ≤ 2 * (d * Real.log (1 + (K : ℝ) / d)) := by linarith
    _ = 2 * d * Real.log (1 + (K : ℝ) / d) := by ring


open LinearMDPRL.Linear MeasureTheory ProbabilityTheory Matrix in
theorem c1_elliptical_potential {S A : Type*} {d : ℕ} (hd : 1 ≤ d)
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (hφ : ∀ x a, ‖φ x a‖ ≤ 1)
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (h K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K,
        (WithLp.ofLp (φ (xs k h) (as k h)) ⬝ᵥ
          ((gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ (xs k h) (as k h))))
      ≤ 2 * d * Real.log (1 + (K : ℝ) / d) := by
  set y : ℕ → Fin d → ℝ := fun s => WithLp.ofLp (φ (xs s h) (as s h)) with hy
  have hyy : ∀ t, y t ⬝ᵥ y t ≤ 1 := fun t => by
    have h1 := hφ (xs t h) (as t h)
    have h2 : y t ⬝ᵥ y t = ‖φ (xs t h) (as t h)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [hy, dotProduct, sq]
    rw [h2]
    nlinarith [norm_nonneg (φ (xs t h) (as t h))]
  have hgram : ∀ m : ℕ, gram φ 1 xs as (m + 1) h =
      BanditAlgorithm.regularizedDesignMatrix d 1 (fun s (_ : Unit) => y s) m () := by
    intro m
    have hS : ∑ τ ∈ Finset.Ico 1 (m + 1), vecMulVec (WithLp.ofLp (φ (xs τ h) (as τ h)))
          (WithLp.ofLp (φ (xs τ h) (as τ h))) =
        ∑ s ∈ Finset.range m, vecMulVec (y (s + 1)) (y (s + 1)) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, hy]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [add_comm 1 s]
    simp only [LinearMDPRL.Linear.gram, BanditAlgorithm.regularizedDesignMatrix]
    rw [hS, add_comm]
  have hsum : ∑ k ∈ Finset.Icc 1 K,
        (WithLp.ofLp (φ (xs k h) (as k h)) ⬝ᵥ
          ((gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ (xs k h) (as k h)))) =
      ∑ s ∈ Finset.range K, y (s + 1) ⬝ᵥ
        (BanditAlgorithm.regularizedDesignMatrix d 1 (fun s (_ : Unit) => y s) s ())⁻¹ *ᵥ
          y (s + 1) := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih, hgram]
  rw [hsum]
  exact c1_core hd y hyy K


open MeasureTheory ProbabilityTheory in
lemma c0_pt (c pr nr : ℝ) :
    c * (pr - nr) + (max c 0 * nr + max (-c) 0 * pr) = max c 0 * pr + max (-c) 0 * nr := by
  rcases le_total 0 c with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring


open MeasureTheory ProbabilityTheory in
lemma c0_lin_int {S : Type*} [MeasurableSpace S] {d : ℕ} (P : Measure S) [IsProbabilityMeasure P]
    (c : Fin d → ℝ) (mu : Fin d → SignedMeasure S)
    (hP : ∀ B, MeasurableSet B → (P B).toReal = ∑ i, c i * mu i B)
    (V : S → ℝ) (hV : Measurable V) (B : ℝ) (hVB : ∀ y, |V y| ≤ B) :
    ∫ y, V y ∂P = ∑ i, c i * ((∫ y, V y ∂((mu i).toJordanDecomposition.posPart)) -
      ∫ y, V y ∂((mu i).toJordanDecomposition.negPart)) := by
  classical
  set pos : Fin d → Measure S := fun i => (mu i).toJordanDecomposition.posPart with hpos
  set neg : Fin d → Measure S := fun i => (mu i).toJordanDecomposition.negPart with hneg
  haveI hposf : ∀ i, IsFiniteMeasure (pos i) := fun i =>
    inferInstanceAs (IsFiniteMeasure ((mu i).toJordanDecomposition.posPart))
  haveI hnegf : ∀ i, IsFiniteMeasure (neg i) := fun i =>
    inferInstanceAs (IsFiniteMeasure ((mu i).toJordanDecomposition.negPart))
  set cp : Fin d → ENNReal := fun i => ENNReal.ofReal (c i) with hcp
  set cn : Fin d → ENNReal := fun i => ENNReal.ofReal (-(c i)) with hcn
  have hsm : ∀ (e : ENNReal) (ν : Measure S) [IsFiniteMeasure ν], e ≠ ⊤ → IsFiniteMeasure (e • ν) :=
    fun e ν _ he => ⟨by
      rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top he.lt_top (measure_lt_top _ _)⟩
  set rp : Measure S := ∑ i, (cp i • pos i + cn i • neg i) with hrp
  set rn : Measure S := ∑ i, (cp i • neg i + cn i • pos i) with hrn
  have hsa : ∀ (e1 e2 : ENNReal) (a b : Measure S) [IsFiniteMeasure a] [IsFiniteMeasure b],
      e1 ≠ ⊤ → e2 ≠ ⊤ → IsFiniteMeasure (e1 • a + e2 • b) := by
    intro e1 e2 a b _ _ h1 h2
    haveI := hsm e1 a h1
    haveI := hsm e2 b h2
    exact ⟨by rw [Measure.add_apply]; exact ENNReal.add_lt_top.2 ⟨measure_lt_top _ _, measure_lt_top _ _⟩⟩
  haveI hrpf : IsFiniteMeasure rp := by
    haveI : ∀ i, IsFiniteMeasure ((fun i => cp i • pos i + cn i • neg i) i) := fun i =>
      hsa (cp i) (cn i) (pos i) (neg i) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    exact (inferInstance : IsFiniteMeasure (∑ i ∈ (Finset.univ : Finset (Fin d)),
      (fun i => cp i • pos i + cn i • neg i) i))
  haveI hrnf : IsFiniteMeasure rn := by
    haveI : ∀ i, IsFiniteMeasure ((fun i => cp i • neg i + cn i • pos i) i) := fun i =>
      hsa (cp i) (cn i) (neg i) (pos i) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    exact (inferInstance : IsFiniteMeasure (∑ i ∈ (Finset.univ : Finset (Fin d)),
      (fun i => cp i • neg i + cn i • pos i) i))
  have hmeas : P + rn = rp := by
    refine Measure.ext fun Bs hBs => ?_
    have h1 : (P + rn) Bs ≠ ⊤ := measure_ne_top _ _
    have h2 : rp Bs ≠ ⊤ := measure_ne_top _ _
    rw [← ENNReal.toReal_eq_toReal_iff' h1 h2]
    have hmu : ∀ i, mu i Bs = (pos i Bs).toReal - (neg i Bs).toReal := fun i => by
      have := SignedMeasure.apply_eq_posPart_real_sub_negPart_real (mu i) hBs
      simpa [hpos, hneg, measureReal_def] using this
    have hrpB : (rp Bs).toReal = ∑ i, (max (c i) 0 * (pos i Bs).toReal +
        max (-(c i)) 0 * (neg i Bs).toReal) := by
      rw [hrp, Measure.coe_finsetSum, Finset.sum_apply, ENNReal.toReal_sum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, hcp, hcn]
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
          ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
      · intro i _
        haveI := hsa (cp i) (cn i) (pos i) (neg i) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
        exact measure_ne_top _ _
    have hrnB : (rn Bs).toReal = ∑ i, (max (c i) 0 * (neg i Bs).toReal +
        max (-(c i)) 0 * (pos i Bs).toReal) := by
      rw [hrn, Measure.coe_finsetSum, Finset.sum_apply, ENNReal.toReal_sum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, hcp, hcn]
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
          ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
      · intro i _
        haveI := hsa (cp i) (cn i) (neg i) (pos i) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
        exact measure_ne_top _ _
    rw [Measure.add_apply, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hrpB, hrnB,
      hP Bs hBs, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hmu i]
    exact c0_pt (c i) _ _
  have hint : ∀ (ν : Measure S) [IsFiniteMeasure ν], Integrable V ν := fun ν _ =>
    Integrable.of_bound hV.aestronglyMeasurable B
      (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hVB y)
  have h : ∫ y, V y ∂(P + rn) = ∫ y, V y ∂rp := by rw [hmeas]
  rw [integral_add_measure (hint P) (hint rn)] at h
  have hI : ∀ (e1 e2 : ENNReal) (a b : Measure S) [IsFiniteMeasure a] [IsFiniteMeasure b],
      e1 ≠ ⊤ → e2 ≠ ⊤ →
      ∫ y, V y ∂(e1 • a + e2 • b) = e1.toReal * ∫ y, V y ∂a + e2.toReal * ∫ y, V y ∂b := by
    intro e1 e2 a b _ _ h1 h2
    haveI := hsm e1 a h1
    haveI := hsm e2 b h2
    rw [integral_add_measure (hint _) (hint _), integral_smul_measure, integral_smul_measure,
      smul_eq_mul, smul_eq_mul]
  have hrpI : ∫ y, V y ∂rp = ∑ i, (max (c i) 0 * ∫ y, V y ∂(pos i) +
      max (-(c i)) 0 * ∫ y, V y ∂(neg i)) := by
    rw [hrp, integral_finsetSum_measure]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hI _ _ _ _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
      simp only [ENNReal.toReal_ofReal']
    · intro i _
      haveI := hsm (cp i) (pos i) ENNReal.ofReal_ne_top
      haveI := hsm (cn i) (neg i) ENNReal.ofReal_ne_top
      exact hint _
  have hrnI : ∫ y, V y ∂rn = ∑ i, (max (c i) 0 * ∫ y, V y ∂(neg i) +
      max (-(c i)) 0 * ∫ y, V y ∂(pos i)) := by
    rw [hrn, integral_finsetSum_measure]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hI _ _ _ _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
      simp only [ENNReal.toReal_ofReal']
    · intro i _
      haveI := hsm (cp i) (neg i) ENNReal.ofReal_ne_top
      haveI := hsm (cn i) (pos i) ENNReal.ofReal_ne_top
      exact hint _
  have hPI : ∫ y, V y ∂P = ∫ y, V y ∂rp - ∫ y, V y ∂rn := by linarith
  rw [hPI, hrpI, hrnI, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases le_total 0 (c i) with hc | hc
  · rw [max_eq_left hc, max_eq_right (by linarith)]; ring
  · rw [max_eq_right hc, max_eq_left (by linarith)]; ring


open LinearMDPRL.Linear MeasureTheory ProbabilityTheory in
theorem c0_linear_integral {S A : Type} [MeasurableSpace S] [MeasurableSpace A]
    (d H : ℕ) (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d))
    (hM : IsLinearMDP M H d φ) (h : ℕ) (hh : h ∈ Finset.Icc 1 H) :
    (∃ θ : EuclideanSpace ℝ (Fin d), ‖θ‖ ≤ Real.sqrt d ∧ ∀ x a, M.r h x a = inner ℝ (φ x a) θ) ∧
    ∀ (V : S → ℝ) (B : ℝ), 0 ≤ B → Measurable V → (∀ y, |V y| ≤ B) →
      ∃ ν : EuclideanSpace ℝ (Fin d), ‖ν‖ ≤ B * Real.sqrt d ∧
        ∀ x a, ∫ y, V y ∂(M.P h (x, a)) = inner ℝ (φ x a) ν := by
  obtain ⟨-, -, hlin⟩ := hM
  obtain ⟨mu, θ, hP, hr, hθ, hTV⟩ := hlin h hh
  refine ⟨⟨θ, hθ, hr⟩, ?_⟩
  intro V B hB hV hVB
  set T : Fin d → ℝ := fun i => (∫ y, V y ∂((mu i).toJordanDecomposition.posPart)) -
      ∫ y, V y ∂((mu i).toJordanDecomposition.negPart) with hT
  refine ⟨WithLp.toLp 2 T, ?_, ?_⟩
  · have hTi : ∀ i, |T i| ≤ B * ((mu i).totalVariation Set.univ).toReal := by
      intro i
      have hp := norm_integral_le_of_norm_le_const (μ := (mu i).toJordanDecomposition.posPart)
        (f := V) (C := B) (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hVB y)
      have hn := norm_integral_le_of_norm_le_const (μ := (mu i).toJordanDecomposition.negPart)
        (f := V) (C := B) (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hVB y)
      have htv : ((mu i).totalVariation Set.univ).toReal =
          ((mu i).toJordanDecomposition.posPart Set.univ).toReal +
          ((mu i).toJordanDecomposition.negPart Set.univ).toReal := by
        rw [SignedMeasure.totalVariation, Measure.add_apply,
          ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      rw [htv]
      simp only [hT, Real.norm_eq_abs, measureReal_def] at hp hn ⊢
      calc |(∫ y, V y ∂((mu i).toJordanDecomposition.posPart)) -
            ∫ y, V y ∂((mu i).toJordanDecomposition.negPart)|
          ≤ |∫ y, V y ∂((mu i).toJordanDecomposition.posPart)| +
            |∫ y, V y ∂((mu i).toJordanDecomposition.negPart)| := abs_sub _ _
        _ ≤ _ := by nlinarith
    rw [EuclideanSpace.norm_eq]
    have hsum : ∑ i, ‖(WithLp.toLp 2 T : EuclideanSpace ℝ (Fin d)) i‖ ^ 2 ≤
        B ^ 2 * ∑ i, (((mu i).totalVariation Set.univ).toReal) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [Real.norm_eq_abs, sq_abs]
      have := hTi i
      have h0 := abs_nonneg (T i)
      calc T i ^ 2 = |T i| ^ 2 := (sq_abs _).symm
        _ ≤ (B * ((mu i).totalVariation Set.univ).toReal) ^ 2 := by gcongr
        _ = _ := by ring
    calc Real.sqrt (∑ i, ‖(WithLp.toLp 2 T : EuclideanSpace ℝ (Fin d)) i‖ ^ 2)
        ≤ Real.sqrt (B ^ 2 * ∑ i, (((mu i).totalVariation Set.univ).toReal) ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = B * Real.sqrt (∑ i, (((mu i).totalVariation Set.univ).toReal) ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB]
      _ ≤ B * Real.sqrt d := by gcongr
  · intro x a
    haveI : IsProbabilityMeasure (M.P h (x, a)) := (M.isMarkov h).isProbabilityMeasure (x, a)
    rw [c0_lin_int (M.P h (x, a)) (fun i => φ x a i) mu (hP x a) V hV B hVB]
    simp [PiLp.inner_apply, hT, mul_comm]


open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
/-- C4: one-step weight/Q error (Jin et al. Lemma B.4), deterministic given the concentration
bound and nonnegativity of the next-step value estimate -/
theorem c4_lsvi_q_error {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A]
    [LinearOrder A] [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H : ℕ) (hd : 1 ≤ d)
    (hH : 1 ≤ H) (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d))
    (hM : IsLinearMDP M H d φ) (b B : ℝ) (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ)
    (hh : h ∈ Finset.Icc 1 H)
    (hV0 : ∀ y, 0 ≤ lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y)
    (hconc : Real.sqrt
              ((∑ τ ∈ Finset.Ico 1 k,
                  (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) (xs τ (h + 1)) -
                    ∫ y, lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y
                      ∂(M.P h (xs τ h, as τ h))) • WithLp.ofLp (φ (xs τ h) (as τ h))) ⬝ᵥ
                ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ
                  (∑ τ ∈ Finset.Ico 1 k,
                  (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) (xs τ (h + 1)) -
                    ∫ y, lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y
                      ∂(M.P h (xs τ h, as τ h))) • WithLp.ofLp (φ (xs τ h) (as τ h))))) ≤ B) :
    ∀ x a, |inner ℝ (φ x a) (lsviW φ M.r 1 (fun _ => b) H xs as k h) -
        (M.r h x a + ∫ y, lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y ∂(M.P h (x, a)))|
      ≤ (B + 2 * H * Real.sqrt d) *
          Real.sqrt (WithLp.ofLp (φ x a) ⬝ᵥ ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ x a))) := by
  intro x a
  have hh' := Finset.mem_Icc.mp hh
  have hpd := c4_gram_pd φ xs as k h
  have hdet := e5_det_unit hpd
  have hVm := c4_lsviV_meas H M.r φ hM.2.1 1 (fun _ => b) xs as k (h + 1)
  have hVb : ∀ y, |lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y| ≤ (H : ℝ) := fun y => by
    rw [abs_of_nonneg (hV0 y)]; exact c4_lsviV_le _ _ _ _ _ _ _ _ _ _
  obtain ⟨⟨θ, hθn, hr⟩, hint⟩ := c0_linear_integral d H M φ hM h hh
  obtain ⟨ν, hνn, hν⟩ := hint _ (H : ℝ) (Nat.cast_nonneg _) hVm hVb
  have hin : ∀ (u w : EuclideanSpace ℝ (Fin d)),
      inner ℝ u w = WithLp.ofLp u ⬝ᵥ WithLp.ofLp w := by
    intro u w; rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
  have hW : lsviW φ M.r 1 (fun _ => b) H xs as k h = WithLp.toLp 2 ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ
      ∑ τ ∈ Finset.Ico 1 k, (M.r h (xs τ h) (as τ h) +
        lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) (xs τ (h + 1))) •
          WithLp.ofLp (φ (xs τ h) (as τ h))) := by
    rw [lsviW, if_pos hh', ridgeW]
  have h1 : ∀ τ, M.r h (xs τ h) (as τ h) +
      lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) (xs τ (h + 1)) =
      WithLp.ofLp (φ (xs τ h) (as τ h)) ⬝ᵥ (WithLp.ofLp θ + WithLp.ofLp ν) +
        (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) (xs τ (h + 1)) -
          ∫ y, lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y ∂(M.P h (xs τ h, as τ h))) := by
    intro τ
    rw [hr, hν, hin, hin, dotProduct_add]
    ring
  have h2 : LinearMDPRL.Linear.gram φ 1 xs as k h *ᵥ (WithLp.ofLp θ + WithLp.ofLp ν) =
      (∑ τ ∈ Finset.Ico 1 k, (WithLp.ofLp (φ (xs τ h) (as τ h)) ⬝ᵥ
        (WithLp.ofLp θ + WithLp.ofLp ν)) • WithLp.ofLp (φ (xs τ h) (as τ h))) +
        (WithLp.ofLp θ + WithLp.ofLp ν) := by
    rw [LinearMDPRL.Linear.gram, add_mulVec, sum_mulVec, one_smul, one_mulVec]
    congr 1
    exact Finset.sum_congr rfl fun τ _ => e5_vecMulVec_mulVec _ _
  have hsum : ∑ τ ∈ Finset.Ico 1 k, (M.r h (xs τ h) (as τ h) +
        lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) (xs τ (h + 1))) •
          WithLp.ofLp (φ (xs τ h) (as τ h)) =
      (LinearMDPRL.Linear.gram φ 1 xs as k h *ᵥ (WithLp.ofLp θ + WithLp.ofLp ν) - (WithLp.ofLp θ + WithLp.ofLp ν)) +
      ∑ τ ∈ Finset.Ico 1 k,
        (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) (xs τ (h + 1)) -
          ∫ y, lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y ∂(M.P h (xs τ h, as τ h))) •
            WithLp.ofLp (φ (xs τ h) (as τ h)) := by
    simp_rw [h1, add_smul, Finset.sum_add_distrib]
    rw [h2]
    abel
  have hw : WithLp.ofLp (lsviW φ M.r 1 (fun _ => b) H xs as k h) =
      (WithLp.ofLp θ + WithLp.ofLp ν) - (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ (WithLp.ofLp θ + WithLp.ofLp ν) +
      (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ ∑ τ ∈ Finset.Ico 1 k,
        (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) (xs τ (h + 1)) -
          ∫ y, lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y ∂(M.P h (xs τ h, as τ h))) •
            WithLp.ofLp (φ (xs τ h) (as τ h)) := by
    rw [hW, hsum, WithLp.ofLp_toLp, mulVec_add, mulVec_sub, e5_inv_mulVec hdet]
  have hdiff : inner ℝ (φ x a) (lsviW φ M.r 1 (fun _ => b) H xs as k h) -
      (M.r h x a + ∫ y, lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y ∂(M.P h (x, a))) =
      -(WithLp.ofLp (φ x a) ⬝ᵥ (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ (WithLp.ofLp θ + WithLp.ofLp ν)) +
      WithLp.ofLp (φ x a) ⬝ᵥ (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ ∑ τ ∈ Finset.Ico 1 k,
        (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) (xs τ (h + 1)) -
          ∫ y, lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y ∂(M.P h (xs τ h, as τ h))) •
            WithLp.ofLp (φ (xs τ h) (as τ h)) := by
    rw [hin, hw, hr, hν, hin, hin, dotProduct_add, dotProduct_sub, dotProduct_add]
    ring
  rw [hdiff]
  -- abbreviations for the bound
  have hipsd := hpd.inv.posSemidef
  have hq0 : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ v := fun v => by
    have := hipsd.dotProduct_mulVec_nonneg v; rwa [star_trivial] at this
  have hb1 := c4_abs_cs _ _ _ (hq0 _) (hq0 _)
    (e5_cs_psd hipsd (WithLp.ofLp (φ x a)) (WithLp.ofLp θ + WithLp.ofLp ν))
  have hb2 := c4_abs_cs _ _ _ (hq0 _) (hq0 _)
    (e5_cs_psd hipsd (WithLp.ofLp (φ x a)) (∑ τ ∈ Finset.Ico 1 k,
        (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) (xs τ (h + 1)) -
          ∫ y, lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y ∂(M.P h (xs τ h, as τ h))) •
            WithLp.ofLp (φ (xs τ h) (as τ h))))
  have hGn : Real.sqrt ((WithLp.ofLp θ + WithLp.ofLp ν) ⬝ᵥ (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ
      (WithLp.ofLp θ + WithLp.ofLp ν)) ≤ (1 + H) * Real.sqrt d := by
    have hib := e5_inv_bound hpd one_pos (c4_gram_low φ xs as k h) (WithLp.ofLp θ + WithLp.ofLp ν)
    rw [div_one] at hib
    have hnorm : (WithLp.ofLp θ + WithLp.ofLp ν) ⬝ᵥ (WithLp.ofLp θ + WithLp.ofLp ν) =
        ‖θ + ν‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hin, WithLp.ofLp_add]
    calc _ ≤ Real.sqrt (‖θ + ν‖ ^ 2) := Real.sqrt_le_sqrt (hnorm ▸ hib)
      _ = ‖θ + ν‖ := Real.sqrt_sq (norm_nonneg _)
      _ ≤ ‖θ‖ + ‖ν‖ := norm_add_le _ _
      _ ≤ Real.sqrt d + H * Real.sqrt d := add_le_add hθn hνn
      _ = (1 + H) * Real.sqrt d := by ring
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hsd := Real.sqrt_nonneg (d : ℝ)
  have hsp := Real.sqrt_nonneg (WithLp.ofLp (φ x a) ⬝ᵥ (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ
    WithLp.ofLp (φ x a))
  calc _ ≤ |WithLp.ofLp (φ x a) ⬝ᵥ (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ (WithLp.ofLp θ + WithLp.ofLp ν)| +
        |WithLp.ofLp (φ x a) ⬝ᵥ (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ ∑ τ ∈ Finset.Ico 1 k,
        (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) (xs τ (h + 1)) -
          ∫ y, lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y ∂(M.P h (xs τ h, as τ h))) •
            WithLp.ofLp (φ (xs τ h) (as τ h))| := by
        rw [← abs_neg (WithLp.ofLp (φ x a) ⬝ᵥ _)]
        exact abs_add_le _ _
    _ ≤ Real.sqrt (WithLp.ofLp (φ x a) ⬝ᵥ (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ x a)) *
          ((1 + H) * Real.sqrt d) +
        Real.sqrt (WithLp.ofLp (φ x a) ⬝ᵥ (LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ x a)) * B := by
        gcongr
        · exact hb1.trans (mul_le_mul_of_nonneg_left hGn hsp)
        · exact hb2.trans (mul_le_mul_of_nonneg_left hconc hsp)
    _ ≤ _ := by
        have : (1 + (H : ℝ)) * Real.sqrt d ≤ 2 * H * Real.sqrt d := by nlinarith
        nlinarith


open MeasureTheory ProbabilityTheory in
lemma c5_policy_comp {S A : Type*} [MeasurableSpace S] [Fintype A] (π : S → ℕ → A) (k : ℕ)
    (hπ : ∀ a, MeasurableSet {x | π x k = a}) (F : S → A → ℝ)
    (hF : ∀ a, Measurable (fun x => F x a)) : Measurable (fun x => F x (π x k)) := by
  classical
  have h : (fun x => F x (π x k)) =
      fun x => ∑ a : A, Set.indicator {x | π x k = a} (fun x => F x a) x := by
    funext x
    rw [Finset.sum_eq_single (π x k)]
    · simp [Set.indicator_apply]
    · intro b _ hb
      simp [Set.indicator_apply, Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h]
  exact Finset.measurable_sum _ fun a _ => (hF a).indicator (hπ a)


open MeasureTheory ProbabilityTheory in
lemma c5_int_bounds {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    {f : S → ℝ} (hf : Measurable f) {B : ℝ} (hb : ∀ y, f y ∈ Set.Icc 0 B) :
    ∫ y, f y ∂ν ∈ Set.Icc 0 B := by
  have hint : Integrable f ν :=
    Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb y).1]; exact (hb y).2)
  constructor
  · exact integral_nonneg fun y => (hb y).1
  · calc ∫ y, f y ∂ν ≤ ∫ _y, B ∂ν := integral_mono hint (integrable_const B) fun y => (hb y).2
      _ = B := by simp


open MeasureTheory ProbabilityTheory in
lemma c5_kint_meas {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (P : Kernel (S × A) S) {f : S → ℝ} (hf : Measurable f) (a : A) :
    Measurable (fun x => ∫ y, f y ∂(P (x, a))) :=
  (hf.stronglyMeasurable.integral_kernel (κ := P)).measurable.comp
    (measurable_id.prodMk measurable_const)


open MeasureTheory ProbabilityTheory LinearMDPRL.Linear in
lemma c5_opt_aux {S A : Type*} [MeasurableSpace S] [Fintype A] [Nonempty A] [MeasurableSpace A]
    (H : ℕ) (M : EpisodicMDP S A) (n : ℕ) :
    Measurable (optRem M H n) ∧ ∀ x, optRem M H n x ∈ Set.Icc (0 : ℝ) n := by
  induction n with
  | zero =>
    refine ⟨?_, fun x => ?_⟩
    · simp only [optRem]; exact measurable_const
    · simp [optRem]
  | succ n ih =>
    obtain ⟨hm, hb⟩ := ih
    haveI := M.isMarkov (H - n)
    have hfun : optRem M H (n + 1) = Finset.univ.sup' Finset.univ_nonempty
        (fun a x => M.r (H - n) x a + ∫ y, optRem M H n y ∂(M.P (H - n) (x, a))) := by
      funext x; simp only [optRem, Finset.sup'_apply]
    refine ⟨?_, fun x => ?_⟩
    · rw [hfun]
      exact Finset.measurable_sup' _ fun a _ =>
        (M.r_meas (H - n) a).add (c5_kint_meas (M.P (H - n)) hm a)
    · have hel : ∀ a, M.r (H - n) x a + ∫ y, optRem M H n y ∂(M.P (H - n) (x, a)) ∈
          Set.Icc (0 : ℝ) ((n + 1 : ℕ) : ℝ) := by
        intro a
        have h1 := M.r_mem (H - n) x a
        have h2 := c5_int_bounds (M.P (H - n) (x, a)) hm hb
        push_cast
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      simp only [optRem]
      constructor
      · obtain ⟨a⟩ := (inferInstance : Nonempty A)
        exact le_trans (hel a).1 (Finset.le_sup' (fun a =>
          M.r (H - n) x a + ∫ y, optRem M H n y ∂(M.P (H - n) (x, a))) (Finset.mem_univ a))
      · exact Finset.sup'_le _ _ fun a _ => (hel a).2


open MeasureTheory ProbabilityTheory LinearMDPRL.Linear in
lemma c5_val_aux {S A : Type*} [MeasurableSpace S] [Fintype A] [MeasurableSpace A]
    (H : ℕ) (M : EpisodicMDP S A) (π : Policy S A) (hπ : IsMeasurablePolicy π) (n : ℕ) :
    Measurable (valueRem M H π n) ∧ ∀ x, valueRem M H π n x ∈ Set.Icc (0 : ℝ) n := by
  induction n with
  | zero =>
    refine ⟨?_, fun x => ?_⟩
    · simp only [valueRem]; exact measurable_const
    · simp [valueRem]
  | succ n ih =>
    obtain ⟨hm, hb⟩ := ih
    haveI := M.isMarkov (H - n)
    refine ⟨?_, fun x => ?_⟩
    · simp only [valueRem]
      exact (c5_policy_comp π (H - n) (hπ (H - n)) (M.r (H - n)) (M.r_meas (H - n))).add
        (c5_policy_comp π (H - n) (hπ (H - n))
          (fun x a => ∫ y, valueRem M H π n y ∂(M.P (H - n) (x, a)))
          (fun a => c5_kint_meas (M.P (H - n)) hm a))
    · have h1 := M.r_mem (H - n) x (π x (H - n))
      have h2 := c5_int_bounds (M.P (H - n) (x, π x (H - n))) hm hb
      simp only [valueRem]
      push_cast
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]


open MeasureTheory ProbabilityTheory LinearMDPRL.Linear in
lemma c5_cast (H h : ℕ) (hh1 : 1 ≤ h) (hh : h ≤ H) :
    (((H + 1 - h : ℕ)) : ℝ) = (H : ℝ) + 1 - h := by
  rw [Nat.cast_sub (by omega)]; push_cast; ring


open MeasureTheory ProbabilityTheory LinearMDPRL.Linear in
/-- C5: measurability and range of the value functions -/
theorem c5_values {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A]
    [MeasurableSpace A] (H : ℕ) (M : EpisodicMDP S A) :
    (∀ h, 1 ≤ h → h ≤ H + 1 → Measurable (Vstar M H h) ∧
        ∀ x, Vstar M H h x ∈ Set.Icc (0 : ℝ) ((H : ℝ) + 1 - h)) ∧
    ∀ π : Policy S A, IsMeasurablePolicy π →
      ∀ h, 1 ≤ h → h ≤ H + 1 → Measurable (V M H π h) ∧
        ∀ x, V M H π h x ∈ Set.Icc (0 : ℝ) ((H : ℝ) + 1 - h) := by
  refine ⟨fun h h1 h2 => ?_, fun π hπ h h1 h2 => ?_⟩
  · by_cases hh : h ≤ H
    · obtain ⟨hm, hb⟩ := c5_opt_aux H M (H + 1 - h)
      have heq : Vstar M H h = optRem M H (H + 1 - h) := by
        funext x; simp [Vstar, h1, hh]
      rw [heq, ← c5_cast H h h1 hh]
      exact ⟨hm, hb⟩
    · have hH : h = H + 1 := by omega
      have heq : Vstar M H h = fun _ => 0 := by
        funext x; simp [Vstar]; omega
      rw [heq]
      refine ⟨measurable_const, fun x => ?_⟩
      subst hH; push_cast; simp
  · by_cases hh : h ≤ H
    · obtain ⟨hm, hb⟩ := c5_val_aux H M π hπ (H + 1 - h)
      have heq : V M H π h = valueRem M H π (H + 1 - h) := by
        funext x; simp [V, h1, hh]
      rw [heq, ← c5_cast H h h1 hh]
      exact ⟨hm, hb⟩
    · have hH : h = H + 1 := by omega
      have heq : V M H π h = fun _ => 0 := by
        funext x; simp [V]; omega
      rw [heq]
      refine ⟨measurable_const, fun x => ?_⟩
      subst hH; push_cast; simp


open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
/-- C5b: the greedy policy of an LSVI-UCB run is measurable -/
theorem c5b_greedy_measurable {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A]
    [LinearOrder A] [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H : ℕ)
    (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d))
    (hφ : ∀ a, Measurable (fun x => φ x a)) (lam : ℝ) (β : ℕ → ℝ)
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k : ℕ) :
    IsMeasurablePolicy (greedyPolicy φ M.r lam β H xs as k) := by
  intro h a
  exact c5b_greedy_set (fun x b => lsviQ φ M.r lam β H xs as k h x b)
    (fun b => c5b_lsviQ_meas H M.r φ hφ lam β xs as k h b) a


open MeasureTheory ProbabilityTheory in
lemma c6_hoeff {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    {h : S → ℝ} (hh : Measurable h) {c : ℝ} (hc : 0 < c) (hb : ∀ y, |h y| ≤ c) (l : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (l * ((∫ z, h z ∂ν) - h y))) ∂ν ≤
      ENNReal.ofReal (Real.exp (c ^ 2 * l ^ 2 / 2)) := by
  have hmem : ∀ y, -h y ∈ Set.Icc (-c) c := fun y => by
    have := abs_le.mp (hb y); constructor <;> linarith [this.1, this.2]
  have hs := hasSubgaussianMGF_of_mem_Icc (μ := ν) (X := fun y => -h y) hh.neg.aemeasurable
    (ae_of_all _ hmem)
  have key : ∀ y, (∫ z, h z ∂ν) - h y = -h y - ∫ z, -h z ∂ν := by
    intro y; rw [integral_neg]; ring
  simp_rw [key]
  rw [← ofReal_integral_eq_lintegral_ofReal (hs.integrable_exp_mul l)
    (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  apply ENNReal.ofReal_le_ofReal
  have h1 := hs.mgf_le l
  have hc2 : (((‖c - -c‖₊ / 2) ^ 2 : NNReal) : ℝ) = c ^ 2 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs]
    rw [show c - -c = 2 * c by ring, abs_of_pos (by linarith)]
    norm_num
  rw [hc2] at h1
  exact h1


open MeasureTheory in
lemma c6_meas_comp {Ω S : Type*} {m1 m2 : MeasurableSpace Ω} [mS : MeasurableSpace S]
    (h12 : m1 ≤ m2) (g : Ω → S → ℝ) (hg : Measurable[m1.prod mS] (fun p : Ω × S => g p.1 p.2))
    (X : Ω → S) (hX : Measurable[m2] X) : Measurable[m2] (fun ω => g ω (X ω)) := by
  have h1 : @Measurable Ω (Ω × S) m2 (m1.prod mS) (fun ω => (ω, X ω)) :=
    (measurable_id'' h12).prodMk hX
  exact hg.comp h1


open MeasureTheory ProbabilityTheory in
lemma c6_meas_int {Ω T S : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSpace S]
    (κ : Kernel T S) [IsMarkovKernel κ] {Y : Ω → T} (hY : Measurable Y) (g : Ω → S → ℝ)
    (hg : Measurable (fun p : Ω × S => g p.1 p.2)) :
    Measurable (fun ω => ∫ y, g ω y ∂(κ (Y ω))) := by
  have h := (hg.stronglyMeasurable.integral_kernel_prod_right' (κ := κ.comap Y hY)).measurable
  simpa [Kernel.comap_apply] using h


open MeasureTheory ProbabilityTheory in
lemma c6_meas_F {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] {Z M : Ω → ℝ}
    (g : Ω → S → ℝ) (hZ : Measurable Z) (hM : Measurable M)
    (hg : Measurable (fun p : Ω × S => g p.1 p.2)) (q l : ℝ) :
    Measurable (fun p : Ω × S => ENNReal.ofReal (Z p.1) * ENNReal.ofReal (Real.exp (-q)) *
      ENNReal.ofReal (Real.exp (l * (M p.1 - g p.1 p.2)))) := by
  refine ((ENNReal.measurable_ofReal.comp (hZ.comp measurable_fst)).mul measurable_const).mul
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_))
  exact measurable_const.mul ((hM.comp measurable_fst).sub hg)


open MeasureTheory ProbabilityTheory in
/-- C6: Azuma--Hoeffding for bounded parametric transitions (Markov-kernel form) -/
theorem c6_azuma_markov {Ω T S : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    [MeasurableSpace S] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Filtration ℕ ‹MeasurableSpace Ω›) (κ : Kernel T S) [IsMarkovKernel κ]
    (Y : ℕ → Ω → T) (X : ℕ → Ω → S) (n : ℕ)
    (hY : ∀ t, t < n → Measurable[G t] (Y t)) (hX : ∀ t, t < n → Measurable[G (t + 1)] (X t))
    (htrans : ∀ t, t < n → ∀ (B : Set S), MeasurableSet B →
      μ[(X t ⁻¹' B).indicator (fun _ => (1 : ℝ)) | G t] =ᵐ[μ] fun ω => (κ (Y t ω) B).toReal)
    (g : ℕ → Ω → S → ℝ) (c : ℝ) (hc : 0 < c)
    (hg : ∀ t, t < n →
      Measurable[(G t).prod ‹MeasurableSpace S›] (fun p : Ω × S => g t p.1 p.2))
    (hgb : ∀ t ω y, |g t ω y| ≤ c) (ε : ℝ) (hε : 0 < ε) :
    μ {ω | ε < ∑ t ∈ Finset.range n,
        ((∫ y, g t ω y ∂(κ (Y t ω))) - g t ω (X t ω))}
      ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2) / (2 * n * c ^ 2))) := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : ℕ → Ω → ℝ, M = fun t ω => ∫ y, g t ω y ∂(κ (Y t ω)) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ → Ω → ℝ, D = fun t ω => M t ω - g t ω (X t ω) := ⟨_, rfl⟩
  have hMG : ∀ t, t < n → Measurable[G t] (M t) := fun t ht => by
    rw [hM]; exact @c6_meas_int Ω T S (G t) _ _ κ _ (Y t) (hY t ht) (g t) (hg t ht)
  have hDG : ∀ t j, t < j → j ≤ n → Measurable[G j] (D t) := fun t j htn hjn => by
    rw [hD]
    have ht : t < n := by omega
    have h1 : Measurable[G j] (M t) := (hMG t ht).mono (G.mono htn.le) le_rfl
    have h2 : Measurable[G j] (fun ω => g t ω (X t ω)) :=
      c6_meas_comp (G.mono htn.le) (g t) (hg t ht) (X t) ((hX t ht).mono (G.mono htn) le_rfl)
    exact h1.sub h2
  -- the exponential supermartingale
  have hint : ∀ l : ℝ, ∀ j, j ≤ n → ∫⁻ ω, ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.range j,
      D t ω - j * (c ^ 2 * l ^ 2 / 2))) ∂μ ≤ 1 := by
    intro l j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hjn
      have hj : j < n := hjn
      refine le_trans ?_ (ih hj.le)
      set Zn : Ω → ℝ := fun ω => Real.exp (l * ∑ t ∈ Finset.range j, D t ω
        - j * (c ^ 2 * l ^ 2 / 2)) with hZn
      have hZm : Measurable[G j] Zn := by
        refine Real.measurable_exp.comp ((measurable_const.mul ?_).sub measurable_const)
        exact Finset.measurable_sum _ fun t ht => hDG t j (Finset.mem_range.mp ht) hj.le
      have hF := @c6_meas_F Ω S (G j) _ Zn (M j) (g j) hZm (hMG j hj) (hg j hj) (c ^ 2 * l ^ 2 / 2) l
      have hk := kcl μ (G.le j) κ (Y j) (X j) (hY j hj) ((hX j hj).mono (G.le (j + 1)) le_rfl)
        (htrans j hj)
        (fun ω y => ENNReal.ofReal (Zn ω) * ENNReal.ofReal (Real.exp (-(c ^ 2 * l ^ 2 / 2))) *
          ENNReal.ofReal (Real.exp (l * (M j ω - g j ω y)))) hF
      calc ∫⁻ ω, ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.range (j + 1), D t ω
            - ((j + 1 : ℕ) : ℝ) * (c ^ 2 * l ^ 2 / 2))) ∂μ
          = ∫⁻ ω, ENNReal.ofReal (Zn ω) * ENNReal.ofReal (Real.exp (-(c ^ 2 * l ^ 2 / 2))) *
              ENNReal.ofReal (Real.exp (l * (M j ω - g j ω (X j ω)))) ∂μ := by
            refine lintegral_congr fun ω => ?_
            have hDn : D j ω = M j ω - g j ω (X j ω) := by rw [hD]
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [← Real.exp_add, ← Real.exp_add, Finset.sum_range_succ, hDn]
            congr 1
            push_cast
            ring
        _ = _ := hk
        _ ≤ ∫⁻ ω, ENNReal.ofReal (Zn ω) ∂μ := by
            refine lintegral_mono fun ω => ?_
            beta_reduce
            have hgm : Measurable (g j ω) := by
              have hpm : @Measurable S (Ω × S) _ ((G j).prod ‹MeasurableSpace S›)
                  (fun y => (ω, y)) := measurable_const.prodMk measurable_id
              exact (hg j hj).comp hpm
            have hmy : Measurable (fun y => ENNReal.ofReal (Real.exp (l * (M j ω - g j ω y)))) :=
              ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
                (measurable_const.mul (measurable_const.sub hgm)))
            rw [lintegral_const_mul _ hmy]
            have hb := c6_hoeff (κ (Y j ω)) hgm hc (hgb j ω) l
            have hMn : M j ω = ∫ z, g j ω z ∂(κ (Y j ω)) := by rw [hM]
            rw [hMn]
            calc ENNReal.ofReal (Zn ω) * ENNReal.ofReal (Real.exp (-(c ^ 2 * l ^ 2 / 2))) * _
                ≤ ENNReal.ofReal (Zn ω) * ENNReal.ofReal (Real.exp (-(c ^ 2 * l ^ 2 / 2))) *
                    ENNReal.ofReal (Real.exp (c ^ 2 * l ^ 2 / 2)) := by gcongr
              _ = ENNReal.ofReal (Zn ω) := by
                rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
                simp
  -- Chernoff
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : {ω | ε < ∑ t ∈ Finset.range 0, ((∫ y, g t ω y ∂(κ (Y t ω))) - g t ω (X t ω))} = ∅ := by
      ext ω; simp [not_lt.mpr hε.le]
    rw [this]; simp
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set l : ℝ := ε / (n * c ^ 2) with hl
  have hl0 : 0 < l := by positivity
  set q : ℝ := l * ε - n * (c ^ 2 * l ^ 2 / 2) with hq
  have hZm : Measurable (fun ω => Real.exp (l * ∑ t ∈ Finset.range n, D t ω
      - n * (c ^ 2 * l ^ 2 / 2))) := by
    refine Real.measurable_exp.comp ((measurable_const.mul ?_).sub measurable_const)
    exact Finset.measurable_sum _ fun t ht => (hDG t n (Finset.mem_range.mp ht) le_rfl).mono (G.le n) le_rfl
  have hsub : {ω | ε < ∑ t ∈ Finset.range n, ((∫ y, g t ω y ∂(κ (Y t ω))) - g t ω (X t ω))} ⊆
      {ω | ENNReal.ofReal (Real.exp q) ≤ ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.range n, D t ω
        - n * (c ^ 2 * l ^ 2 / 2)))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hsum : ∑ t ∈ Finset.range n, D t ω =
        ∑ t ∈ Finset.range n, ((∫ y, g t ω y ∂(κ (Y t ω))) - g t ω (X t ω)) := by
      rw [hD, hM]
    rw [hq, hsum]
    nlinarith
  have hne : ENNReal.ofReal (Real.exp q) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  calc _ ≤ _ := measure_mono hsub
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.range n, D t ω
          - n * (c ^ 2 * l ^ 2 / 2))) ∂μ) / ENNReal.ofReal (Real.exp q) :=
        meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp hZm).aemeasurable hne
          ENNReal.ofReal_ne_top
    _ ≤ 1 / ENNReal.ofReal (Real.exp q) := ENNReal.div_le_div_right (hint l n le_rfl) _
    _ = ENNReal.ofReal (Real.exp (-(ε ^ 2) / (2 * n * c ^ 2))) := by
        rw [ENNReal.div_eq_inv_mul, mul_one, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
          ← Real.exp_neg]
        congr 2
        rw [hq, hl]
        field_simp
        ring



lemma c3_logP_le (X Y : ℝ) (hX : 1 ≤ X) (hY : 0 < Y) (hYX : Y ≤ 64 * X ^ 2) :
    Real.log Y ≤ 5 * (Real.log X + 1) := by
  have h2 := Real.log_two_lt_d9
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have : Real.log Y ≤ Real.log (64 * X ^ 2) := Real.log_le_log hY hYX
  have h64 : Real.log (64 * X ^ 2) = 6 * Real.log 2 + 2 * Real.log X := by
    have : (64 : ℝ) = 2 ^ 6 := by norm_num
    rw [Real.log_mul (by norm_num) (by positivity), this, Real.log_pow, Real.log_pow]
    norm_num
  rw [h64] at this
  linarith

set_option maxHeartbeats 800000 in
lemma c3_num (d K H : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (hH : 1 ≤ H) (b : ℝ) (hb : 0 ≤ b)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (det q : ℝ) (hdet0 : 0 < det)
    (hdet : det ≤ (1 + (K : ℝ)) ^ d)
    (hq : 5 * d * H * Real.sqrt (Real.log (d * K * H * (1 + b) / δ) + 1) - 1 < Real.sqrt q) :
    (H : ℝ) ^ 2 / 2 * Real.log (Real.sqrt det /
        (δ / (K * H * ((2 * ((K : ℝ) * (1 + H)) / (1 / (4 * (d : ℝ) * K)) + 1) ^ d *
          (2 * 1 / ((1 / (4 * (K : ℝ) * d * (1 + b))) ^ 2) + 1) ^ (d * d))))) < q := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hd0 : (0 : ℝ) < d := by linarith
  have hK0 : (0 : ℝ) < K := by linarith
  have hH0 : (0 : ℝ) < H := by linarith
  have hb1 : (1 : ℝ) ≤ 1 + b := by linarith
  set X : ℝ := d * K * H * (1 + b) / δ with hXdef
  have hX1 : 1 ≤ X := by
    rw [hXdef, le_div_iff₀ hδ]
    have : (1 : ℝ) ≤ d * K * H * (1 + b) := by
      have h1 : (1 : ℝ) ≤ d * K := by nlinarith
      have h2 : (1 : ℝ) ≤ d * K * H := by nlinarith
      nlinarith
    linarith
  set Λ : ℝ := Real.log X + 1 with hΛ
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hΛ1 : 1 ≤ Λ := by linarith
  have hX0 : 0 < X := by linarith
  -- B0
  set B0 : ℝ := 5 * d * H * Real.sqrt Λ with hB0
  have hsq1 : 1 ≤ Real.sqrt Λ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hΛ1
  have hB05 : 5 ≤ B0 := by
    have : (1 : ℝ) ≤ d * H := by nlinarith
    nlinarith
  have hhalf : B0 / 2 < Real.sqrt q := by linarith
  have hq2 : (B0 / 2) ^ 2 < q := (Real.lt_sqrt (by linarith)).mp hhalf
  have hB02 : B0 ^ 2 = 25 * (d : ℝ) ^ 2 * (H : ℝ) ^ 2 * Λ := by
    rw [hB0, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith)]; ring
  -- the logarithm
  set P : ℝ := 2 * ((K : ℝ) * (1 + H)) / (1 / (4 * (d : ℝ) * K)) + 1 with hP
  set Q : ℝ := 2 * 1 / ((1 / (4 * (K : ℝ) * d * (1 + b))) ^ 2) + 1 with hQ
  have hPe : P = 8 * d * K ^ 2 * (1 + H) + 1 := by
    rw [hP]; field_simp; ring
  have hQe : Q = 32 * K ^ 2 * d ^ 2 * (1 + b) ^ 2 + 1 := by
    rw [hQ]; field_simp; ring
  have hP0 : 0 < P := by rw [hPe]; positivity
  have hQ0 : 0 < Q := by rw [hQe]; positivity
  have hKX : (K : ℝ) ≤ X := by
    rw [hXdef, le_div_iff₀ hδ]
    have h1 : (1 : ℝ) ≤ d * H * (1 + b) := by
      have : (1 : ℝ) ≤ d * H := by nlinarith
      nlinarith
    have : (K : ℝ) * 1 ≤ K * (d * H * (1 + b)) := by gcongr
    nlinarith
  have hdKH : (d : ℝ) * K * H ≤ X := by
    rw [hXdef, le_div_iff₀ hδ]
    have : (d : ℝ) * K * H * δ ≤ d * K * H * 1 := by gcongr
    have h2 : (d : ℝ) * K * H * 1 ≤ d * K * H * (1 + b) := by gcongr
    linarith
  have hX2 : 1 ≤ X ^ 2 := one_le_pow₀ hX1
  have hPX : P ≤ 64 * X ^ 2 := by
    rw [hPe]
    have h1 : (d : ℝ) * K * H ≤ X := hdKH
    have h2 : (K : ℝ) ≤ X := hKX
    have h3 : (d : ℝ) * K ^ 2 * H ≤ X ^ 2 := by
      calc (d : ℝ) * K ^ 2 * H = (d * K * H) * K := by ring
        _ ≤ X * X := mul_le_mul h1 h2 hK0.le hX0.le
        _ = X ^ 2 := by ring
    have e1 : (d : ℝ) * K ^ 2 ≤ d * K ^ 2 * H := le_mul_of_one_le_right (by positivity) hH1
    have e2 : (d : ℝ) * K ^ 2 * (1 + H) = d * K ^ 2 + d * K ^ 2 * H := by ring
    have e3 : 8 * (d : ℝ) * K ^ 2 * (1 + H) = 8 * ((d : ℝ) * K ^ 2 * (1 + H)) := by ring
    rw [e3, e2]
    linarith
  have hQX : Q ≤ 64 * X ^ 2 := by
    rw [hQe]
    have h4 : (K : ℝ) * d * (1 + b) ≤ X := by
      rw [hXdef, le_div_iff₀ hδ]
      have : (K : ℝ) * d * (1 + b) * δ ≤ K * d * (1 + b) * 1 := by gcongr
      have h5 : (K : ℝ) * d * (1 + b) ≤ d * K * H * (1 + b) := by
        have h7 : (K : ℝ) * d ≤ d * K * H := by
          have : (K : ℝ) * d = d * K * 1 := by ring
          rw [this]; gcongr
        exact mul_le_mul_of_nonneg_right h7 (by linarith)
      linarith
    have h6 : ((K : ℝ) * d * (1 + b)) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
    have e : 32 * (K : ℝ) ^ 2 * d ^ 2 * (1 + b) ^ 2 = 32 * ((K * d * (1 + b)) ^ 2) := by ring
    rw [e]
    linarith
  clear_value P Q
  have hlP := c3_logP_le X P hX1 hP0 hPX
  have hlQ := c3_logP_le X Q hX1 hQ0 hQX
  -- log(1+K)
  have hlK : Real.log (1 + (K : ℝ)) ≤ Λ := by
    have h2 := Real.log_two_lt_d9
    have h3 : (1 + (K : ℝ)) ≤ 2 * X := by linarith
    have hpos : (0 : ℝ) < 1 + K := by positivity
    have h4 := Real.log_le_log hpos h3
    rw [Real.log_mul (by norm_num) hX0.ne'] at h4
    linarith
  have hlKH : Real.log ((K : ℝ) * H / δ) ≤ Λ := by
    have : (K : ℝ) * H / δ ≤ X := by
      rw [hXdef]
      apply div_le_div_of_nonneg_right _ hδ.le
      have : (1 : ℝ) ≤ d * (1 + b) := by nlinarith
      nlinarith [mul_pos hK0 hH0]
    have := Real.log_le_log (by positivity) this
    linarith
  -- assemble
  have hdetlog : Real.log det ≤ d * Λ := by
    have := Real.log_le_log hdet0 hdet
    rw [Real.log_pow] at this
    have h2 : d * Real.log (1 + (K : ℝ)) ≤ d * Λ := by gcongr
    linarith
  have hNr : Real.log (P ^ d * Q ^ (d * d)) = d * Real.log P + ((d : ℝ) * d) * Real.log Q := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hT : Real.log (Real.sqrt det / (δ / (K * H * (P ^ d * Q ^ (d * d))))) =
      Real.log det / 2 + (Real.log ((K : ℝ) * H / δ) + Real.log (P ^ d * Q ^ (d * d))) := by
    have e : Real.sqrt det / (δ / (K * H * (P ^ d * Q ^ (d * d)))) =
        Real.sqrt det * (((K : ℝ) * H / δ) * (P ^ d * Q ^ (d * d))) := by
      field_simp
    rw [e, Real.log_mul (Real.sqrt_pos.mpr hdet0).ne' (by positivity), Real.log_sqrt hdet0.le,
      Real.log_mul (by positivity) (by positivity)]
  have hΛ0 : 0 ≤ Λ := by linarith
  have hdd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hTle : Real.log det / 2 + (Real.log ((K : ℝ) * H / δ) +
      (d * Real.log P + ((d : ℝ) * d) * Real.log Q)) ≤ 25 / 2 * (d : ℝ) ^ 2 * Λ := by
    have a1 : (d : ℝ) * Real.log P ≤ d * (5 * Λ) := by gcongr
    have a2 : (d : ℝ) * d * Real.log Q ≤ d * d * (5 * Λ) := by gcongr
    have a3 : (d : ℝ) * Λ ≤ d ^ 2 * Λ := mul_le_mul_of_nonneg_right hdd hΛ0
    have a4 : (d : ℝ) * (5 * Λ) ≤ 5 * d ^ 2 * Λ := by nlinarith
    have a5 : Λ ≤ d ^ 2 * Λ := by nlinarith
    have a6 : (d : ℝ) * d * (5 * Λ) = 5 * d ^ 2 * Λ := by ring
    linarith
  have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
  rw [hT, hNr]
  have hfin : (H : ℝ) ^ 2 / 2 * (Real.log det / 2 + (Real.log ((K : ℝ) * H / δ) +
        (d * Real.log P + ((d : ℝ) * d) * Real.log Q)))
      ≤ (H : ℝ) ^ 2 / 2 * (25 / 2 * (d : ℝ) ^ 2 * Λ) :=
    mul_le_mul_of_nonneg_left hTle (by positivity)
  have hfin2 : (H : ℝ) ^ 2 / 2 * (25 / 2 * (d : ℝ) ^ 2 * Λ) = (B0 / 2) ^ 2 := by
    rw [div_pow, hB02]; ring
  linarith


open Matrix LinearMDPRL.Linear in
lemma c3_det_gram {S A : Type*} {d : ℕ} (hd : 1 ≤ d) (φ : S → A → EuclideanSpace ℝ (Fin d))
    (hφ : ∀ x a, ‖φ x a‖ ≤ 1) (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h K : ℕ) (hkK : k ≤ K) :
    (LinearMDPRL.Linear.gram φ 1 xs as k h).det ≤ (1 + (K : ℝ)) ^ d := by
  have hpd := c4_gram_pd φ xs as k h
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  refine (e5_det_le_trace hd hpd).trans ?_
  have hdot : ∀ τ, WithLp.ofLp (φ (xs τ h) (as τ h)) ⬝ᵥ WithLp.ofLp (φ (xs τ h) (as τ h)) ≤ 1 := by
    intro τ
    have h1 := hφ (xs τ h) (as τ h)
    have h2 : WithLp.ofLp (φ (xs τ h) (as τ h)) ⬝ᵥ WithLp.ofLp (φ (xs τ h) (as τ h)) =
        ‖φ (xs τ h) (as τ h)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [dotProduct, sq]
    rw [h2]
    nlinarith [norm_nonneg (φ (xs τ h) (as τ h))]
  have htr : (LinearMDPRL.Linear.gram φ 1 xs as k h).trace ≤ d + K := by
    have e : (LinearMDPRL.Linear.gram φ 1 xs as k h).trace =
        ∑ τ ∈ Finset.Ico 1 k, (WithLp.ofLp (φ (xs τ h) (as τ h)) ⬝ᵥ
          WithLp.ofLp (φ (xs τ h) (as τ h))) + d := by
      unfold LinearMDPRL.Linear.gram
      rw [Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_one]
      simp [Matrix.trace, vecMulVec_apply, dotProduct]
    rw [e]
    have h1 : ∑ τ ∈ Finset.Ico 1 k, (WithLp.ofLp (φ (xs τ h) (as τ h)) ⬝ᵥ
          WithLp.ofLp (φ (xs τ h) (as τ h))) ≤ ∑ τ ∈ Finset.Ico 1 k, (1 : ℝ) :=
      Finset.sum_le_sum fun τ _ => hdot τ
    have h2 : ∑ τ ∈ Finset.Ico 1 k, (1 : ℝ) ≤ K := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
      have : k - 1 ≤ K := by omega
      exact_mod_cast this
    linarith
  have h0 : 0 ≤ (LinearMDPRL.Linear.gram φ 1 xs as k h).trace / d :=
    div_nonneg hpd.posSemidef.trace_nonneg hd0.le
  have h1 : (LinearMDPRL.Linear.gram φ 1 xs as k h).trace / d ≤ 1 + K := by
    rw [div_le_iff₀ hd0]
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [mul_le_mul_of_nonneg_left hd1 hK0]
  exact pow_le_pow_left₀ h0 h1 d

open Matrix LinearMDPRL.Linear MeasureTheory in
/-- The centered sum `Σ_τ (f(x^τ_{h+1}) - P_h f(x^τ_h, a^τ_h)) φ(x^τ_h, a^τ_h)`. -/
noncomputable def c3Sv {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] {d : ℕ}
    (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)) (xs : ℕ → ℕ → S)
    (as : ℕ → ℕ → A) (k h : ℕ) (f : S → ℝ) : Fin d → ℝ :=
  ∑ τ ∈ Finset.Ico 1 k, (f (xs τ (h + 1)) - ∫ y, f y ∂(M.P h (xs τ h, as τ h))) •
    WithLp.ofLp (φ (xs τ h) (as τ h))

open Matrix LinearMDPRL.Linear MeasureTheory in
/-- The self-normalized quantity `S_fᵀ Λ⁻¹ S_f`. -/
noncomputable def c3Qf {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] {d : ℕ}
    (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)) (xs : ℕ → ℕ → S)
    (as : ℕ → ℕ → A) (k h : ℕ) (f : S → ℝ) : ℝ :=
  c3Sv M φ xs as k h f ⬝ᵥ ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ c3Sv M φ xs as k h f)

open Matrix LinearMDPRL.Linear MeasureTheory in
lemma c3_cover {S A : Type} [MeasurableSpace S] [MeasurableSpace A] [Fintype A] [Nonempty A]
    {d : ℕ} (M : EpisodicMDP S A) (H K : ℕ) (hH : 1 ≤ H) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (hφn : ∀ x a, ‖φ x a‖ ≤ 1)
    (hφm : ∀ a, Measurable fun x => φ x a) (b : ℝ) (hb : 0 ≤ b)
    (Gw : Finset (Fin d → ℝ)) (GA : Finset (Fin d × Fin d → ℝ))
    (hGw : ∀ z : Fin d → ℝ, (∀ i, |z i| ≤ (K : ℝ) * (1 + H)) →
      ∃ g ∈ Gw, ∀ i, |z i - g i| ≤ 1 / (4 * (d : ℝ) * K))
    (hGA : ∀ z : Fin d × Fin d → ℝ, (∀ i, |z i| ≤ 1) →
      ∃ g ∈ GA, ∀ i, |z i - g i| ≤ (1 / (4 * (K : ℝ) * d * (1 + b))) ^ 2)
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ K)
    (hh1 : 1 ≤ h) (hhH : h + 1 ≤ H)
    (hpos : ∀ h' ∈ Finset.Icc (h + 1) (H + 1), ∀ y,
      0 ≤ lsviV φ M.r 1 (fun _ => b) H xs as k h' y) :
    ∃ w ∈ Gw, ∃ g ∈ GA,
      Real.sqrt (c3Qf M φ xs as k h (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1))) ≤
        Real.sqrt (c3Qf M φ xs as k h
          (c3F φ H b w (Matrix.of fun i j => g (i, j)))) + 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hφe : ∀ y a i, |WithLp.ofLp (φ y a) i| ≤ 1 := by
    intro y a i
    have := PiLp.norm_apply_le (φ y a) i
    rw [Real.norm_eq_abs] at this
    exact this.trans (hφn y a)
  have hV1 : ∀ y, 0 ≤ lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y :=
    hpos (h + 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hV2 : ∀ y, lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1 + 1) y ∈ Set.Icc (0 : ℝ) H :=
    fun y => ⟨hpos (h + 1 + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) y,
      c4_lsviV_le φ M.r 1 (fun _ => b) H xs as k (h + 1 + 1) y⟩
  have hEq := c3_lsviV_eq φ M.r (fun _ => b) H xs as k (h + 1) (by omega) hhH hV1
  have hwb := c3_w_bound φ hφn M.r M.r_mem (fun _ => b) H xs as k (h + 1) (by omega) hhH hV2
  obtain ⟨w, hw, hwc⟩ := hGw (WithLp.ofLp (lsviW φ M.r 1 (fun _ => b) H xs as k (h + 1)))
    (fun i => (hwb i).trans (by
      have : (k : ℝ) ≤ K := by exact_mod_cast hkK
      have h2 : (0 : ℝ) ≤ 1 + H := by positivity
      exact mul_le_mul_of_nonneg_right this h2))
  obtain ⟨g, hg, hgc⟩ := hGA (fun p => ((LinearMDPRL.Linear.gram φ 1 xs as k (h + 1))⁻¹) p.1 p.2)
    (fun p => c3_inv_entry φ xs as k (h + 1) p.1 p.2)
  refine ⟨w, hw, g, hg, ?_⟩
  set f := c3F φ H b w (Matrix.of fun i j => g (i, j)) with hf
  have hVf : ∀ y, |lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y - f y| ≤ 1 / (2 * K) := by
    intro y
    rw [hEq]
    refine (c3F_diff φ hφe H b hb _ w _ _ y).trans ?_
    have s1 : ∑ i, |WithLp.ofLp (lsviW φ M.r 1 (fun _ => b) H xs as k (h + 1)) i - w i| ≤
        d * (1 / (4 * (d : ℝ) * K)) := by
      calc _ ≤ ∑ _i : Fin d, 1 / (4 * (d : ℝ) * K) := Finset.sum_le_sum fun i _ => hwc i
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have s2 : ∑ i, ∑ j, |((LinearMDPRL.Linear.gram φ 1 xs as k (h + 1))⁻¹) i j - (Matrix.of fun i j => g (i, j)) i j| ≤
        d * d * (1 / (4 * (K : ℝ) * d * (1 + b))) ^ 2 := by
      calc _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, (1 / (4 * (K : ℝ) * d * (1 + b))) ^ 2 :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hgc (i, j)
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have s3 : Real.sqrt (∑ i, ∑ j, |((LinearMDPRL.Linear.gram φ 1 xs as k (h + 1))⁻¹) i j -
          (Matrix.of fun i j => g (i, j)) i j|) ≤ d * (1 / (4 * (K : ℝ) * d * (1 + b))) := by
      refine (Real.sqrt_le_sqrt s2).trans ?_
      rw [show (d : ℝ) * d * (1 / (4 * (K : ℝ) * d * (1 + b))) ^ 2 =
        (d * (1 / (4 * (K : ℝ) * d * (1 + b)))) ^ 2 by ring]
      exact (Real.sqrt_sq (by positivity)).le
    have e1 : (d : ℝ) * (1 / (4 * (d : ℝ) * K)) = 1 / (4 * K) := by field_simp
    have e2 : (d : ℝ) * (1 / (4 * (K : ℝ) * d * (1 + b))) = 1 / (4 * K * (1 + b)) := by
      field_simp
    have e3 : b * (1 / (4 * (K : ℝ) * (1 + b))) ≤ 1 / (4 * K) := by
      rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have e4 : b * Real.sqrt (∑ i, ∑ j, |((LinearMDPRL.Linear.gram φ 1 xs as k (h + 1))⁻¹) i j -
          (Matrix.of fun i j => g (i, j)) i j|) ≤ 1 / (4 * K) := by
      calc _ ≤ b * (1 / (4 * K * (1 + b))) := by
            apply mul_le_mul_of_nonneg_left _ hb
            rw [← e2]; exact s3
        _ ≤ 1 / (4 * K) := by
            have : (1 / (4 * (K : ℝ) * (1 + b))) = 1 / (4 * K * (1 + b)) := rfl
            rw [← this]; exact e3
    have e5 : (1 : ℝ) / (2 * K) = 1 / (4 * K) + 1 / (4 * K) := by field_simp; ring
    rw [e5]
    rw [e1] at s1
    linarith
  have hVm := c4_lsviV_meas H M.r φ hφm 1 (fun _ => b) xs as k (h + 1)
  have hfm : Measurable f := c3F_meas φ hφm H b w _
  have hper := c3_perturb M φ hφn xs as k h (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1)) f hVm hfm
    (H : ℝ) (1 / (2 * K)) (by positivity)
    (fun y => by
      rw [abs_of_nonneg (hV1 y)]
      exact c4_lsviV_le φ M.r 1 (fun _ => b) H xs as k (h + 1) y)
    (fun y => by
      have := c3F_mem φ H b (Nat.cast_nonneg _) w (Matrix.of fun i j => g (i, j)) y
      rw [abs_of_nonneg this.1]; exact this.2)
    hVf
  have hk : 2 * (1 / (2 * (K : ℝ))) * k ≤ 1 := by
    have : (k : ℝ) ≤ K := by exact_mod_cast hkK
    rw [show 2 * (1 / (2 * (K : ℝ))) * k = k / K by field_simp]
    rw [div_le_one hK0]; exact this
  show Real.sqrt (c3Qf M φ xs as k h _) ≤ Real.sqrt (c3Qf M φ xs as k h f) + 1
  unfold c3Qf c3Sv
  linarith


open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
/-- The bad event of the self-normalized concentration (C3). -/
def c3Ev {S A Ω : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A] [Nonempty A]
    {d : ℕ} (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)) (b δ : ℝ) (H K : ℕ)
    (x : ℕ → ℕ → Ω → S) (a : ℕ → ℕ → Ω → A) : Set Ω :=
  {ω | ∃ k ∈ Finset.Icc 1 K, ∃ h ∈ Finset.Icc 1 H,
          (∀ h' ∈ Finset.Icc (h + 1) (H + 1), ∀ y,
            0 ≤ lsviV φ M.r 1 (fun _ => b) H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h' y) ∧
          5 * d * H * Real.sqrt (Real.log (d * K * H * (1 + b) / δ) + 1) <
            Real.sqrt (c3Qf M φ (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h
              (lsviV φ M.r 1 (fun _ => b) H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k (h + 1)))}

open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
theorem c3_main5 {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
    [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H K : ℕ) (hd : 1 ≤ d) (hH : 1 ≤ H)
    (hK : 1 ≤ K) (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d))
    (hM : IsLinearMDP M H d φ) (b : ℝ) (hb : 0 ≤ b) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝓕 : Filtration ℕ mΩ) (x : ℕ → ℕ → Ω → S) (a : ℕ → ℕ → Ω → A)
    (hrun : IsLSVIUCBRun μ 𝓕 M φ 1 (fun _ => b) H K x a) :
    μ (c3Ev M φ b δ H K x a) ≤ ENNReal.ofReal δ := by
  show μ {ω | ∃ k ∈ Finset.Icc 1 K, ∃ h ∈ Finset.Icc 1 H,
          (∀ h' ∈ Finset.Icc (h + 1) (H + 1), ∀ y,
            0 ≤ lsviV φ M.r 1 (fun _ => b) H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h' y) ∧
          5 * d * H * Real.sqrt (Real.log (d * K * H * (1 + b) / δ) + 1) <
            Real.sqrt (c3Qf M φ (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h
              (lsviV φ M.r 1 (fun _ => b) H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k (h + 1)))}
          ≤ ENNReal.ofReal δ
  obtain ⟨hφn, hφm, -⟩ := hM
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  obtain ⟨Gw, hGwc, hGw⟩ := c3_gridD (D := Fin d) ((K : ℝ) * (1 + H)) (1 / (4 * (d : ℝ) * K))
    (by positivity) (by positivity)
  obtain ⟨GA, hGAc, hGA⟩ := c3_gridD (D := Fin d × Fin d) 1
    ((1 / (4 * (K : ℝ) * d * (1 + b))) ^ 2) zero_le_one (by positivity)
  rw [Fintype.card_fin] at hGwc
  rw [Fintype.card_prod, Fintype.card_fin] at hGAc
  set Nr : ℝ := (2 * ((K : ℝ) * (1 + H)) / (1 / (4 * (d : ℝ) * K)) + 1) ^ d *
    (2 * 1 / ((1 / (4 * (K : ℝ) * d * (1 + b))) ^ 2) + 1) ^ (d * d) with hNr
  have hNr0 : 0 < Nr := by rw [hNr]; positivity
  set δ' : ℝ := δ / (K * H * Nr) with hδ'
  have hδ'0 : 0 < δ' := by rw [hδ']; positivity
  set I : Finset ((ℕ × ℕ) × ((Fin d → ℝ) × (Fin d × Fin d → ℝ))) :=
    (Finset.Icc 1 K ×ˢ Finset.Icc 1 H) ×ˢ (Gw ×ˢ GA) with hI
  let Ev : (ℕ × ℕ) × ((Fin d → ℝ) × (Fin d × Fin d → ℝ)) → Set Ω := fun p =>
    {ω | (H : ℝ) ^ 2 / 2 * Real.log (Real.sqrt (LinearMDPRL.Linear.gram φ 1
        (fun τ i => x τ i ω) (fun τ i => a τ i ω) p.1.1 p.1.2).det / δ') <
      c3Qf M φ (fun τ i => x τ i ω) (fun τ i => a τ i ω) p.1.1 p.1.2
        (c3F φ H b p.2.1 (Matrix.of fun i j => p.2.2 (i, j)))}
  have hEv : ∀ p ∈ I, μ (Ev p) ≤ ENNReal.ofReal δ' := by
    rintro ⟨⟨k, h⟩, ⟨w, g⟩⟩ hp
    simp only [hI, Finset.mem_product, Finset.mem_Icc] at hp
    exact c3c_fixed μ 𝓕 M φ hφm (fun _ => b) H K x a hrun k h hp.1.1.1 hp.1.1.2 hp.1.2.1 hp.1.2.2
      (c3F φ H b w (Matrix.of fun i j => g (i, j))) (c3F_meas φ hφm H b w _) H hH0
      (fun y => c3F_mem φ H b (Nat.cast_nonneg _) w _ y) δ' hδ'0
  have hsub : {ω | ∃ k ∈ Finset.Icc 1 K, ∃ h ∈ Finset.Icc 1 H,
          (∀ h' ∈ Finset.Icc (h + 1) (H + 1), ∀ y,
            0 ≤ lsviV φ M.r 1 (fun _ => b) H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h' y) ∧
          5 * d * H * Real.sqrt (Real.log (d * K * H * (1 + b) / δ) + 1) <
            Real.sqrt (c3Qf M φ (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h
              (lsviV φ M.r 1 (fun _ => b) H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k (h + 1)))}
        ⊆ ⋃ p ∈ I, Ev p := by
    intro ω hω
    obtain ⟨k, hk, h, hh, hpos, hlt⟩ := hω
    rw [Finset.mem_Icc] at hk hh
    rcases Nat.lt_or_ge h H with hlt' | hge
    · obtain ⟨w, hw, g, hg, hle⟩ := c3_cover M H K hH hK hd φ hφn hφm b hb Gw GA hGw hGA
        (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h hk.1 hk.2 hh.1 hlt' hpos
      rw [Set.mem_iUnion₂]
      refine ⟨((k, h), (w, g)), ?_, ?_⟩
      · simp only [hI, Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨⟨hk.1, hk.2⟩, ⟨hh.1, hh.2⟩⟩, hw, hg⟩
      · show (H : ℝ) ^ 2 / 2 * Real.log (Real.sqrt (LinearMDPRL.Linear.gram φ 1
            (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h).det / δ') <
          c3Qf M φ (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h
            (c3F φ H b w (Matrix.of fun i j => g (i, j)))
        exact c3_num d K H hd hK hH b hb δ hδ hδ1 _ _
          (c4_gram_pd φ (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h).det_pos
          (c3_det_gram hd φ hφn _ _ k h K hk.2) (by linarith)
    · exfalso
      have hhH : h = H := le_antisymm hh.2 hge
      subst hhH
      have hV0 : lsviV φ M.r 1 (fun _ => b) h (fun τ i => x τ i ω) (fun τ i => a τ i ω) k (h + 1)
          = fun _ => 0 := by
        funext y
        simp [lsviV, lsviQ]
      rw [hV0] at hlt
      have hz : c3Qf M φ (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h (fun _ => (0 : ℝ)) = 0 := by
        simp [c3Qf, c3Sv]
      rw [hz, Real.sqrt_zero] at hlt
      have : 0 ≤ (5 : ℝ) * d * h * Real.sqrt (Real.log (d * K * h * (1 + b) / δ) + 1) := by
        positivity
      linarith
  calc _ ≤ μ (⋃ p ∈ I, Ev p) := measure_mono hsub
    _ ≤ ∑ p ∈ I, μ (Ev p) := measure_biUnion_finset_le I Ev
    _ ≤ ∑ p ∈ I, ENNReal.ofReal δ' := Finset.sum_le_sum hEv
    _ = I.card * ENNReal.ofReal δ' := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal δ := by
      have hcard : (I.card : ℝ) = K * H * ((Gw.card : ℝ) * GA.card) := by
        simp only [hI, Finset.card_product, Nat.card_Icc]
        push_cast
        simp
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have hprod : (Gw.card : ℝ) * GA.card ≤ Nr :=
        mul_le_mul hGwc hGAc (Nat.cast_nonneg _) (by positivity)
      have e : (K : ℝ) * H * ((Gw.card : ℝ) * GA.card) * δ' = δ * (((Gw.card : ℝ) * GA.card) / Nr) := by
        rw [hδ']; field_simp
      rw [hcard, e]
      exact mul_le_of_le_one_right hδ.le ((div_le_one hNr0).mpr hprod)


open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma asm_int {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    {f : S → ℝ} (hf : Measurable f) (B : ℝ) (hb : ∀ y, |f y| ≤ B) : Integrable f ν :=
  Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ fun y => by
    rw [Real.norm_eq_abs]; exact hb y)

open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma asm_lsviQ_eq {S A : Type*} [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (r : ℕ → S → A → ℝ) (β : ℕ → ℝ) (H : ℕ)
    (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A) (k h : ℕ) (h1 : 1 ≤ h) (h2 : h ≤ H) (x : S) (a : A) :
    lsviQ φ r 1 β H xs as k h x a =
      min (inner ℝ (φ x a) (lsviW φ r 1 β H xs as k h) + β k * Real.sqrt (WithLp.ofLp (φ x a) ⬝ᵥ
        ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ x a)))) (H : ℝ) := by
  have hnext : (fun y => Finset.univ.sup' Finset.univ_nonempty
      (fun b => lsviQRem φ r 1 β H xs as k (H - h) y b)) = lsviV φ r 1 β H xs as k (h + 1) := by
    funext y
    unfold lsviV lsviQ
    by_cases hc : h + 1 ≤ H
    · have e : H + 1 - (h + 1) = H - h := by omega
      simp only [e, show 1 ≤ h + 1 by omega, hc, and_self, if_true]
    · have e : H - h = 0 := by omega
      simp only [e, lsviQRem, hc, and_false, if_false]
  have hW : lsviW φ r 1 β H xs as k h =
      ridgeW φ r 1 xs as k h (lsviV φ r 1 β H xs as k (h + 1)) := by
    rw [lsviW, if_pos ⟨h1, h2⟩]
  unfold lsviQ
  rw [if_pos ⟨h1, h2⟩, show H + 1 - h = (H - h) + 1 by omega, lsviQRem,
    show H - (H - h) = h by omega, hnext, hW]

open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma asm_greedy_max {A : Type*} [Fintype A] [Nonempty A] [LinearOrder A] (q : A → ℝ) :
    q (greedy q) = Finset.univ.sup' Finset.univ_nonempty q := by
  have hm := Finset.min'_mem (Finset.univ.filter (fun a => ∀ b, q b ≤ q a)) (by
    obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ q Finset.univ_nonempty
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, fun b => ha b (Finset.mem_univ b)⟩⟩)
  have h2 := (Finset.mem_filter.mp hm).2
  refine le_antisymm (Finset.le_sup' q (Finset.mem_univ _)) (Finset.sup'_le _ _ fun b _ => h2 b)

open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma asm_Vstar_succ {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
    [Nonempty A] (M : EpisodicMDP S A) (H h : ℕ) (h1 : 1 ≤ h) (h2 : h ≤ H) :
    Vstar M H (h + 1) = optRem M H (H - h) := by
  funext y
  unfold Vstar
  by_cases hc : h + 1 ≤ H
  · have e : H + 1 - (h + 1) = H - h := by omega
    simp only [e, show 1 ≤ h + 1 by omega, hc, and_self, if_true]
  · have e : H - h = 0 := by omega
    simp only [e, optRem, hc, and_false, if_false]

open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma asm_Vstar_le {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
    [Nonempty A] (M : EpisodicMDP S A) (H h : ℕ) (h1 : 1 ≤ h) (h2 : h ≤ H) (x : S) :
    Vstar M H h x = Finset.univ.sup' Finset.univ_nonempty
      (fun a => M.r h x a + ∫ y, Vstar M H (h + 1) y ∂(M.P h (x, a))) := by
  rw [asm_Vstar_succ M H h h1 h2]
  unfold Vstar
  rw [if_pos ⟨h1, h2⟩, show H + 1 - h = (H - h) + 1 by omega, optRem,
    show H - (H - h) = h by omega]

open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma asm_V_succ {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
    [Nonempty A] (M : EpisodicMDP S A) (H : ℕ) (π : Policy S A) (h : ℕ) (h1 : 1 ≤ h)
    (h2 : h ≤ H) (x : S) :
    V M H π h x = M.r h x (π x h) + ∫ y, V M H π (h + 1) y ∂(M.P h (x, π x h)) := by
  have hn : V M H π (h + 1) = valueRem M H π (H - h) := by
    funext y
    unfold V
    by_cases hc : h + 1 ≤ H
    · have e : H + 1 - (h + 1) = H - h := by omega
      simp only [e, show 1 ≤ h + 1 by omega, hc, and_self, if_true]
    · have e : H - h = 0 := by omega
      simp only [e, valueRem, hc, and_false, if_false]
  rw [hn]
  unfold V
  rw [if_pos ⟨h1, h2⟩, show H + 1 - h = (H - h) + 1 by omega, valueRem,
    show H - (H - h) = h by omega]


open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma asm_int_le {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    {f : S → ℝ} (hf : Measurable f) (B C : ℝ) (hb : ∀ y, |f y| ≤ C) (hle : ∀ y, f y ≤ B) :
    ∫ y, f y ∂ν ≤ B := by
  calc _ ≤ ∫ _y, B ∂ν := integral_mono (asm_int ν hf C hb) (integrable_const B) hle
    _ = B := by simp

open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
theorem asm_det {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
    [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H K : ℕ) (hd : 1 ≤ d) (hH : 1 ≤ H)
    (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)) (hM : IsLinearMDP M H d φ)
    (b B : ℝ) (hbB : B + 2 * H * Real.sqrt d ≤ b) (xs : ℕ → ℕ → S) (as : ℕ → ℕ → A)
    (hact : ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H,
      as k h = greedy (lsviQ φ M.r 1 (fun _ => b) H xs as k h (xs k h)))
    (hconc : ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H,
      (∀ h' ∈ Finset.Icc (h + 1) (H + 1), ∀ y,
        0 ≤ lsviV φ M.r 1 (fun _ => b) H xs as k h' y) →
      Real.sqrt (c3Qf M φ xs as k h (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1))) ≤ B) :
    (∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 (H + 1), ∀ y,
      Vstar M H h y ≤ lsviV φ M.r 1 (fun _ => b) H xs as k h y) ∧
    ∀ k ∈ Finset.Icc 1 K,
      Vstar M H 1 (xs k 1) - V M H (greedyPolicy φ M.r 1 (fun _ => b) H xs as k) 1 (xs k 1) ≤
        ∑ h ∈ Finset.Icc 1 H,
          (((∫ y, (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y -
                V M H (greedyPolicy φ M.r 1 (fun _ => b) H xs as k) (h + 1) y)
                ∂(M.P h (xs k h, as k h)))
            - (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) (xs k (h + 1)) -
                V M H (greedyPolicy φ M.r 1 (fun _ => b) H xs as k) (h + 1) (xs k (h + 1))))
            + 2 * b * Real.sqrt (WithLp.ofLp (φ (xs k h) (as k h)) ⬝ᵥ
                ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ (xs k h) (as k h)))))
    := by
  have hφm := hM.2.1
  have hVsm := (c5_values H M).1
  have hVk_nn : ∀ k h y, lsviV φ M.r 1 (fun _ => b) H xs as k h y ≤ H :=
    fun k h y => c4_lsviV_le _ _ _ _ _ _ _ _ _ _
  -- the common one-step estimate (given optimism at levels > h)
  have onestep : ∀ k ∈ Finset.Icc 1 K, ∀ h, 1 ≤ h → h ≤ H →
      (∀ h'' ∈ Finset.Icc (h + 1) (H + 1), ∀ y,
        Vstar M H h'' y ≤ lsviV φ M.r 1 (fun _ => b) H xs as k h'' y) →
      ∀ x a, |inner ℝ (φ x a) (lsviW φ M.r 1 (fun _ => b) H xs as k h) -
        (M.r h x a + ∫ y, lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y ∂(M.P h (x, a)))|
      ≤ b * Real.sqrt (WithLp.ofLp (φ x a) ⬝ᵥ
          ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ x a))) := by
    intro k hk h h1 hhH hopt' x a
    have hh1 : h ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨h1, hhH⟩
    have hpos : ∀ h'' ∈ Finset.Icc (h + 1) (H + 1), ∀ y,
        0 ≤ lsviV φ M.r 1 (fun _ => b) H xs as k h'' y := by
      intro h'' hh'' y
      have hh''' := Finset.mem_Icc.mp hh''
      exact le_trans (((hVsm h'' (by omega) hh'''.2).2 y).1) (hopt' h'' hh'' y)
    have hc := hconc k hk h hh1 hpos
    have hq := c4_lsvi_q_error d H hd hH M φ hM b B xs as k h hh1
      (hpos (h + 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)) hc x a
    have hnrm : 0 ≤ Real.sqrt (WithLp.ofLp (φ x a) ⬝ᵥ
          ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ x a))) :=
      Real.sqrt_nonneg _
    exact hq.trans (mul_le_mul_of_nonneg_right hbB hnrm)
  -- optimism
  have hopt : ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 (H + 1), ∀ y,
      Vstar M H h y ≤ lsviV φ M.r 1 (fun _ => b) H xs as k h y := by
    intro k hk
    have key : ∀ n, ∀ h, h + n = H + 1 → 1 ≤ h → ∀ h' ∈ Finset.Icc h (H + 1), ∀ y,
        Vstar M H h' y ≤ lsviV φ M.r 1 (fun _ => b) H xs as k h' y := by
      intro n
      induction n with
      | zero =>
        intro h hh h1 h' hh' y
        have : h' = H + 1 := by rw [Finset.mem_Icc] at hh'; omega
        subst this
        have e1 : Vstar M H (H + 1) y = 0 := by simp [Vstar]
        have e2 : lsviV φ M.r 1 (fun _ => b) H xs as k (H + 1) y = 0 := by
          simp [lsviV, lsviQ]
        rw [e1, e2]
      | succ n ih =>
        intro h hh h1 h' hh' y
        have hhH : h ≤ H := by omega
        have ih' := ih (h + 1) (by omega) (by omega)
        rcases eq_or_lt_of_le (Finset.mem_Icc.mp hh').1 with heq | hlt
        · rw [← heq]
          haveI := M.isMarkov h
          have hq := onestep k hk h h1 hhH ih'
          have hpos1 : ∀ y, 0 ≤ lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y := fun y =>
            le_trans (((hVsm (h + 1) (by omega) (by omega)).2 y).1)
              (ih' (h + 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) y)
          have hVk1m := c4_lsviV_meas H M.r φ hφm 1 (fun _ => b) xs as k (h + 1)
          have hVs1m := (hVsm (h + 1) (by omega) (by omega)).1
          have hVk1b : ∀ y, |lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y| ≤ H := fun y => by
            rw [abs_of_nonneg (hpos1 y)]; exact hVk_nn k (h + 1) y
          have hVs1b : ∀ y, |Vstar M H (h + 1) y| ≤ H := fun y => by
            have := (hVsm (h + 1) (by omega) (by omega)).2 y
            rw [abs_of_nonneg this.1]
            have h3 : (h : ℝ) ≥ 1 := by exact_mod_cast h1
            push_cast at this
            linarith [this.2]
          rw [asm_Vstar_le M H h h1 hhH y]
          refine Finset.sup'_le _ _ fun a _ => ?_
          have hQ : lsviQ φ M.r 1 (fun _ => b) H xs as k h y a ≤
              lsviV φ M.r 1 (fun _ => b) H xs as k h y :=
            Finset.le_sup' (fun a => lsviQ φ M.r 1 (fun _ => b) H xs as k h y a) (Finset.mem_univ a)
          refine le_trans ?_ hQ
          rw [asm_lsviQ_eq φ M.r (fun _ => b) H xs as k h h1 hhH]
          beta_reduce
          have h3 := hq y a
          have hmono : ∫ z, Vstar M H (h + 1) z ∂(M.P h (y, a)) ≤
              ∫ z, lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) z ∂(M.P h (y, a)) :=
            integral_mono (asm_int _ hVs1m H hVs1b) (asm_int _ hVk1m H hVk1b)
              (fun z => ih' (h + 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) z)
          refine le_min ?_ ?_
          · have := (abs_le.mp h3).1
            linarith
          · have hr := M.r_mem h y a
            have hint : ∫ z, Vstar M H (h + 1) z ∂(M.P h (y, a)) ≤ (H : ℝ) - h :=
              asm_int_le _ hVs1m _ H hVs1b (fun z => by
                have := ((hVsm (h + 1) (by omega) (by omega)).2 z).2
                push_cast at this
                linarith)
            have h3' : (h : ℝ) ≥ 1 := by exact_mod_cast h1
            linarith [hr.2]
        · exact ih' h' (Finset.mem_Icc.mpr ⟨hlt, (Finset.mem_Icc.mp hh').2⟩) y
    intro h hh y
    have hh' := Finset.mem_Icc.mp hh
    exact key (H + 1 - h) h (by omega) hh'.1 h (Finset.mem_Icc.mpr ⟨le_rfl, hh'.2⟩) y
  refine ⟨hopt, ?_⟩
  intro k hk
  haveI : ∀ h, IsMarkovKernel (M.P h) := M.isMarkov
  set π := greedyPolicy φ M.r 1 (fun _ => b) H xs as k with hπ
  have hπm : IsMeasurablePolicy π :=
    c5b_greedy_measurable d H M φ hφm 1 (fun _ => b) xs as k
  have hVπ := (c5_values H M).2 π hπm
  -- one step of the recursion
  have step : ∀ h, 1 ≤ h → h ≤ H →
      lsviV φ M.r 1 (fun _ => b) H xs as k h (xs k h) - V M H π h (xs k h) ≤
        (∫ y, (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y - V M H π (h + 1) y)
            ∂(M.P h (xs k h, as k h))) +
          2 * b * Real.sqrt (WithLp.ofLp (φ (xs k h) (as k h)) ⬝ᵥ
            ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ (xs k h) (as k h))))
      := by
    intro h h1 hhH
    have hh1 : h ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨h1, hhH⟩
    have hopt' : ∀ h'' ∈ Finset.Icc (h + 1) (H + 1), ∀ y,
        Vstar M H h'' y ≤ lsviV φ M.r 1 (fun _ => b) H xs as k h'' y :=
      fun h'' hh'' y => hopt k hk h'' (Finset.mem_Icc.mpr ⟨by
        have := (Finset.mem_Icc.mp hh'').1; omega, (Finset.mem_Icc.mp hh'').2⟩) y
    have hq := onestep k hk h h1 hhH hopt' (xs k h) (as k h)
    have hpos1 : ∀ y, 0 ≤ lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y := fun y =>
      le_trans (((hVsm (h + 1) (by omega) (by omega)).2 y).1)
        (hopt' (h + 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) y)
    have hVk1m := c4_lsviV_meas H M.r φ hφm 1 (fun _ => b) xs as k (h + 1)
    have hVk1b : ∀ y, |lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y| ≤ H := fun y => by
      rw [abs_of_nonneg (hpos1 y)]; exact hVk_nn k (h + 1) y
    have hVπm := (hVπ (h + 1) (by omega) (by omega)).1
    have hVπb : ∀ y, |V M H π (h + 1) y| ≤ H := fun y => by
      have := (hVπ (h + 1) (by omega) (by omega)).2 y
      rw [abs_of_nonneg this.1]
      have h3 : (h : ℝ) ≥ 1 := by exact_mod_cast h1
      push_cast at this
      linarith [this.2]
    have hact' : π (xs k h) h = as k h := (hact k hk h hh1).symm
    have hVk : lsviV φ M.r 1 (fun _ => b) H xs as k h (xs k h) =
        lsviQ φ M.r 1 (fun _ => b) H xs as k h (xs k h) (as k h) := by
      rw [hact k hk h hh1]
      exact (asm_greedy_max (lsviQ φ M.r 1 (fun _ => b) H xs as k h (xs k h))).symm
    have hVπeq := asm_V_succ M H π h h1 hhH (xs k h)
    rw [hact'] at hVπeq
    rw [hVk, hVπeq, asm_lsviQ_eq φ M.r (fun _ => b) H xs as k h h1 hhH,
      integral_sub (asm_int _ hVk1m H hVk1b) (asm_int _ hVπm H hVπb)]
    beta_reduce
    have h3 := (abs_le.mp hq).2
    have h4 := min_le_left (inner ℝ (φ (xs k h) (as k h)) (lsviW φ M.r 1 (fun _ => b) H xs as k h) +
      b * Real.sqrt (WithLp.ofLp (φ (xs k h) (as k h)) ⬝ᵥ
        ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ (xs k h) (as k h))))) (H : ℝ)
    linarith
  -- telescoping
  have tele : ∀ n, ∀ j, j + n = H + 1 → 1 ≤ j →
      lsviV φ M.r 1 (fun _ => b) H xs as k j (xs k j) - V M H π j (xs k j) ≤
        ∑ h ∈ Finset.Ico j (H + 1),
          (((∫ y, (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) y - V M H π (h + 1) y)
                ∂(M.P h (xs k h, as k h)))
            - (lsviV φ M.r 1 (fun _ => b) H xs as k (h + 1) (xs k (h + 1)) -
                V M H π (h + 1) (xs k (h + 1))))
            + 2 * b * Real.sqrt (WithLp.ofLp (φ (xs k h) (as k h)) ⬝ᵥ
                ((LinearMDPRL.Linear.gram φ 1 xs as k h)⁻¹ *ᵥ WithLp.ofLp (φ (xs k h) (as k h))))) := by
    intro n
    induction n with
    | zero =>
      intro j hj h1
      have : j = H + 1 := by omega
      subst this
      simp [lsviV, lsviQ, V]
    | succ n ih =>
      intro j hj h1
      have ih' := ih (j + 1) (by omega) (by omega)
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      have st := step j h1 (by omega)
      linarith
  have hIcc : Finset.Ico 1 (H + 1) = Finset.Icc 1 H := by
    ext z; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  have h1' := tele H 1 (by omega) le_rfl
  rw [hIcc] at h1'
  have := hopt k hk 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) (xs k 1)
  linarith


open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma pv_meas {Ω' S A : Type*} [MeasurableSpace Ω'] [MeasurableSpace S] [MeasurableSpace A]
    [Fintype A] [Nonempty A] (M : EpisodicMDP S A) (H : ℕ)
    (π : Ω' → Policy S A) (hπ : ∀ h a, MeasurableSet {p : Ω' × S | π p.1 p.2 h = a}) :
    ∀ n, Measurable (fun p : Ω' × S => valueRem M H (π p.1) n p.2) := by
  intro n
  induction n with
  | zero => simp only [valueRem]; exact measurable_const
  | succ n ih =>
    haveI := M.isMarkov (H - n)
    have hmeas : Measurable (fun p : Ω' × S => (p.2, π p.1 p.2 (H - n))) :=
      measurable_snd.prodMk (measurable_to_countable' fun a => hπ (H - n) a)
    have hint : Measurable (fun p : Ω' × S =>
        ∫ y, valueRem M H (π p.1) n y ∂(M.P (H - n) (p.2, π p.1 p.2 (H - n)))) := by
      have h1 : StronglyMeasurable (fun q : (Ω' × S) × S => valueRem M H (π q.1.1) n q.2) :=
        (ih.comp (measurable_fst.fst.prodMk measurable_snd)).stronglyMeasurable
      have h2 := h1.integral_kernel_prod_right'
        (κ := (M.P (H - n)).comap (fun p : Ω' × S => (p.2, π p.1 p.2 (H - n))) hmeas)
      exact h2.measurable
    have hr : Measurable (fun p : Ω' × S => M.r (H - n) p.2 (π p.1 p.2 (H - n))) :=
      c5_policy_comp (S := Ω' × S) (fun p h => π p.1 p.2 h) (H - n) (fun a => hπ (H - n) a)
        (fun p a => M.r (H - n) p.2 a) (fun a => (M.r_meas (H - n) a).comp measurable_snd)
    simp only [valueRem]
    exact hr.add hint

open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
lemma asm_g_meas {Ω S A : Type} [G : MeasurableSpace Ω] [mS : MeasurableSpace S] [Fintype A]
    [Nonempty A] [LinearOrder A] [mA : MeasurableSpace A] [DiscreteMeasurableSpace A] {d : ℕ}
    (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d))
    (hφ : ∀ b, Measurable (fun x => φ x b)) (β : ℕ → ℝ) (H k : ℕ)
    (x : ℕ → ℕ → Ω → S) (a : ℕ → ℕ → Ω → A)
    (hx : ∀ τ, 1 ≤ τ → τ < k → ∀ i, 1 ≤ i → i ≤ H + 1 → Measurable (x τ i))
    (ha : ∀ τ, 1 ≤ τ → τ < k → ∀ i, 1 ≤ i → i ≤ H → Measurable (a τ i)) (j : ℕ) :
    Measurable (fun p : Ω × S =>
      max 0 (min (lsviV φ M.r 1 β H (fun τ i => x τ i p.1) (fun τ i => a τ i p.1) k j p.2)
        (H : ℝ)) -
      V M H (greedyPolicy φ M.r 1 β H (fun τ i => x τ i p.1) (fun τ i => a τ i p.1) k) j p.2) := by
  have hx' : ∀ τ, 1 ≤ τ → τ < k → ∀ i, 1 ≤ i → i ≤ H + 1 →
      Measurable (fun p : Ω × S => x τ i p.1) :=
    fun τ h1 h2 i h3 h4 => (hx τ h1 h2 i h3 h4).comp measurable_fst
  have ha' : ∀ τ, 1 ≤ τ → τ < k → ∀ i, 1 ≤ i → i ≤ H →
      Measurable (fun p : Ω × S => a τ i p.1) :=
    fun τ h1 h2 i h3 h4 => (ha τ h1 h2 i h3 h4).comp measurable_fst
  have hQ : ∀ h b, Measurable (fun p : Ω × S =>
      lsviQ φ M.r 1 β H (fun τ i => x τ i p.1) (fun τ i => a τ i p.1) k h p.2 b) := by
    intro h b
    unfold lsviQ
    by_cases hc : 1 ≤ h ∧ h ≤ H
    · simp only [if_pos hc]
      exact c3a_Q_meas (Ω := Ω × S) φ hφ M.r (fun j b => M.r_meas j b) 1 β H
        (fun τ i p => x τ i p.1) (fun τ i p => a τ i p.1) k hx' ha'
        (H + 1 - h) (by omega) Prod.snd measurable_snd b
    · simp only [if_neg hc]
      exact measurable_const
  have hV : ∀ h, Measurable (fun p : Ω × S =>
      lsviV φ M.r 1 β H (fun τ i => x τ i p.1) (fun τ i => a τ i p.1) k h p.2) := by
    intro h
    have e : (fun p : Ω × S => lsviV φ M.r 1 β H (fun τ i => x τ i p.1) (fun τ i => a τ i p.1) k h p.2)
        = Finset.univ.sup' Finset.univ_nonempty (fun b (p : Ω × S) =>
          lsviQ φ M.r 1 β H (fun τ i => x τ i p.1) (fun τ i => a τ i p.1) k h p.2 b) := by
      funext p; simp only [lsviV, Finset.sup'_apply]
    rw [e]
    exact Finset.measurable_sup' _ (fun b _ => hQ h b)
  have hπ : ∀ h a0, MeasurableSet
      {p : Ω × S | greedyPolicy φ M.r 1 β H (fun τ i => x τ i p.1) (fun τ i => a τ i p.1) k p.2 h = a0} := by
    intro h a0
    exact c5b_greedy_set (S := Ω × S)
      (fun p b => lsviQ φ M.r 1 β H (fun τ i => x τ i p.1) (fun τ i => a τ i p.1) k h p.2 b)
      (fun b => hQ h b) a0
  have hVπ : Measurable (fun p : Ω × S =>
      V M H (greedyPolicy φ M.r 1 β H (fun τ i => x τ i p.1) (fun τ i => a τ i p.1) k) j p.2) := by
    unfold V
    by_cases hc : 1 ≤ j ∧ j ≤ H
    · simp only [if_pos hc]
      exact pv_meas M H
        (fun ω => greedyPolicy φ M.r 1 β H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k) hπ
        (H + 1 - j)
    · simp only [if_neg hc]
      exact measurable_const
  exact (measurable_const.max ((hV j).min measurable_const)).sub hVπ


open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
/-- The Azuma sum `Σ_k ζ̃_{k,h}` (with the value estimate clipped to `[0, H]`) along the data. -/
noncomputable def azS {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
    [Nonempty A] [LinearOrder A] {d : ℕ} (M : EpisodicMDP S A)
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (β : ℕ → ℝ) (H K : ℕ) (xs : ℕ → ℕ → S)
    (as : ℕ → ℕ → A) (h : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K,
        ((∫ y, (max 0 (min (lsviV φ M.r 1 β H xs as k (h + 1) y) (H : ℝ)) -
            V M H (greedyPolicy φ M.r 1 β H xs as k) (h + 1) y) ∂(M.P h (xs k h, as k h))) -
          (max 0 (min (lsviV φ M.r 1 β H xs as k (h + 1) (xs k (h + 1))) (H : ℝ)) -
            V M H (greedyPolicy φ M.r 1 β H xs as k) (h + 1) (xs k (h + 1))))

open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
theorem asm_azuma {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
    [MeasurableSpace A] [DiscreteMeasurableSpace A] {d : ℕ}
    {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝓕 : Filtration ℕ mΩ) (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d))
    (hφ : ∀ b, Measurable (fun x => φ x b)) (β : ℕ → ℝ) (H K : ℕ) (hH : 1 ≤ H)
    (x : ℕ → ℕ → Ω → S) (a : ℕ → ℕ → Ω → A) (hrun : IsLSVIUCBRun μ 𝓕 M φ 1 β H K x a)
    (h : ℕ) (hh1 : 1 ≤ h) (hhH : h ≤ H) (ε : ℝ) (hε : 0 < ε) :
    μ {ω | ε < azS M φ β H K (fun τ i => x τ i ω) (fun τ i => a τ i ω) h}
      ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2) / (2 * K * (H : ℝ) ^ 2))) := by
  haveI := M.isMarkov h
  have hmono : Monotone (fun t : ℕ => 𝓕 (tIdx H (t + 1) h)) := by
    intro i j hij
    refine 𝓕.mono ?_
    unfold tIdx
    have : i * (H + 1) ≤ j * (H + 1) := Nat.mul_le_mul_right _ hij
    simp only [Nat.add_sub_cancel]
    omega
  let G : Filtration ℕ mΩ := ⟨fun t => 𝓕 (tIdx H (t + 1) h), hmono, fun t => 𝓕.le _⟩
  have hGt : ∀ t, G t = 𝓕 (tIdx H (t + 1) h) := fun t => rfl
  have hact := c3a_actions μ 𝓕 M φ hφ 1 β H K x a hrun
  have hxm : ∀ t, t < K → Measurable[G t] (x (t + 1) h) := fun t ht => by
    rw [hGt]; exact hrun.adapted (t + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) h
      (Finset.mem_Icc.mpr ⟨hh1, by omega⟩)
  have ham : ∀ t, t < K → Measurable[G t] (a (t + 1) h) := fun t ht => by
    rw [hGt]; exact hact (t + 1) (by omega) (by omega) h hh1 hhH
  let g : ℕ → Ω → S → ℝ := fun t ω y =>
    max 0 (min (lsviV φ M.r 1 β H (fun τ i => x τ i ω) (fun τ i => a τ i ω) (t + 1) (h + 1) y)
      (H : ℝ)) -
    V M H (greedyPolicy φ M.r 1 β H (fun τ i => x τ i ω) (fun τ i => a τ i ω) (t + 1)) (h + 1) y
  have hC6 := c6_azuma_markov μ G (M.P h)
    (fun t ω => (x (t + 1) h ω, a (t + 1) h ω)) (fun t ω => x (t + 1) (h + 1) ω) K
    (fun t ht => (hxm t ht).prodMk (ham t ht))
    (fun t ht => by
      show Measurable[𝓕 (tIdx H (t + 1 + 1) h)] (x (t + 1) (h + 1))
      refine (hrun.adapted (t + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) (h + 1)
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).mono (𝓕.mono ?_) le_rfl
      unfold tIdx
      have : (t + 1 - 1) * (H + 1) + (H + 1) = (t + 1 + 1 - 1) * (H + 1) := by
        simp only [Nat.add_sub_cancel]; ring
      omega)
    (fun t ht B hB => hrun.transition (t + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) h
      (Finset.mem_Icc.mpr ⟨hh1, hhH⟩) B hB)
    g (H : ℝ) (by exact_mod_cast hH)
    (fun t ht => by
      show Measurable[(𝓕 (tIdx H (t + 1) h)).prod ‹MeasurableSpace S›] (fun p : Ω × S => g t p.1 p.2)
      have hx2 : ∀ τ, 1 ≤ τ → τ < t + 1 → ∀ i, 1 ≤ i → i ≤ H + 1 →
          Measurable[𝓕 (tIdx H (t + 1) h)] (x τ i) := by
        intro τ hτ1 hτk i hi1 hi2
        exact (hrun.adapted τ (Finset.mem_Icc.mpr ⟨hτ1, by omega⟩) i
          (Finset.mem_Icc.mpr ⟨hi1, hi2⟩)).mono (𝓕.mono (c3a_tIdx_le H τ i (t + 1) h hτ1 hτk hi2))
          le_rfl
      have ha2 : ∀ τ, 1 ≤ τ → τ < t + 1 → ∀ i, 1 ≤ i → i ≤ H →
          Measurable[𝓕 (tIdx H (t + 1) h)] (a τ i) := by
        intro τ hτ1 hτk i hi1 hi2
        exact (hact τ hτ1 (by omega) i hi1 hi2).mono
          (𝓕.mono (c3a_tIdx_le H τ i (t + 1) h hτ1 hτk (by omega))) le_rfl
      exact @asm_g_meas Ω S A (𝓕 (tIdx H (t + 1) h)) _ _ _ _ _ _ d M φ hφ β H (t + 1) x a hx2 ha2
        (h + 1))
    (fun t ω y => by
      have hπm := c5b_greedy_measurable d H M φ hφ 1 β (fun τ i => x τ i ω)
        (fun τ i => a τ i ω) (t + 1)
      have hV := ((c5_values H M).2 _ hπm (h + 1) (by omega) (by omega)).2 y
      have hHn : (0 : ℝ) ≤ H := Nat.cast_nonneg _
      have hc0 : 0 ≤ max 0 (min (lsviV φ M.r 1 β H (fun τ i => x τ i ω) (fun τ i => a τ i ω)
          (t + 1) (h + 1) y) (H : ℝ)) := le_max_left _ _
      have hc1 : max 0 (min (lsviV φ M.r 1 β H (fun τ i => x τ i ω) (fun τ i => a τ i ω)
          (t + 1) (h + 1) y) (H : ℝ)) ≤ H := max_le hHn (min_le_right _ _)
      have h3 : (h : ℝ) ≥ 1 := by exact_mod_cast hh1
      push_cast at hV
      show |max 0 (min _ (H : ℝ)) - _| ≤ H
      rw [abs_le]
      constructor <;> linarith [hV.1, hV.2])
    ε hε
  refine le_trans (measure_mono ?_) hC6
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hS : ∑ k ∈ Finset.Icc 1 K,
      ((∫ y, (max 0 (min (lsviV φ M.r 1 β H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k (h + 1) y)
              (H : ℝ)) -
            V M H (greedyPolicy φ M.r 1 β H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k)
              (h + 1) y) ∂(M.P h (x k h ω, a k h ω))) -
          (max 0 (min (lsviV φ M.r 1 β H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k (h + 1)
              (x k (h + 1) ω)) (H : ℝ)) -
            V M H (greedyPolicy φ M.r 1 β H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k)
              (h + 1) (x k (h + 1) ω))) =
      ∑ t ∈ Finset.range K, ((∫ y, g t ω y ∂(M.P h (x (t + 1) h ω, a (t + 1) h ω))) -
        g t ω (x (t + 1) (h + 1) ω)) := by
    have e : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
      ext z; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [e, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [add_comm 1 t]
  unfold azS at hω
  rw [hS] at hω
  exact hω


lemma fin_iota (d K H : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (hH : 1 ≤ H) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (ι : ℝ) (hι : ι = Real.log (2 * d * ((K : ℝ) * H) / p)) :
    0.69 ≤ ι ∧ Real.log (2 * H / p) ≤ ι ∧ Real.log (1 + (K : ℝ) / d) ≤ ι := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hN2 : 2 ≤ 2 * (d : ℝ) * ((K : ℝ) * H) / p := by
    rw [le_div_iff₀ hp0]
    have : (1 : ℝ) ≤ d * (K * H) := by nlinarith [mul_pos (by linarith : (0 : ℝ) < K) (by linarith : (0 : ℝ) < H)]
    nlinarith
  have h2 := Real.log_two_gt_d9
  refine ⟨?_, ?_, ?_⟩
  · rw [hι]
    have := Real.log_le_log (by norm_num) hN2
    linarith
  · rw [hι]
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_right _ hp0.le
    have : (1 : ℝ) ≤ d * K := by nlinarith
    nlinarith
  · rw [hι]
    apply Real.log_le_log (by positivity)
    rw [le_div_iff₀ hp0]
    have hd0 : (0 : ℝ) < d := by linarith
    have e1 : (K : ℝ) / d ≤ K := div_le_self (by linarith) hd1
    have e2 : (1 + (K : ℝ) / d) * p ≤ 1 + K := by nlinarith
    have e3 : (1 : ℝ) + K ≤ 2 * K := by linarith
    have e4 : (2 : ℝ) * K ≤ 2 * d * (K * H) := by nlinarith [mul_pos (by linarith : (0 : ℝ) < K) (by linarith : (0 : ℝ) < H)]
    linarith

lemma fin_hbB (d K H : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (hH : 1 ≤ H) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (ι b : ℝ) (hι : ι = Real.log (2 * d * ((K : ℝ) * H) / p))
    (hb : b = 30 * d * H * Real.sqrt ι) :
    5 * d * H * Real.sqrt (Real.log (d * K * H * (1 + b) / (p / 2)) + 1) +
      2 * H * Real.sqrt d ≤ b := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  obtain ⟨hι69, -, -⟩ := fin_iota d K H hd hK hH p hp0 hp1 ι hι
  have hdH : (1 : ℝ) ≤ d * H := by nlinarith
  set N : ℝ := 2 * d * ((K : ℝ) * H) / p with hN
  have hN1 : (d : ℝ) * H ≤ N := by
    rw [hN, le_div_iff₀ hp0]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < K) (by linarith : (0 : ℝ) < H),
      mul_pos (by linarith : (0 : ℝ) < d) (by linarith : (0 : ℝ) < H)]
  have hN0 : 0 < N := by linarith
  set sι := Real.sqrt ι with hsι
  have hsq : sι ^ 2 = ι := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ sι := Real.sqrt_nonneg _
  have hs8 : 0.8 ≤ sι := by nlinarith
  have hbpos : 0 ≤ b := by rw [hb]; positivity
  have hsle : sι ≤ 1 + ι := by nlinarith
  -- 1 + b ≤ 31 N (1 + ι)
  have h1b : 1 + b ≤ 31 * N * (1 + ι) := by
    have : b ≤ 30 * N * (1 + ι) := by
      rw [hb]
      have : (30 : ℝ) * d * H * sι ≤ 30 * (d * H) * (1 + ι) := by
        have := mul_le_mul_of_nonneg_left hsle (by positivity : (0 : ℝ) ≤ 30 * (d * H))
        linarith
      have h2 : (30 : ℝ) * (d * H) * (1 + ι) ≤ 30 * N * (1 + ι) := by
        have : 0 ≤ 1 + ι := by linarith
        nlinarith
      linarith
    nlinarith
  have hlog1b : Real.log (1 + b) ≤ 3.47 + 2 * ι := by
    have h31 : Real.log 31 ≤ 3.47 := by
      have h2 := Real.log_two_lt_d9
      have : Real.log 31 ≤ Real.log (2 ^ 5) := Real.log_le_log (by norm_num) (by norm_num)
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have := Real.log_le_log (by linarith) h1b
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hN0.ne'] at this
    have h3 : Real.log (1 + ι) ≤ ι := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + ι)
      linarith
    have h4 : Real.log N = ι := by rw [hι]
    linarith
  have harg : (d : ℝ) * K * H * (1 + b) / (p / 2) = N * (1 + b) := by
    rw [hN]; field_simp
  rw [harg, Real.log_mul hN0.ne' (by linarith)]
  have h4 : Real.log N = ι := by rw [hι]
  rw [h4]
  have hL : ι + Real.log (1 + b) + 1 ≤ 16 * ι := by linarith
  have hsqL : Real.sqrt (ι + Real.log (1 + b) + 1) ≤ 4 * sι := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hd2 : Real.sqrt d ≤ d := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hfirst : 5 * (d : ℝ) * H * Real.sqrt (ι + Real.log (1 + b) + 1) ≤ 5 * d * H * (4 * sι) :=
    mul_le_mul_of_nonneg_left hsqL (by positivity)
  have hsecond : 2 * (H : ℝ) * Real.sqrt d ≤ 2 * H * d :=
    mul_le_mul_of_nonneg_left hd2 (by positivity)
  have h10 : 2 * (H : ℝ) * d ≤ 10 * d * H * sι := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < d) (by linarith : (0 : ℝ) < H)]
  have hbe : b = 30 * d * H * sι := hb
  nlinarith [hfirst, hsecond, h10, hbe]

lemma fin_num2 (d K H : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (hH : 1 ≤ H) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (ι : ℝ) (hι : ι = Real.log (2 * d * ((K : ℝ) * H) / p)) :
    (H : ℝ) * ((H : ℝ) * Real.sqrt (2 * K * Real.log (2 * H / p)) +
      2 * (30 * d * H * Real.sqrt ι) * Real.sqrt (K * (2 * d * Real.log (1 + (K : ℝ) / d)))) ≤
    100 * Real.sqrt ((d : ℝ) ^ 3 * (H : ℝ) ^ 3 * ((K : ℝ) * H) * ι ^ 2) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  obtain ⟨hι69, hlog1, hlog2⟩ := fin_iota d K H hd hK hH p hp0 hp1 ι hι
  set u := Real.sqrt ((d : ℝ) * K) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = d * K := Real.sq_sqrt (by positivity)
  have hRHS : Real.sqrt ((d : ℝ) ^ 3 * (H : ℝ) ^ 3 * ((K : ℝ) * H) * ι ^ 2) = d * H ^ 2 * ι * u := by
    have : (d : ℝ) ^ 3 * (H : ℝ) ^ 3 * ((K : ℝ) * H) * ι ^ 2 = (d * H ^ 2 * ι) ^ 2 * (d * K) := by ring
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hRHS]
  have hι0 : 0 < ι := by linarith
  set sι := Real.sqrt ι with hsι
  have hsq : sι ^ 2 = ι := Real.sq_sqrt hι0.le
  have hs0 : 0 ≤ sι := Real.sqrt_nonneg _
  have T1 : Real.sqrt (2 * K * Real.log (2 * H / p)) ≤ 2 * ι * u := by
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : 2 * (K : ℝ) * Real.log (2 * H / p) ≤ 2 * K * ι := by
      apply mul_le_mul_of_nonneg_left hlog1; positivity
    have h2 : (2 * (K : ℝ) * ι) ≤ (2 * ι * u) ^ 2 := by
      rw [mul_pow, hu2]
      nlinarith [mul_pos (by linarith : (0 : ℝ) < K) hι0, mul_pos (by linarith : (0 : ℝ) < d) hι0,
        mul_pos (mul_pos (by linarith : (0 : ℝ) < K) hι0) (by linarith : (0 : ℝ) < d)]
    linarith
  have hlogK : K * (2 * (d : ℝ) * Real.log (1 + (K : ℝ) / d)) ≤ 2 * d * K * ι := by
    have : K * (2 * (d : ℝ) * Real.log (1 + (K : ℝ) / d)) ≤ K * (2 * d * ι) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hlog2 (by positivity)
    linarith
  have hZ0 : 0 ≤ (K : ℝ) * (2 * (d : ℝ) * Real.log (1 + (K : ℝ) / d)) := by
    have : 0 ≤ Real.log (1 + (K : ℝ) / d) := Real.log_nonneg (by
      have : 0 ≤ (K : ℝ) / d := by positivity
      linarith)
    positivity
  have T2 : sι * Real.sqrt (K * (2 * (d : ℝ) * Real.log (1 + (K : ℝ) / d))) ≤ 3 / 2 * ι * u := by
    rw [hsι, ← Real.sqrt_mul hι0.le, Real.sqrt_le_left (by positivity)]
    have h1 : ι * (K * (2 * (d : ℝ) * Real.log (1 + (K : ℝ) / d))) ≤ ι * (2 * d * K * ι) :=
      mul_le_mul_of_nonneg_left hlogK hι0.le
    have h2 : (3 / 2 * ι * u) ^ 2 = 9 / 4 * ι ^ 2 * (d * K) := by rw [mul_pow, hu2]; ring
    rw [h2]
    nlinarith [mul_pos (mul_pos (by linarith : (0 : ℝ) < d) (by linarith : (0 : ℝ) < K))
      (pow_pos hι0 2)]
  have e : (H : ℝ) * ((H : ℝ) * Real.sqrt (2 * K * Real.log (2 * H / p)) +
      2 * (30 * d * H * sι) * Real.sqrt (K * (2 * d * Real.log (1 + (K : ℝ) / d)))) =
      H ^ 2 * Real.sqrt (2 * K * Real.log (2 * H / p)) +
      60 * d * H ^ 2 * (sι * Real.sqrt (K * (2 * (d : ℝ) * Real.log (1 + (K : ℝ) / d)))) := by ring
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left T1 (by positivity : (0 : ℝ) ≤ (H : ℝ) ^ 2)
  have h2 := mul_le_mul_of_nonneg_left T2 (by positivity : (0 : ℝ) ≤ 60 * (d : ℝ) * (H : ℝ) ^ 2)
  have hpos : 0 ≤ (H : ℝ) ^ 2 * ι * u := by positivity
  nlinarith [mul_nonneg (sub_nonneg.2 hd1) hpos]


lemma fin_cs (K : ℕ) (q : ℕ → ℝ) (hq : ∀ k, 0 ≤ q k) :
    ∑ k ∈ Finset.Icc 1 K, Real.sqrt (q k) ≤
      Real.sqrt ((K : ℝ) * ∑ k ∈ Finset.Icc 1 K, q k) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 K) (fun _ => (1 : ℝ))
    (fun k => Real.sqrt (q k))
  have hsq : ∑ k ∈ Finset.Icc 1 K, (Real.sqrt (q k)) ^ 2 = ∑ k ∈ Finset.Icc 1 K, q k :=
    Finset.sum_congr rfl fun k _ => Real.sq_sqrt (hq k)
  have hcard : ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) ^ 2 = K := by simp
  simp only [one_mul] at h
  rw [hsq, hcard] at h
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt h)

open MeasureTheory ProbabilityTheory Matrix LinearMDPRL.Linear in
theorem lsvi_ucb_regret_final :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
        [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H K : ℕ), 1 ≤ d → 1 ≤ H → 1 ≤ K →
      ∀ (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)), IsLinearMDP M H d φ →
      ∀ p : ℝ, 0 < p → p < 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) (x : ℕ → ℕ → Ω → S) (a : ℕ → ℕ → Ω → A),
        IsLSVIUCBRun μ 𝓕 M φ 1 (fun _ => c * d * H * Real.sqrt (iota d K H p)) H K x a →
        μ {ω | C * Real.sqrt ((d : ℝ) ^ 3 * (H : ℝ) ^ 3 * ((K : ℝ) * H) * iota d K H p ^ 2) <
            regret M φ 1 (fun _ => c * d * H * Real.sqrt (iota d K H p)) H K
              (fun τ i => x τ i ω) (fun τ i => a τ i ω)}
          ≤ ENNReal.ofReal p := by
  refine ⟨30, 100, by norm_num, by norm_num, ?_⟩
  intro S A mS iF iN iL mA iD d H K hd hH hK M φ hM p hp0 hp1 Ω mΩ μ iμ 𝓕 x a hrun
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  obtain ⟨ι, hιd⟩ : ∃ ι, ι = iota d K H p := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = 30 * d * H * Real.sqrt ι := ⟨_, rfl⟩
  have hι' : ι = Real.log (2 * d * ((K : ℝ) * H) / p) := by rw [hιd]; rfl
  have hbeq : (30 : ℝ) * d * H * Real.sqrt (iota d K H p) = b := by rw [hbd, hιd]
  rw [hbeq] at hrun ⊢
  rw [← hιd]
  obtain ⟨hι69, hlog1, hlog2⟩ := fin_iota d K H hd hK hH p hp0 hp1 ι hι'
  have hb0 : 0 ≤ b := by rw [hbd]; positivity
  have hbB := fin_hbB d K H hd hK hH p hp0 hp1 ι b hι' hbd
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = p / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ < 1 := by rw [hδ]; linarith
  rw [← hδ] at hbB
  have hφm := hM.2.1
  have hφn := hM.1
  have hlogpos : 0 < Real.log (2 * H / p) :=
    Real.log_pos (by rw [lt_div_iff₀ hp0]; nlinarith)
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = H * Real.sqrt (2 * K * Real.log (2 * H / p)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hε]
    exact mul_pos (by linarith) (Real.sqrt_pos.mpr (mul_pos (by linarith) hlogpos))
  -- the Azuma events
  have hAz : ∀ h ∈ Finset.Icc 1 H,
      μ {ω | ε < azS M φ (fun _ => b) H K (fun τ i => x τ i ω) (fun τ i => a τ i ω) h} ≤
        ENNReal.ofReal (p / (2 * H)) := by
    intro h hh
    have hh' := Finset.mem_Icc.mp hh
    refine le_trans (asm_azuma μ 𝓕 M φ hφm (fun _ => b) H K hH x a hrun h hh'.1 hh'.2 ε hε0) ?_
    apply ENNReal.ofReal_le_ofReal
    have hε2 : ε ^ 2 = (H : ℝ) ^ 2 * (2 * K * Real.log (2 * H / p)) := by
      rw [hε, mul_pow, Real.sq_sqrt (by positivity)]
    have e : -(ε ^ 2) / (2 * K * (H : ℝ) ^ 2) = -Real.log (2 * H / p) := by
      rw [hε2]; field_simp
    rw [e, Real.exp_neg, Real.exp_log (by positivity)]
    apply le_of_eq
    field_simp
  -- the sets
  have hC3 := c3_main5 d H K hd hH hK M φ hM b hb0 δ hδ0 hδ1 μ 𝓕 x a hrun
  have hsub : {ω | 100 * Real.sqrt ((d : ℝ) ^ 3 * (H : ℝ) ^ 3 * ((K : ℝ) * H) * ι ^ 2) <
        regret M φ 1 (fun _ => b) H K (fun τ i => x τ i ω) (fun τ i => a τ i ω)} ⊆
      c3Ev M φ b δ H K x a ∪ ⋃ h ∈ Finset.Icc 1 H,
        {ω | ε < azS M φ (fun _ => b) H K (fun τ i => x τ i ω) (fun τ i => a τ i ω) h} := by
    intro ω hω
    by_contra hnot
    rw [Set.mem_union, not_or, Set.mem_iUnion₂] at hnot
    obtain ⟨hn3, hnAz⟩ := hnot
    simp only [not_exists] at hnAz
    have hnAz' : ∀ h ∈ Finset.Icc 1 H,
        azS M φ (fun _ => b) H K (fun τ i => x τ i ω) (fun τ i => a τ i ω) h ≤ ε := by
      intro h hh
      have := hnAz h hh
      simpa using this
    simp only [c3Ev, Set.mem_setOf_eq, not_exists, not_and, not_lt] at hn3
    have hact : ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H,
        a k h ω = greedy (lsviQ φ M.r 1 (fun _ => b) H (fun τ i => x τ i ω)
          (fun τ i => a τ i ω) k h (x k h ω)) :=
      fun k hk h hh => hrun.actions ω k hk h hh
    obtain ⟨hopt, hreg⟩ := asm_det d H K hd hH M φ hM b
      (5 * d * H * Real.sqrt (Real.log (d * K * H * (1 + b) / δ) + 1)) hbB
      (fun τ i => x τ i ω) (fun τ i => a τ i ω) hact
      (fun k hk h hh hpos => hn3 k hk h hh hpos)
    -- regret bound
    have hregret : regret M φ 1 (fun _ => b) H K (fun τ i => x τ i ω) (fun τ i => a τ i ω) ≤
        (H : ℝ) * (ε + 2 * b * Real.sqrt (K * (2 * d * Real.log (1 + (K : ℝ) / d)))) := by
      have hclip : ∀ k ∈ Finset.Icc 1 K, ∀ h ∈ Finset.Icc 1 H, ∀ y,
          max 0 (min (lsviV φ M.r 1 (fun _ => b) H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k
            (h + 1) y) (H : ℝ)) =
          lsviV φ M.r 1 (fun _ => b) H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k (h + 1) y := by
        intro k hk h hh y
        have hh' := Finset.mem_Icc.mp hh
        have h0 : 0 ≤ lsviV φ M.r 1 (fun _ => b) H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k
            (h + 1) y :=
          le_trans (((c5_values H M).1 (h + 1) (by omega) (by omega)).2 y).1
            (hopt k hk (h + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) y)
        have h1 := c4_lsviV_le φ M.r 1 (fun _ => b) H (fun τ i => x τ i ω) (fun τ i => a τ i ω)
          k (h + 1) y
        rw [min_eq_left h1, max_eq_right h0]
      have hzeta : ∀ h ∈ Finset.Icc 1 H, ∑ k ∈ Finset.Icc 1 K,
          ((∫ y, (lsviV φ M.r 1 (fun _ => b) H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k (h + 1) y -
                V M H (greedyPolicy φ M.r 1 (fun _ => b) H (fun τ i => x τ i ω)
                  (fun τ i => a τ i ω) k) (h + 1) y) ∂(M.P h (x k h ω, a k h ω)))
            - (lsviV φ M.r 1 (fun _ => b) H (fun τ i => x τ i ω) (fun τ i => a τ i ω) k (h + 1)
                  (x k (h + 1) ω) -
                V M H (greedyPolicy φ M.r 1 (fun _ => b) H (fun τ i => x τ i ω)
                  (fun τ i => a τ i ω) k) (h + 1) (x k (h + 1) ω))) =
          azS M φ (fun _ => b) H K (fun τ i => x τ i ω) (fun τ i => a τ i ω) h := by
        intro h hh
        unfold azS
        refine Finset.sum_congr rfl fun k hk => ?_
        simp only [hclip k hk h hh]
      have hsum : ∀ h ∈ Finset.Icc 1 H, ∑ k ∈ Finset.Icc 1 K,
          Real.sqrt (WithLp.ofLp (φ (x k h ω) (a k h ω)) ⬝ᵥ
            ((LinearMDPRL.Linear.gram φ 1 (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h)⁻¹ *ᵥ
              WithLp.ofLp (φ (x k h ω) (a k h ω)))) ≤
          Real.sqrt (K * (2 * d * Real.log (1 + (K : ℝ) / d))) := by
        intro h hh
        refine le_trans (fin_cs K (fun k => WithLp.ofLp (φ (x k h ω) (a k h ω)) ⬝ᵥ
            ((LinearMDPRL.Linear.gram φ 1 (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h)⁻¹ *ᵥ
              WithLp.ofLp (φ (x k h ω) (a k h ω)))) (fun k =>
            e5_a_nonneg (c4_gram_pd φ (fun τ i => x τ i ω) (fun τ i => a τ i ω) k h) _)) ?_
        apply Real.sqrt_le_sqrt
        exact mul_le_mul_of_nonneg_left (c1_elliptical_potential hd φ hφn
          (fun τ i => x τ i ω) (fun τ i => a τ i ω) h K) (Nat.cast_nonneg _)
      unfold regret
      refine le_trans (Finset.sum_le_sum fun k hk => hreg k hk) ?_
      rw [Finset.sum_comm]
      calc _ ≤ ∑ h ∈ Finset.Icc 1 H, (ε + 2 * b *
            Real.sqrt (K * (2 * d * Real.log (1 + (K : ℝ) / d)))) :=
            Finset.sum_le_sum fun h hh => ?_
        _ = (H : ℝ) * (ε + 2 * b * Real.sqrt (K * (2 * d * Real.log (1 + (K : ℝ) / d)))) := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      rw [Finset.sum_add_distrib]
      refine add_le_add (le_trans (le_of_eq (hzeta h hh)) (hnAz' h hh)) ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hsum h hh) (by positivity)
    have hnum := fin_num2 d K H hd hK hH p hp0 hp1 ι hι'
    have : (H : ℝ) * (ε + 2 * b * Real.sqrt (K * (2 * d * Real.log (1 + (K : ℝ) / d)))) ≤
        100 * Real.sqrt ((d : ℝ) ^ 3 * (H : ℝ) ^ 3 * ((K : ℝ) * H) * ι ^ 2) := by
      rw [hε, hbd]; exact hnum
    exact absurd hω (not_lt.mpr (hregret.trans this))
  -- measure
  calc _ ≤ μ (c3Ev M φ b δ H K x a ∪ ⋃ h ∈ Finset.Icc 1 H,
        {ω | ε < azS M φ (fun _ => b) H K (fun τ i => x τ i ω) (fun τ i => a τ i ω) h}) :=
        measure_mono hsub
    _ ≤ μ (c3Ev M φ b δ H K x a) + μ (⋃ h ∈ Finset.Icc 1 H,
        {ω | ε < azS M φ (fun _ => b) H K (fun τ i => x τ i ω) (fun τ i => a τ i ω) h}) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal δ + ∑ h ∈ Finset.Icc 1 H, ENNReal.ofReal (p / (2 * H)) :=
        add_le_add hC3 ((measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hAz))
    _ = ENNReal.ofReal p := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_add hδ0.le (by positivity)]
        congr 1
        rw [hδ]; field_simp; ring


open LinearMDPRL.Linear MeasureTheory ProbabilityTheory in
theorem solution :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {S A : Type} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
        [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H K : ℕ), 1 ≤ d → 1 ≤ H → 1 ≤ K →
      ∀ (M : EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)), IsLinearMDP M H d φ →
      ∀ p : ℝ, 0 < p → p < 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) (x : ℕ → ℕ → Ω → S) (a : ℕ → ℕ → Ω → A),
        IsLSVIUCBRun μ 𝓕 M φ 1 (fun _ => c * d * H * Real.sqrt (iota d K H p)) H K x a →
        μ {ω | C * Real.sqrt ((d : ℝ) ^ 3 * (H : ℝ) ^ 3 * ((K : ℝ) * H) * iota d K H p ^ 2) <
            regret M φ 1 (fun _ => c * d * H * Real.sqrt (iota d K H p)) H K
              (fun τ i => x τ i ω) (fun τ i => a τ i ω)}
          ≤ ENNReal.ofReal p := by
  exact lsvi_ucb_regret_final
