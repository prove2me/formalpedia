-- Prove2me | solution 1 for LinParamBandits.LowerBound.min_directional_risk
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:45:49.374784+00:00
-- url     : https://prove2.me/submissions/81c24fea-cc2a-47cf-980c-12a3daa0cf3f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LinParamBandits_LowerBound_Model
import Theorems.Thm_LinParamBandits_LowerBound_estimation_error
import Theorems.Thm_LinParamBandits_LowerBound_norm_prob_bound
import Theorems.Thm_LinParamBandits_LowerBound_posterior_direction_tail

open MeasureTheory ProbabilityTheory

namespace LPB25Aux

lemma exp_neg_le_poly (u : ℝ) (hu : 0 ≤ u) : Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  have h := Real.quadratic_le_exp_of_nonneg hu
  have hp : 0 ≤ 1 - u + u ^ 2 / 2 := by nlinarith [sq_nonneg (u - 1)]
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos u)]
  have := mul_le_mul_of_nonneg_right h hp
  nlinarith [sq_nonneg (u ^ 2)]

lemma gaussianReal_real_eq (s : Set ℝ) :
    (gaussianReal 0 1).real s = ∫ x in s, gaussianPDFReal 0 1 x := by
  rw [measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero, ENNReal.toReal_ofReal]
  exact setIntegral_nonneg_of_ae (Filter.Eventually.of_forall (fun x => gaussianPDFReal_nonneg _ _ x))

lemma pdf_eq (x : ℝ) : gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

/-- `2 (1 - Φ(√(1/2))) ≥ 0.475`. -/
lemma gauss_tail : (0.475 : ℝ) ≤ 2 * (1 - cdf (gaussianReal 0 1) (Real.sqrt 0.5)) := by
  set a := Real.sqrt 0.5 with ha
  set c := (Real.sqrt (2 * Real.pi))⁻¹ with hc
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by norm_num)
  have ha2 : a ^ 2 = 0.5 := Real.sq_sqrt (by norm_num)
  rw [cdf_eq_real]
  have hcompl : 1 - (gaussianReal 0 1).real (Set.Iic a) = (gaussianReal 0 1).real (Set.Ioi a) := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  rw [hcompl]
  have hsplit : (gaussianReal 0 1).real (Set.Ioi 0)
      = (gaussianReal 0 1).real (Set.Ioc 0 a) + (gaussianReal 0 1).real (Set.Ioi a) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi ha0.le, measureReal_union _ measurableSet_Ioi]
    exact Set.Ioc_disjoint_Ioi le_rfl
  have hhalf : (gaussianReal 0 1).real (Set.Ioi 0) = 1 / 2 := by
    rw [gaussianReal_real_eq]
    simp_rw [pdf_eq]
    rw [integral_const_mul, integral_gaussian_Ioi]
    have hpi := Real.pi_pos
    rw [show Real.pi / (1 / 2) = 2 * Real.pi by ring]
    have : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp
  have hIoc : (gaussianReal 0 1).real (Set.Ioc 0 a) ≤ c * (a - a ^ 3 / 6 + a ^ 5 / 40) := by
    rw [gaussianReal_real_eq]
    have hc0 : 0 ≤ c := by positivity
    calc ∫ x in Set.Ioc 0 a, gaussianPDFReal 0 1 x
        ≤ ∫ x in Set.Ioc 0 a, c * (1 - x ^ 2 / 2 + x ^ 4 / 8) := by
          refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc (fun x _ => ?_)
          · exact (integrable_gaussianPDFReal 0 1).integrableOn
          · exact (by fun_prop : Continuous fun x : ℝ => c * (1 - x ^ 2 / 2 + x ^ 4 / 8)).integrableOn_Ioc
          · rw [pdf_eq]
            refine mul_le_mul_of_nonneg_left ?_ hc0
            have := exp_neg_le_poly (x ^ 2 / 2) (by positivity)
            rw [show -(1 / 2) * x ^ 2 = -(x ^ 2 / 2) by ring]
            nlinarith
      _ = c * (a - a ^ 3 / 6 + a ^ 5 / 40) := by
          rw [← intervalIntegral.integral_of_le ha0.le]
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
            (f := fun x => c * (x - x ^ 3 / 6 + x ^ 5 / 40))]
          · ring
          · intro x _
            refine HasDerivAt.const_mul c ?_
            have h3 := (hasDerivAt_pow 3 x).div_const (6 : ℝ)
            have h5 := (hasDerivAt_pow 5 x).div_const (40 : ℝ)
            have := ((hasDerivAt_id' x).sub h3).add h5
            refine this.congr_deriv ?_
            norm_num
            ring
          · exact (by fun_prop : Continuous fun x : ℝ => c * (1 - x ^ 2 / 2 + x ^ 4 / 8)).intervalIntegrable _ _
  -- numerics
  have hpi := Real.pi_gt_d6
  have hs : (2.5066 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hspos : 0 < Real.sqrt (2 * Real.pi) := by linarith
  have hale : a ≤ 0.7072 := by
    rw [ha, Real.sqrt_le_left (by norm_num)]; norm_num
  have hpoly : a - a ^ 3 / 6 + a ^ 5 / 40 = a * (443 / 480) := by
    have h3 : a ^ 3 = a * a ^ 2 := by ring
    have h5 : a ^ 5 = a * (a ^ 2) ^ 2 := by ring
    rw [h3, h5, ha2]; ring
  rw [hpoly] at hIoc
  have hca : c * (a * (443 / 480)) ≤ 0.2625 := by
    rw [hc, inv_mul_le_iff₀ hspos]
    nlinarith
  linarith

open LinParamBandits.LowerBound

lemma measurable_snoc_pair {r t : ℕ} {X : Type*} [MeasurableSpace X] {f : X → History r t}
    {a : X → Vec r × ℝ} (hf : Measurable f) (ha : Measurable a) :
    Measurable (fun x => (Fin.snoc (α := fun _ => Vec r × ℝ) (f x) (a x) : History r (t + 1))) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using ha
  · simpa using (show Measurable (fun x => f x j) from (measurable_pi_apply j).comp hf)

lemma hist_measurable {r : ℕ} (ψ : SpherePolicy r) (t : ℕ) :
    Measurable (fun ω : Ω r => hist ψ ω.1 ω.2 t) := by
  induction t with
  | zero => simp only [hist]; exact measurable_const
  | succ t ih =>
    simp only [hist]
    have h1 : Measurable (fun ω : Ω r => ψ.act t (hist ψ ω.1 ω.2 t)) :=
      (ψ.measurable_act t).comp ih
    refine measurable_snoc_pair ih (h1.prodMk ?_)
    exact (h1.inner measurable_fst).add ((measurable_pi_apply t).comp measurable_snd)


lemma key_real (s T' z Ξ Γ Θ r : ℝ) (hs : 0 < s) (hsT : s ^ 2 = T') (hr : 0 < r) (hrs : r ≤ s)
    (hz1 : 0.09 ≤ z) (hz2 : z ≤ 3) (hΞ : 0 ≤ Ξ) (hΓ : 0 ≤ Γ) (hb : 0.5 * Θ ≤ Γ)
    (h23 : 1 / (r + Ξ) ≤ Θ) : s / 12 ≤ z * Ξ + T' / z * Γ := by
  have hzpos : 0 < z := by linarith
  have hT0 : 0 ≤ T' := by rw [← hsT]; positivity
  have h2nd : 0 ≤ T' / z * Γ := by positivity
  have h1st : 0 ≤ z * Ξ := by positivity
  rcases le_or_gt s Ξ with hx | hx
  · have : 0.09 * s ≤ z * Ξ := mul_le_mul hz1 hx hs.le hzpos.le
    linarith
  · have hden : 0 < r + Ξ := by linarith
    have hΘlow : 1 / (2 * s) ≤ Θ := le_trans (one_div_le_one_div_of_le hden (by linarith)) h23
    have hΓlow : 1 / (4 * s) ≤ Γ := by
      have : 1 / (4 * s) = 0.5 * (1 / (2 * s)) := by field_simp; norm_num
      rw [this]; linarith
    have hTz : T' / 3 ≤ T' / z := div_le_div_of_nonneg_left hT0 hzpos hz2
    have hmain : T' / 3 * (1 / (4 * s)) ≤ T' / z * Γ :=
      mul_le_mul hTz hΓlow (by positivity) (by positivity)
    have heq : T' / 3 * (1 / (4 * s)) = s / 12 := by
      rw [← hsT]; field_simp; ring
    linarith

end LPB25Aux

open LinParamBandits.LowerBound LPB25Aux in
theorem solution (r : ℕ) (hr : 2 ≤ r) (ψ : SpherePolicy r) (T : ℕ) (hT : r ^ 2 ≤ T)
    (S : Fin (r - 1) → History r T → Vec r)
    (hS_meas : ∀ k, Measurable (S k))
    (hS_orth : ∀ h, Orthonormal ℝ (fun k => S k h))
    (hS_perp : ∀ᵐ ω ∂(P r), ∀ k, inner ℝ (S k (hist ψ ω.1 ω.2 T)) (zhat ψ T ω) = 0)
    (k : Fin (r - 1)) :
    ENNReal.ofReal (0.027 * Real.sqrt T)
      ≤ ∫⁻ ω, ENNReal.ofReal
          (‖ω.1‖ * ∑ t ∈ Finset.range T, (inner ℝ (arm ψ ω.1 ω.2 t) (S k (hist ψ ω.1 ω.2 T))) ^ 2
            + (T : ℝ) / ‖ω.1‖ * (inner ℝ (ω.1 - zhat ψ T ω) (S k (hist ψ ω.1 ω.2 T))) ^ 2) ∂(P r) := by
  classical
  haveI : IsProbabilityMeasure (prior r) := by
    unfold prior; exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure noise := by unfold noise; infer_instance
  haveI : IsProbabilityMeasure (P r) := by unfold P; infer_instance
  have hT1 : 1 ≤ T := by nlinarith
  have hH := hist_measurable ψ T
  have hm : histSigma ψ T ≤ (inferInstance : MeasurableSpace (Ω r)) := hH.comap_le
  have hzhat : Measurable (zhat ψ T) := by
    have : StronglyMeasurable[histSigma ψ T] (zhat ψ T) := by
      unfold zhat; exact stronglyMeasurable_condExp
    exact (this.mono hm).measurable
  have hSk : Measurable (fun ω : Ω r => S k (hist ψ ω.1 ω.2 T)) := (hS_meas k).comp hH
  -- the three ingredients
  set Γ : Ω r → ℝ := fun ω => (inner ℝ (ω.1 - zhat ψ T ω) (S k (hist ψ ω.1 ω.2 T))) ^ 2 with hΓ
  set Θ : Ω r → ℝ := (P r)[Γ | histSigma ψ T] with hΘ
  set Ξ : Ω r → ℝ := fun ω =>
    ∑ t ∈ Finset.range T, (inner ℝ (arm ψ ω.1 ω.2 t) (S k (hist ψ ω.1 ω.2 T))) ^ 2 with hΞ
  have h23 : ∀ᵐ ω ∂(P r), 1 / ((r : ℝ) + Ξ ω) ≤ Θ ω :=
    estimation_error r hr ψ T hT1 S hS_meas hS_orth hS_perp k
  have hBc := posterior_direction_tail r hr ψ T hT1 S hS_meas hS_orth hS_perp k 0.5 (by norm_num)
  have h24 := norm_prob_bound r hr 0.09 3 (by norm_num) (by norm_num)
  -- the events
  set A0 : Set (Vec r) := {z | 0.09 ≤ ‖z‖ ∧ ‖z‖ ≤ 3} with hA0
  set A : Set (Ω r) := A0 ×ˢ Set.univ with hA
  set B : Set (Ω r) := {ω | 0.5 * Θ ω ≤ Γ ω} with hB
  have hΓm : Measurable Γ :=
    ((measurable_fst.sub hzhat).inner hSk).pow_const 2
  have hΘm : Measurable Θ := (stronglyMeasurable_condExp.mono hm).measurable
  have hA0m : MeasurableSet A0 :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hAm : MeasurableSet A := hA0m.prod MeasurableSet.univ
  have hBm : MeasurableSet B := measurableSet_le (hΘm.const_mul _) hΓm
  -- probabilities
  have hPA : (P r).real A = (prior r).real A0 := by
    rw [hA]; unfold P
    rw [measureReal_prod_prod, probReal_univ, mul_one]
  have hPB : (P r).real B = 2 * (1 - cdf (gaussianReal 0 1) (Real.sqrt 0.5)) := by
    have h1 : ∫ ω, (P r)[B.indicator (fun _ => (1 : ℝ)) | histSigma ψ T] ω ∂(P r)
        = ∫ ω, B.indicator (fun _ => (1 : ℝ)) ω ∂(P r) := integral_condExp hm
    rw [integral_indicator_const _ hBm, smul_eq_mul, mul_one] at h1
    rw [← h1, integral_congr_ae hBc]
    simp
  have hgt := gauss_tail
  have hAB : (P r).real A + (P r).real B - 1 ≤ (P r).real (A ∩ B) := by
    have := measureReal_union_add_inter (μ := P r) (s := A) hBm
    have h2 : (P r).real (A ∪ B) ≤ 1 := measureReal_le_one
    linarith
  -- pointwise bound on `A ∩ B`
  have hsq : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < T))
  have hsqT : Real.sqrt T ^ 2 = T := Real.sq_sqrt (Nat.cast_nonneg _)
  have hrle : (r : ℝ) ≤ Real.sqrt T := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast hT
  have hpt : ∀ᵐ ω ∂(P r), (A ∩ B).indicator (fun _ => ENNReal.ofReal (Real.sqrt T / 12)) ω
      ≤ ENNReal.ofReal (‖ω.1‖ * Ξ ω + (T : ℝ) / ‖ω.1‖ * Γ ω) := by
    filter_upwards [h23] with ω hω
    by_cases hin : ω ∈ A ∩ B
    · rw [Set.indicator_of_mem hin]
      apply ENNReal.ofReal_le_ofReal
      have hin' := hin
      simp only [hA, hB, hA0, Set.mem_inter_iff, Set.mem_prod, Set.mem_setOf_eq,
        Set.mem_univ, and_true] at hin'
      obtain ⟨⟨hz1, hz2⟩, hb⟩ := hin'
      exact key_real (Real.sqrt T) T ‖ω.1‖ (Ξ ω) (Γ ω) (Θ ω) r hsq hsqT
        (by exact_mod_cast (by omega : 0 < r)) hrle hz1 hz2
        (Finset.sum_nonneg (fun t _ => sq_nonneg _)) (sq_nonneg _) hb hω
    · rw [Set.indicator_of_notMem hin]; exact bot_le
  calc ENNReal.ofReal (0.027 * Real.sqrt T)
      ≤ ENNReal.ofReal (Real.sqrt T / 12 * (P r).real (A ∩ B)) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith
    _ = ENNReal.ofReal (Real.sqrt T / 12) * (P r) (A ∩ B) := by
        rw [ENNReal.ofReal_mul (by positivity), ofReal_measureReal]
    _ = ∫⁻ ω, (A ∩ B).indicator (fun _ => ENNReal.ofReal (Real.sqrt T / 12)) ω ∂(P r) :=
        (lintegral_indicator_const (hAm.inter hBm) _).symm
    _ ≤ _ := lintegral_mono_ae hpt
