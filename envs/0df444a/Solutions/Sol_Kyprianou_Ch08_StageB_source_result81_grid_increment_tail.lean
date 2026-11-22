-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_grid_increment_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:50:05.359992+00:00
-- url     : https://prove2.me/submissions/ae2303c2-0ff1-4738-94c0-9a47b3046a6a

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_positive_mgf
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (K : ℝ)
    (hK : ∀ b : ℝ, 1 ≤ b → tripletLaplace (-D.triplet.drift) D.gaussianCoefficient
      D.triplet.levyMeasure b ≤ K * b ^ 2)
    (s : ℝ≥0) (r : ℝ) (hr : 1 ≤ r) (d : ℝ≥0) (hd : (d : ℝ) = (r ^ 4)⁻¹) :
    P {ω | r⁻¹ ≤ D.X (s + d) ω - D.X s ω} ≤ ENNReal.ofReal (Real.exp (K - r)) := by
  let g : ℝ → ℝ := fun y => Real.exp (-r) * Real.exp (r ^ 2 * y)
  have hg : Measurable (fun y => ENNReal.ofReal (g y)) := by fun_prop
  have hi := (D.levy.stationary_increments s d).comp hg
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hb : 1 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have hm := source_result81_law_positive_mgf Ω P D d (r ^ 2) (by positivity)
  have htail (ω : Ω) (hω : r⁻¹ ≤ D.X (s + d) ω - D.X s ω) :
      1 ≤ ENNReal.ofReal (g (D.X (s + d) ω - D.X s ω)) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    dsimp [g]
    rw [← Real.exp_add, Real.one_le_exp_iff]
    have he := mul_le_mul_of_nonneg_left hω (sq_nonneg r)
    rw [show r ^ 2 * r⁻¹ = r by field_simp] at he
    linarith
  refine (meas_le_lintegral₀ hi.aemeasurable_fst htail).trans ?_
  rw [hi.lintegral_eq]
  change (∫⁻ ω, ENNReal.ofReal (g (D.X d ω - D.X 0 ω)) ∂P) ≤ _
  simp only [D.levy.start_zero, sub_zero]
  have hg0 : ∀ ω, 0 ≤ Real.exp (-r) * Real.exp (r ^ 2 * D.X d ω) := fun _ => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal (hm.1.const_mul _) (Eventually.of_forall hg0),
    integral_const_mul, hm.2, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr _)
  have h := mul_le_mul_of_nonneg_left (hK (r ^ 2) hb) d.coe_nonneg
  rw [show (d : ℝ) * (K * (r ^ 2) ^ 2) = K by rw [hd]; field_simp] at h
  linarith
