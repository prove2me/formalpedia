-- Prove2me | solution 1 for OAI.RieszRectifiability.schwartz_fractional_equation_of_real_pairing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:42.884263+00:00
-- url     : https://prove2.me/submissions/24e06b39-c5c8-4634-bc27-50c81c7ee578

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

variable [MetricSpace X]

omit [MeasurableSpace X] in
theorem fractionalPairEnergy_nonneg (m : ℕ) (w : X → ℝ) (x y : X) :
    0 ≤ fractionalPairEnergy m w x y := by
  unfold fractionalPairEnergy
  positivity

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FiniteStepLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-step functions in L²

Finite-step functions on finite measures belong to L². Products are represented on
intersections of cells, expressing squared distances through cell masses and mixed moments.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X ι κ : Type*} [MeasurableSpace X] [Fintype ι] [Fintype κ]

theorem toLp_norm_sq_eq_integral (μ : Measure X) (f : X → ℝ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_L2Pairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integral pairings of real L² functions

The L² inner product agrees with integration of pointwise products. Subtraction and
Cauchy–Schwarz then bound differences of pairings by squared L² errors.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem real_scalar_inner_mul (a b : ℝ) : inner ℝ a b = a * b := by
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  simp only [← pow_two, Real.norm_eq_abs, sq_abs]
  ring

theorem toLp_inner_eq_integral (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy, real_scalar_inner_mul]

theorem integral_mul_cauchy_schwarz_sq (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [toLp_norm_sq_eq_integral, toLp_norm_sq_eq_integral] at h
  simpa only [toLp_inner_eq_integral, pow_two] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BallLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localization to balls

Restricting a measure preserves its global upper growth bound and gives finite mass on
positive-radius balls. The diameter estimate controls pairs of points in a ball, while
the Lipschitz height estimate supplies the boundedness needed for local `MemLp` control.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem globalGrowth_restrict {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (s : Set (Ambient d)) :
    GlobalUpperGrowth m C (μ.restrict s) := by
  refine ⟨hg.1, fun a R hR => ?_⟩
  exact (Measure.restrict_le_self (s := s) (μ := μ) (ball a R)).trans (hg.2 a R hR)

theorem finiteMeasure_restrict_ball_of_globalGrowth {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) : IsFiniteMeasure (μ.restrict (ball a R)) := by
  constructor
  simpa only [Measure.restrict_apply_univ] using! (hg.2 a R hR).trans_lt ENNReal.ofReal_lt_top

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NearPairWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem nearPairSet_measurable {d : ℕ} (r : ℝ) :
    MeasurableSet (nearPairSet (d := d) r) :=
  measurableSet_le (continuous_snd.dist continuous_fst).measurable measurable_const

theorem nearPairWeight_measurable {d : ℕ} (p : ℕ) (r : ℝ) :
    Measurable (nearPairWeight (d := d) p r) := by
  apply Measurable.indicator _ (nearPairSet_measurable r)
  unfold inverseDistancePow
  fun_prop

theorem nearPairWeight_nonneg {d : ℕ} (p : ℕ) (r : ℝ) (q : Ambient d × Ambient d) :
    0 ≤ nearPairWeight p r q :=
  indicator_nonneg (fun _ _ => inverseDistancePow_nonneg p _ _) q

theorem nearPairWeight_section {d : ℕ} (p : ℕ) (r : ℝ) (x : Ambient d) :
    (fun y => nearPairWeight p r (x, y)) =
      (closedBall x r).indicator (inverseDistancePow p x) := by
  funext y
  classical
  by_cases h : y ∈ closedBall x r
  · simp only [nearPairWeight, indicator_of_mem (show (x, y) ∈ nearPairSet r from h),
      indicator_of_mem h]
  · simp only [nearPairWeight, indicator_of_notMem (show (x, y) ∉ nearPairSet r from h),
      indicator_of_notMem h]

theorem nearPairWeight_section_integrable {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ)
    (r : ℝ) (hr : 0 < r) (x : Ambient d) :
    Integrable (fun y => nearPairWeight p r (x, y)) μ := by
  rw [nearPairWeight_section]
  exact (integrable_indicator_iff measurableSet_closedBall).mpr
    (inverseDistancePow_near_integrable_and_bound p C μ hg x r hr).1

theorem nearPairWeight_section_norm_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ)
    (r : ℝ) (hr : 0 < r) (x : Ambient d) :
    (∫ y, ‖nearPairWeight p r (x, y)‖ ∂μ) ≤ 2 * (C * 2 ^ (p + 1) * 2 ^ p * r) := by
  simp_rw [Real.norm_of_nonneg (nearPairWeight_nonneg p r _)]
  rw [nearPairWeight_section, integral_indicator measurableSet_closedBall]
  exact inverseDistancePow_near_integral_bound p C μ hg x r hr

theorem nearPairWeight_integrable {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (r : ℝ) (hr : 0 < r) : Integrable (nearPairWeight p r) (μ.prod μ) := by
  have hmeas : AEStronglyMeasurable (nearPairWeight p r) (μ.prod μ) :=
    (nearPairWeight_measurable p r).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).mpr
  refine ⟨Filter.Eventually.of_forall (nearPairWeight_section_integrable p C μ hg r hr), ?_⟩
  apply Integrable.of_bound hmeas.norm.integral_prod_right' (2 * (C * 2 ^ (p + 1) * 2 ^ p * r))
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact nearPairWeight_section_norm_bound p C μ hg r hr x

theorem nearPairWeight_integral_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (r : ℝ) (hr : 0 < r) :
    (∫ q, nearPairWeight p r q ∂μ.prod μ) ≤
      μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) := by
  have hi := nearPairWeight_integrable p C μ hg r hr
  rw [integral_prod _ hi]
  have h := integral_mono hi.integral_prod_left
    (integrable_const (2 * (C * 2 ^ (p + 1) * 2 ^ p * r))) (fun x => by
      simpa only [Real.norm_of_nonneg (nearPairWeight_nonneg p r _)] using!
        nearPairWeight_section_norm_bound p C μ hg r hr x)
  simpa only [integral_const, smul_eq_mul] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function
open scoped NNReal

variable {d : ℕ}

theorem weightedDifference_measurable (m : ℕ) (w : Ambient d → ℝ) (hw : Measurable w) :
    Measurable (fun q : Ambient d × Ambient d => weightedDifference m w q.1 q.2) := by
  unfold weightedDifference
  fun_prop

theorem weightedDifference_sq (m : ℕ) (w : Ambient d → ℝ) (x y : Ambient d) :
    weightedDifference m w x y ^ 2 = fractionalPairEnergy m w x y := by
  rw [weightedDifference, div_pow, Real.sq_sqrt (pow_nonneg dist_nonneg _)]
  rfl

theorem weightedDifference_mul (m : ℕ) (w ψ : Ambient d → ℝ) (x y : Ambient d) :
    weightedDifference m w x y * weightedDifference m ψ x y = fractionalBilinear m w ψ x y := by
  rw [weightedDifference, weightedDifference, div_mul_div_comm, ← pow_two,
    Real.sq_sqrt (pow_nonneg dist_nonneg _)]
  rfl

theorem lipschitz_fractionalEnergy_bound (p : ℕ) (ψ : Ambient d → ℝ)
    (L : ℝ≥0) (hψ : LipschitzWith L ψ) (x y : Ambient d) :
    fractionalPairEnergy (p + 1) ψ x y ≤ (L : ℝ) ^ 2 * (dist x y ^ p)⁻¹ := by
  by_cases hxy : x = y
  · subst y
    simp only [fractionalPairEnergy, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]
    positivity
  · have hd : 0 < dist x y := dist_pos.mpr hxy
    have hdiff : |ψ x - ψ y| ≤ (L : ℝ) * dist x y := by
      simpa only [Real.dist_eq] using! hψ.dist_le_mul x y
    have hsq : (ψ x - ψ y) ^ 2 ≤ (L : ℝ) ^ 2 * dist x y ^ 2 := by
      simpa only [sq_abs, mul_pow] using!
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg L.coe_nonneg dist_nonneg)).mpr hdiff
    calc
      _ ≤ ((L : ℝ) ^ 2 * dist x y ^ 2) / dist x y ^ (p + 1 + 1) :=
        div_le_div_of_nonneg_right hsq (pow_nonneg dist_nonneg _)
      _ = _ := by
        rw [show p + 1 + 1 = p + 2 by omega, pow_add]
        field_simp

theorem weightedDifference_memLp (m : ℕ) (w : Ambient d → ℝ) (hw : Measurable w)
    (ρ : Measure (Ambient d × Ambient d))
    (hE : Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m w q.1 q.2) ρ) :
    MemLp (fun q : Ambient d × Ambient d => weightedDifference m w q.1 q.2) 2 ρ := by
  apply (memLp_two_iff_integrable_sq (weightedDifference_measurable m w hw).aestronglyMeasurable).mpr
  simpa only [weightedDifference_sq] using! hE

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NearBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Near-diagonal fractional bilinear bounds

On the near-pair region, Lipschitz control makes the test function's fractional energy
integrable under upper growth. Cauchy–Schwarz then bounds the absolute bilinear pairing
by the full energy of the other function and the near-pair inverse-distance integral.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem near_fractionalBilinear_integrable_and_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w ψ : Ambient d → ℝ) (hw : Measurable w) (L : ℝ≥0) (hψ : LipschitzWith L ψ)
    (henergy : Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) w q.1 q.2) (μ.prod μ))
    (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) w ψ q.1 q.2)
      (nearPairSet r) (μ.prod μ) ∧
      (∫ q in nearPairSet r, |fractionalBilinear (p + 1) w ψ q.1 q.2| ∂μ.prod μ) ^ 2 ≤
        (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) w q.1 q.2 ∂μ.prod μ) *
          ((L : ℝ) ^ 2 * (μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)))) := by
  let ρ : Measure (Ambient d × Ambient d) := (μ.prod μ).restrict (nearPairSet r)
  have hweak : Integrable (fun q : Ambient d × Ambient d => inverseDistancePow p q.1 q.2) ρ :=
    (integrable_indicator_iff (nearPairSet_measurable r)).mp
      (nearPairWeight_integrable p C μ hg r hr)
  have htestMeas : AEStronglyMeasurable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) ψ q.1 q.2) ρ := by
    have hψm : Measurable ψ := hψ.continuous.measurable
    apply Measurable.aestronglyMeasurable
    unfold fractionalPairEnergy
    fun_prop
  have htestEnergy : Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) ψ q.1 q.2) ρ := by
    apply (hweak.const_mul ((L : ℝ) ^ 2)).mono' htestMeas
    apply Filter.Eventually.of_forall
    intro q
    rw [Real.norm_of_nonneg (fractionalPairEnergy_nonneg _ _ _ _)]
    exact lipschitz_fractionalEnergy_bound p ψ L hψ q.1 q.2
  have hf := weightedDifference_memLp (p + 1) w hw ρ henergy.restrict
  have hgtest := weightedDifference_memLp (p + 1) ψ hψ.continuous.measurable ρ htestEnergy
  have hprod : MemLp (fun q : Ambient d × Ambient d =>
      weightedDifference (p + 1) w q.1 q.2 * weightedDifference (p + 1) ψ q.1 q.2) 1 ρ :=
    MemLp.mul' (hφ := hf) (hf := hgtest)
  have hcs := integral_mul_cauchy_schwarz_sq ρ
    (fun q => ‖weightedDifference (p + 1) w q.1 q.2‖)
    (fun q => ‖weightedDifference (p + 1) ψ q.1 q.2‖) hf.norm hgtest.norm
  simp only [Real.norm_eq_abs, ← abs_mul, weightedDifference_mul, sq_abs,
    weightedDifference_sq] at hcs
  have hwork : (∫ q, fractionalPairEnergy (p + 1) w q.1 q.2 ∂ρ) ≤
      ∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) w q.1 q.2 ∂μ.prod μ :=
    setIntegral_le_integral henergy
      (Filter.Eventually.of_forall fun q => fractionalPairEnergy_nonneg _ _ _ _)
  have hweakBound : (∫ q, inverseDistancePow p q.1 q.2 ∂ρ) ≤
      μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) := by
    change (∫ q in nearPairSet r, inverseDistancePow p q.1 q.2 ∂μ.prod μ) ≤ _
    rw [← integral_indicator (nearPairSet_measurable r)]
    exact nearPairWeight_integral_bound p C μ hg r hr
  have htestBound : (∫ q, fractionalPairEnergy (p + 1) ψ q.1 q.2 ∂ρ) ≤
      (L : ℝ) ^ 2 * (μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r))) := by
    have h := integral_mono htestEnergy (hweak.const_mul ((L : ℝ) ^ 2))
      (fun q => lipschitz_fractionalEnergy_bound p ψ L hψ q.1 q.2)
    rw [integral_const_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left hweakBound (sq_nonneg _))
  refine ⟨?_, ?_⟩
  · simpa only [weightedDifference_mul] using! memLp_one_iff_integrable.mp hprod
  · exact hcs.trans (mul_le_mul hwork htestBound
      (integral_nonneg (fun q => fractionalPairEnergy_nonneg _ _ _ _))
      (integral_nonneg (fun q => fractionalPairEnergy_nonneg _ _ _ _)))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FarKernelDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem inverseDistancePow_far_difference {d : ℕ} (m : ℕ) (a x y : Ambient d)
    (hy : 0 < dist a y) (hfar : 2 * dist x a ≤ dist a y) :
    |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y| ≤
      (m + 1 : ℝ) * 2 ^ (m + 2) * dist x a * inverseDistancePow (m + 2) a y := by
  have hhalf : dist a y / 2 ≤ dist x y := by
    have ht := dist_triangle a x y
    rw [dist_comm a x] at ht
    linarith
  have h := inverse_pow_difference_le m (dist x y) (dist a y) (dist a y / 2)
    (by positivity) hhalf (by linarith)
  have hdist := abs_dist_sub_le x a y
  unfold inverseDistancePow
  calc
    _ ≤ (m + 1 : ℝ) * |dist x y - dist a y| * ((dist a y / 2) ^ (m + 2))⁻¹ := h
    _ ≤ (m + 1 : ℝ) * dist x a * ((dist a y / 2) ^ (m + 2))⁻¹ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdist (by positivity))
        (by positivity)
    _ = _ := by
      rw [div_pow, inv_div]
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LipschitzTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

theorem lipschitz_bounded_product_real {f g : X → ℝ} {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, |f x| ≤ (Bf : ℝ)) (hBg : ∀ x, |g x| ≤ (Bg : ℝ)) :
    LipschitzWith (Bf * Kg + Kf * Bg) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hf' : |f x - f y| ≤ (Kf : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using! hf.dist_le_mul x y
  have hg' : |g x - g y| ≤ (Kg : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using! hg.dist_le_mul x y
  calc
    dist (f x * g x) (f y * g y) =
        |f x * (g x - g y) + (f x - f y) * g y| := by
      rw [Real.dist_eq]
      congr 1
      ring
    _ ≤ |f x| * |g x - g y| + |f x - f y| * |g y| := by
      simpa only [abs_mul] using! abs_add_le
        (f x * (g x - g y)) ((f x - f y) * g y)
    _ ≤ (Bf : ℝ) * ((Kg : ℝ) * dist x y) +
        ((Kf : ℝ) * dist x y) * (Bg : ℝ) := by
      exact add_le_add (mul_le_mul (hBf x) hg' (abs_nonneg _) (by positivity))
        (mul_le_mul hf' (hBg y) (abs_nonneg _) (by positivity))
    _ = ((Bf * Kg + Kf * Bg : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_add, NNReal.coe_mul]
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedBilinearKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set Function
open scoped NNReal

theorem cappedInverseDistancePow_eq {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (q : X × X) (h : ε ≤ dist q.1 q.2) :
    cappedInverseDistancePow m ε q = (dist q.1 q.2 ^ m)⁻¹ := by
  simp only [cappedInverseDistancePow, max_eq_right h]

theorem cappedInverseDistancePow_swap {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (q : X × X) :
    cappedInverseDistancePow m ε q.swap = cappedInverseDistancePow m ε q := by
  simp only [cappedInverseDistancePow, Prod.swap, dist_comm]

theorem cappedTestKernel_bound {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (φ : Ambient d → ℝ) (B : ℝ≥0) (hB : ∀ x, |φ x| ≤ (B : ℝ))
    (q : Ambient d × Ambient d) :
    |cappedTestKernel m ε φ q| ≤ (2 * (B : ℝ)) * (ε ^ (m + 1))⁻¹ := by
  unfold cappedTestKernel
  rw [abs_mul]
  have hd : |φ q.1 - φ q.2| ≤ 2 * (B : ℝ) := by
    have h := abs_sub_le (φ q.1) 0 (φ q.2)
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith [hB q.1, hB q.2]
  exact mul_le_mul hd (cappedInverseDistancePow_bound (m + 1) ε hε q) (abs_nonneg _) (by positivity)

theorem cappedTestKernel_lipschitz {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (φ : Ambient d → ℝ) (L B : ℝ≥0) (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ)) :
    LipschitzWith
      ((2 * B) * Real.toNNReal (2 * (m + 1 : ℝ) * (ε ^ (m + 2))⁻¹) +
        (L + L) * Real.toNNReal ((ε ^ (m + 1))⁻¹)) (cappedTestKernel m ε φ) := by
  have hdiff : LipschitzWith (L + L) (fun q : Ambient d × Ambient d => φ q.1 - φ q.2) := by
    simpa only [mul_one] using! (hφ.comp LipschitzWith.prod_fst).sub (hφ.comp LipschitzWith.prod_snd)
  apply lipschitz_bounded_product_real hdiff (cappedInverseDistancePow_lipschitz m ε hε)
  · intro q
    have h := abs_sub_le (φ q.1) 0 (φ q.2)
    simp only [sub_zero, zero_sub, abs_neg] at h
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    linarith [hB q.1, hB q.2]
  · intro q
    exact (cappedInverseDistancePow_bound (m + 1) ε hε q).trans (Real.le_coe_toNNReal _)

theorem cappedTestKernel_antisymm {d : ℕ} (m : ℕ) (ε : ℝ) (φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) : cappedTestKernel m ε φ q.swap = -cappedTestKernel m ε φ q := by
  unfold cappedTestKernel
  rw [cappedInverseDistancePow_swap]
  dsimp only [Prod.swap]
  ring

theorem capped_bilinear_eq_outside {d : ℕ} (m : ℕ) (ε : ℝ) (w φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) (h : ε ≤ dist q.1 q.2) :
    (w q.1 - w q.2) * cappedTestKernel m ε φ q = fractionalBilinear m w φ q.1 q.2 := by
  unfold cappedTestKernel fractionalBilinear
  rw [cappedInverseDistancePow_eq _ _ _ h]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ClosedTailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem closedExterior_measurable {d : ℕ} (a : Ambient d) (R : ℝ) :
    MeasurableSet (closedExterior a R) :=
  measurableSet_le measurable_const (continuous_const.dist continuous_id).measurable

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RenormalizedFarPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem inverseDistancePow_far_le {d : ℕ} (p : ℕ) (a x y : Ambient d)
    (hy : 0 < dist a y) (hfar : 2 * dist x a ≤ dist a y) :
    inverseDistancePow p x y ≤ 2 ^ p * inverseDistancePow p a y := by
  have hhalf : dist a y / 2 ≤ dist x y := by
    have ht := dist_triangle a x y
    rw [dist_comm a x] at ht
    linarith
  calc
    _ ≤ ((dist a y / 2) ^ p)⁻¹ := by
      simpa only [inverseDistancePow, one_div] using!
        one_div_le_one_div_of_le (pow_pos (by positivity : 0 < dist a y / 2) p)
          (pow_le_pow_left₀ (by positivity) hhalf p)
    _ = _ := by unfold inverseDistancePow; rw [div_pow, inv_div]; ring

theorem renormalizedNormalIntegrand_bound {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (a x y : Ambient d) (H R : ℝ) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hx : dist x a ≤ H) (hy : R ≤ dist a y) :
    |renormalizedNormalIntegrand m w φ a (x, y)| ≤
      2 ^ (m + 1) * (|φ x * w x| * inverseDistancePow (m + 1) a y) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          (|φ x| * (|w y| * inverseDistancePow (m + 2) a y)) := by
  have hpos : 0 < dist a y := lt_of_lt_of_le hR hy
  have hfar : 2 * dist x a ≤ dist a y := (by linarith : 2 * dist x a ≤ R).trans hy
  have hk := inverseDistancePow_far_le (m + 1) a x y hpos hfar
  have hdiff : |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y| ≤
      (m + 1 : ℝ) * 2 ^ (m + 2) * H * inverseDistancePow (m + 2) a y := by
    apply (inverseDistancePow_far_difference m a x y hpos hfar).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by positivity))
      (inverseDistancePow_nonneg _ _ _)
  unfold renormalizedNormalIntegrand
  rw [abs_mul]
  calc
    _ ≤ |φ x| * (|w x| * inverseDistancePow (m + 1) x y +
        |w y| * |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y|) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [sub_zero, zero_sub, abs_neg, abs_mul,
        abs_of_nonneg (inverseDistancePow_nonneg _ _ _)] using!
        abs_sub_le (w x * inverseDistancePow (m + 1) x y) 0
          (w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y))
    _ ≤ |φ x| * (|w x| * (2 ^ (m + 1) * inverseDistancePow (m + 1) a y) +
        |w y| * ((m + 1 : ℝ) * 2 ^ (m + 2) * H * inverseDistancePow (m + 2) a y)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hk (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hdiff (abs_nonneg _))) (abs_nonneg _)
    _ = _ := by rw [abs_mul]; ring

theorem renormalizedNormalIntegrand_bound_of_support {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (a x y : Ambient d) (H R : ℝ) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hx : φ x ≠ 0 → dist x a ≤ H) (hy : R ≤ dist a y) :
    |renormalizedNormalIntegrand m w φ a (x, y)| ≤
      2 ^ (m + 1) * (|φ x * w x| * inverseDistancePow (m + 1) a y) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          (|φ x| * (|w y| * inverseDistancePow (m + 2) a y)) := by
  by_cases hφ : φ x = 0
  · simp only [renormalizedNormalIntegrand, hφ, zero_mul, abs_zero, mul_zero, add_zero, le_refl]
  · exact renormalizedNormalIntegrand_bound m w φ a x y H R hR hHR (hx hφ) hy

theorem renormalized_far_pairing_integrable_and_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasure ν]
    (hg : GlobalUpperGrowth m C μ) (w φ : Ambient d → ℝ)
    (hw : Measurable w) (hφm : Measurable φ) (hφ : Integrable φ ν)
    (hφw : Integrable (fun x => φ x * w x) ν)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hnear : ∀ᵐ x ∂ν, φ x ≠ 0 → dist x a ≤ H)
    (hweighted : IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ)
    (Z : ℝ) (hZ : (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤ Z) :
    Integrable (renormalizedNormalIntegrand m w φ a) (ν.prod (μ.restrict (closedExterior a R))) ∧
      (∫ q, |renormalizedNormalIntegrand m w φ a q| ∂ν.prod (μ.restrict (closedExterior a R))) ≤
        2 ^ (m + 1) * ((∫ x, |φ x * w x| ∂ν) * (2 * (C * 2 ^ m / R))) +
          ((m + 1 : ℝ) * 2 ^ (m + 2) * H) * ((∫ x, |φ x| ∂ν) * Z) := by
  let η := μ.restrict (closedExterior a R)
  obtain ⟨hkernel, hkernelBound⟩ := inverseDistancePow_closedExterior_integrable_and_bound m C μ hg a R hR
  have hdom₁ := (hφw.abs.mul_prod hkernel).const_mul ((2 : ℝ) ^ (m + 1))
  have hdom₂ := (hφ.abs.mul_prod hweighted).const_mul ((m + 1 : ℝ) * 2 ^ (m + 2) * H)
  have hm : Measurable (renormalizedNormalIntegrand m w φ a) := by
    unfold renormalizedNormalIntegrand inverseDistancePow
    fun_prop
  have hpoint : ∀ᵐ q ∂ν.prod η, |renormalizedNormalIntegrand m w φ a q| ≤
      2 ^ (m + 1) * (|φ q.1 * w q.1| * inverseDistancePow (m + 1) a q.2) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          (|φ q.1| * (|w q.2| * inverseDistancePow (m + 2) a q.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hnear,
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (closedExterior_measurable a R))] with q hx hy
    exact renormalizedNormalIntegrand_bound_of_support m w φ a q.1 q.2 H R hR hHR hx hy
  have hi : Integrable (renormalizedNormalIntegrand m w φ a) (ν.prod η) := by
    apply (hdom₁.add hdom₂).mono' hm.aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using! hpoint
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ q, 2 ^ (m + 1) * (|φ q.1 * w q.1| * inverseDistancePow (m + 1) a q.2) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          (|φ q.1| * (|w q.2| * inverseDistancePow (m + 2) a q.2)) ∂ν.prod η :=
      integral_mono_ae hi.abs (hdom₁.add hdom₂) hpoint
    _ = 2 ^ (m + 1) * ((∫ x, |φ x * w x| ∂ν) * (∫ y, inverseDistancePow (m + 1) a y ∂η)) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          ((∫ x, |φ x| ∂ν) * (∫ y, |w y| * inverseDistancePow (m + 2) a y ∂η)) := by
      rw [integral_add hdom₁ hdom₂]
      simp only [integral_const_mul]
      rw [integral_prod_mul (fun x => |φ x * w x|) (inverseDistancePow (m + 1) a),
        integral_prod_mul (fun x => |φ x|) (fun y => |w y| * inverseDistancePow (m + 2) a y)]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hkernelBound (integral_nonneg fun _ => abs_nonneg _)) (by positivity))
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hZ (integral_nonneg fun _ => abs_nonneg _)) (by positivity))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_SignedKernelConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergence of signed weighted kernel integrals

Finite step approximations in the second variable reduce weighted product
integrals to sums of weighted moments and cell masses. Integrable absolute
weights and Lipschitz kernel bounds control the approximation error, allowing
convergence of these finite sums to pass to the original kernel integrals.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem integrable_weighted_product_kernel (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure ν] (w : X → ℝ) (hw : Integrable w μ)
    (F : X × Y → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ q, |F q| ≤ B) :
    Integrable (fun q : X × Y => w q.1 * F q) (μ.prod ν) := by
  have hdom := (hw.abs.mul_prod (integrable_const (μ := ν) (1 : ℝ))).mul_const B
  apply hdom.mono' (hw.aestronglyMeasurable.comp_fst.mul hF.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro q
  change ‖w q.1 * F q‖ ≤ (|w q.1| * 1) * B
  rw [Real.norm_eq_abs, abs_mul, mul_one]
  exact mul_le_mul_of_nonneg_left (hB q) (abs_nonneg (w q.1))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CappedBilinearConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem antisymmetric_kernel_pairing {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (w : X → ℝ) (hw : Integrable w μ)
    (F : X × X → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ q, |F q| ≤ B)
    (hanti : ∀ q, F q.swap = -F q) :
    Integrable (fun q : X × X => (w q.1 - w q.2) * F q) (μ.prod μ) ∧
      (∫ q : X × X, (w q.1 - w q.2) * F q ∂μ.prod μ) =
        2 * ∫ q : X × X, w q.1 * F q ∂μ.prod μ := by
  have hi := integrable_weighted_product_kernel μ μ w hw F hF B hB
  have hswap : Integrable (fun q : X × X => w q.2 * F q.swap) (μ.prod μ) := hi.swap
  have heq : (fun q : X × X => (w q.1 - w q.2) * F q) =
      fun q => w q.1 * F q + w q.2 * F q.swap := by
    funext q
    rw [hanti q]
    ring
  refine ⟨heq ▸ hi.add hswap, ?_⟩
  rw [heq, integral_add hi hswap]
  have hswapInt : (∫ q : X × X, w q.2 * F q.swap ∂μ.prod μ) =
      ∫ q : X × X, w q.1 * F q ∂μ.prod μ :=
    integral_prod_swap (fun q : X × X => w q.1 * F q)
  rw [hswapInt]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedBilinearError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem capped_bilinear_error_pointwise {d : ℕ} (m : ℕ) (ε : ℝ)
    (w φ : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    |fractionalBilinear m w φ q.1 q.2 - (w q.1 - w q.2) * cappedTestKernel m ε φ q| ≤
      (nearPairSet ε).indicator (fun q => |fractionalBilinear m w φ q.1 q.2|) q := by
  classical
  by_cases hnear : q ∈ nearPairSet ε
  · rw [indicator_of_mem hnear]
    by_cases hdiag : q.1 = q.2
    · simp only [hdiag, fractionalBilinear, cappedTestKernel, sub_self, zero_mul, zero_div,
        abs_zero, le_refl]
    · have hd : 0 < dist q.1 q.2 := dist_pos.mpr hdiag
      have hcap : cappedInverseDistancePow (m + 1) ε q ≤ (dist q.1 q.2 ^ (m + 1))⁻¹ := by
        exact inv_anti₀ (pow_pos hd _) (pow_le_pow_left₀ hd.le (le_max_right _ _) _)
      have hdiff : 0 ≤ (dist q.1 q.2 ^ (m + 1))⁻¹ - cappedInverseDistancePow (m + 1) ε q :=
        sub_nonneg.mpr hcap
      have heq : fractionalBilinear m w φ q.1 q.2 - (w q.1 - w q.2) * cappedTestKernel m ε φ q =
          ((w q.1 - w q.2) * (φ q.1 - φ q.2)) *
            ((dist q.1 q.2 ^ (m + 1))⁻¹ - cappedInverseDistancePow (m + 1) ε q) := by
        unfold fractionalBilinear cappedTestKernel
        ring
      rw [heq, abs_mul, abs_of_nonneg hdiff]
      calc
        _ ≤ |(w q.1 - w q.2) * (φ q.1 - φ q.2)| * (dist q.1 q.2 ^ (m + 1))⁻¹ := by
          exact mul_le_mul_of_nonneg_left
            (sub_le_self _ (cappedInverseDistancePow_nonneg (m + 1) ε q)) (abs_nonneg _)
        _ = _ := by
          simp only [fractionalBilinear, div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hd _))]
  · rw [indicator_of_notMem hnear]
    have hd : ε ≤ dist q.1 q.2 := by
      have hn : ¬dist q.2 q.1 ≤ ε := hnear
      simpa only [dist_comm q.2 q.1] using! (lt_of_not_ge hn).le
    rw [capped_bilinear_eq_outside m ε w φ q hd, sub_self, abs_zero]

theorem fractional_bilinear_integrable_and_cap_error {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w φ : Ambient d → ℝ) (hw : Measurable w) (hwI : Integrable w μ)
    (L B : ℝ≥0) (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ))
    (henergy : Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) w q.1 q.2) (μ.prod μ))
    (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) w φ q.1 q.2) (μ.prod μ) ∧
      |(∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) w φ q.1 q.2 ∂μ.prod μ) -
        ∫ q : Ambient d × Ambient d, (w q.1 - w q.2) * cappedTestKernel (p + 1) ε φ q ∂μ.prod μ| ≤
          ∫ q in nearPairSet ε, |fractionalBilinear (p + 1) w φ q.1 q.2| ∂μ.prod μ := by
  let F := fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) w φ q.1 q.2
  let G := fun q : Ambient d × Ambient d => (w q.1 - w q.2) * cappedTestKernel (p + 1) ε φ q
  have hFmeas : Measurable F := by
    dsimp only [F]
    unfold fractionalBilinear
    have hφm := hφ.continuous.measurable
    fun_prop
  have hGkernel := cappedTestKernel_lipschitz (p + 1) ε hε φ L B hφ hB
  have hG : Integrable G (μ.prod μ) :=
    (antisymmetric_kernel_pairing μ w hwI (cappedTestKernel (p + 1) ε φ)
      hGkernel.continuous.measurable ((2 * (B : ℝ)) * (ε ^ (p + 1 + 1))⁻¹)
      (cappedTestKernel_bound (p + 1) ε hε φ B hB) (cappedTestKernel_antisymm (p + 1) ε φ)).1
  have hnear : IntegrableOn F (nearPairSet ε) (μ.prod μ) :=
    (near_fractionalBilinear_integrable_and_bound p C μ hg w φ hw L hφ henergy ε hε).1
  have hdom : Integrable ((nearPairSet ε).indicator (fun q => |F q|)) (μ.prod μ) :=
    (integrable_indicator_iff (nearPairSet_measurable ε)).mpr hnear.abs
  have herr : Integrable (fun q => F q - G q) (μ.prod μ) := by
    apply hdom.mono' (hFmeas.aestronglyMeasurable.sub hG.aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro q
    simpa only [Real.norm_eq_abs] using! capped_bilinear_error_pointwise (p + 1) ε w φ q
  have hF : Integrable F (μ.prod μ) := by
    have heq : F = fun q => (F q - G q) + G q := by funext q; ring
    rw [heq]
    exact herr.add hG
  refine ⟨hF, ?_⟩
  change |(∫ q, F q ∂μ.prod μ) - ∫ q, G q ∂μ.prod μ| ≤ ∫ q in nearPairSet ε, |F q| ∂μ.prod μ
  rw [← integral_sub hF hG, ← integral_indicator (nearPairSet_measurable ε)]
  calc
    _ ≤ ∫ q, |F q - G q| ∂μ.prod μ := abs_integral_le_integral_abs
    _ ≤ _ := integral_mono_ae herr.abs hdom
      (Filter.Eventually.of_forall fun q => capped_bilinear_error_pointwise (p + 1) ε w φ q)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_FinitePairingCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem closedExterior_eq_compl_ball {d : ℕ} (a : Ambient d) (R : ℝ) :
    closedExterior a R = (ball a R)ᶜ := by
  ext y
  change (R ≤ dist a y) ↔ ¬ dist y a < R
  rw [dist_comm y a, not_lt]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FarTestKernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter

theorem inverseDistancePow_bound_of_separation {d : ℕ} (q : ℕ)
    (x y : Ambient d) (R : ℝ) (hR : 0 < R) (hsep : R ≤ dist x y) :
    inverseDistancePow q x y ≤ (R ^ q)⁻¹ := by
  simpa only [inverseDistancePow, one_div] using!
    one_div_le_one_div_of_le (pow_pos hR q) (pow_le_pow_left₀ hR.le hsep q)

theorem subtracted_far_test_kernel_uniform_bound {d : ℕ} (m : ℕ)
    (x y : Ambient d) (R : ℝ) (hR : 0 < R) (hx : R ≤ ‖x‖)
    (hy : y ∈ closedExterior x R) :
    |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x| ≤
      2 * (R ^ (m + 1))⁻¹ := by
  have ha := inverseDistancePow_bound_of_separation (m + 1) x y R hR hy
  have hb := inverseDistancePow_bound_of_separation (m + 1) 0 x R hR
    (by simpa only [dist_zero_left] using! hx)
  have hna := inverseDistancePow_nonneg (m + 1) x y
  have hnb := inverseDistancePow_nonneg (m + 1) 0 x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem subtracted_far_test_kernel_central_bound {d : ℕ} (m : ℕ)
    (x y : Ambient d) (hx : 0 < ‖x‖) (hy : ‖y‖ ≤ ‖x‖ / 2) :
    |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x| ≤
      (m + 1 : ℝ) * 2 ^ (m + 2) * ‖y‖ * inverseDistancePow (m + 2) 0 x := by
  have hh := inverseDistancePow_far_difference m (0 : Ambient d) y x
    (by simpa only [dist_zero_left] using! hx)
    (by simpa only [dist_zero_left, dist_zero_right] using! (show 2 * ‖y‖ ≤ ‖x‖ by linarith))
  simpa only [inverseDistancePow, dist_comm y x, dist_zero_right] using! hh

theorem subtracted_far_test_kernel_integrable {d : ℕ}
    (μ : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g μ)
    (m : ℕ) (x : Ambient d) (R : ℝ) (hR : 0 < R) (hx : R ≤ ‖x‖) :
    IntegrableOn (fun y => (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x) • g y)
      (closedExterior x R) μ := by
  apply hg.restrict.bdd_smul (2 * (R ^ (m + 1))⁻¹)
    (((inverseDistancePow_measurable (m + 1) x).sub measurable_const).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (closedExterior_measurable x R)] with y hy
  exact subtracted_far_test_kernel_uniform_bound m x y R hR hx hy

theorem raw_far_test_kernel_integrable {d : ℕ}
    (μ : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g μ)
    (m : ℕ) (x : Ambient d) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun y => inverseDistancePow (m + 1) x y • g y) (closedExterior x R) μ := by
  apply hg.restrict.bdd_smul ((R ^ (m + 1))⁻¹)
    (inverseDistancePow_measurable (m + 1) x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (closedExterior_measurable x R)] with y hy
  rw [Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  exact inverseDistancePow_bound_of_separation (m + 1) x y R hR hy

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_TranslatedFarTestIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Set

theorem far_kernel_add_translation {d : ℕ} (m : ℕ) (g : Ambient d → ℂ)
    (x : Ambient d) (R : ℝ) :
    (IntegrableOn (fun h => inverseDistancePow (m + 1) 0 h • g (x + h)) (closedExterior 0 R) ↔
      IntegrableOn (fun y => inverseDistancePow (m + 1) x y • g y) (closedExterior x R)) ∧
    (∫ h in closedExterior 0 R, inverseDistancePow (m + 1) 0 h • g (x + h)) =
      ∫ y in closedExterior x R, inverseDistancePow (m + 1) x y • g y := by
  have hp := measurePreserving_add_left (volume : Measure (Ambient d)) x
  have he := (MeasurableEquiv.addLeft x).measurableEmbedding
  have hs : (fun h => x + h) ⁻¹' closedExterior x R = closedExterior 0 R := by
    ext h
    simp [closedExterior, dist_eq_norm]
  have hk : ∀ h : Ambient d, inverseDistancePow (m + 1) x (x + h) = inverseDistancePow (m + 1) 0 h := by
    intro h
    simp [inverseDistancePow, dist_eq_norm]
  constructor
  · simpa only [hs, Function.comp_def, hk] using! hp.integrableOn_comp_preimage he
      (f := fun y => inverseDistancePow (m + 1) x y • g y) (s := closedExterior x R)
  · simpa only [hs, hk] using! hp.setIntegral_preimage_emb he
      (fun y => inverseDistancePow (m + 1) x y • g y) (closedExterior x R)

theorem far_kernel_sub_translation {d : ℕ} (m : ℕ) (g : Ambient d → ℂ)
    (x : Ambient d) (R : ℝ) :
    (IntegrableOn (fun h => inverseDistancePow (m + 1) 0 h • g (x - h)) (closedExterior 0 R) ↔
      IntegrableOn (fun y => inverseDistancePow (m + 1) x y • g y) (closedExterior x R)) ∧
    (∫ h in closedExterior 0 R, inverseDistancePow (m + 1) 0 h • g (x - h)) =
      ∫ y in closedExterior x R, inverseDistancePow (m + 1) x y • g y := by
  have hp := (volume : Measure (Ambient d)).measurePreserving_sub_left x
  have he := (MeasurableEquiv.subLeft x).measurableEmbedding
  have hs : (fun h => x - h) ⁻¹' closedExterior x R = closedExterior 0 R := by
    ext h
    simp [closedExterior, dist_eq_norm]
  have hk : ∀ h : Ambient d, inverseDistancePow (m + 1) x (x - h) = inverseDistancePow (m + 1) 0 h := by
    intro h
    simp [inverseDistancePow, dist_eq_norm]
  constructor
  · simpa only [hs, Function.comp_def, hk] using! hp.integrableOn_comp_preimage he
      (f := fun y => inverseDistancePow (m + 1) x y • g y) (s := closedExterior x R)
  · simpa only [hs, hk] using! hp.setIntegral_preimage_emb he
      (fun y => inverseDistancePow (m + 1) x y • g y) (closedExterior x R)

theorem fractionalSchwartz_far_integral_identity (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) (R : ℝ) (hR : 0 < R) :
    (-1 / 2 : ℝ) • (∫ h in closedExterior 0 R, fractionalSchwartzKernel (p + 1) g x h) =
      (∫ h in closedExterior (0 : Ambient (p + 1)) R, inverseDistancePow (p + 1 + 1) 0 h) • g x -
        ∫ y in closedExterior x R, inverseDistancePow (p + 1 + 1) x y • g y := by
  obtain ⟨hplus, heqplus⟩ := far_kernel_add_translation (p + 1) g x R
  obtain ⟨hminus, heqminus⟩ := far_kernel_sub_translation (p + 1) g x R
  have hr := raw_far_test_kernel_integrable volume g g.integrable (p + 1) x R hR
  have hp := hplus.mpr hr
  have hm := hminus.mpr hr
  have hk := (inverseDistancePow_closedExterior_integrable_and_bound (d := p + 1) (p + 1) _ volume
    (volume_global_upper_growth (p + 1)) 0 R hR).1
  have hc := hk.smul_const (g x)
  have heq : fractionalSchwartzKernel (p + 1) g x = fun h =>
      (inverseDistancePow (p + 1 + 1) 0 h • g (x + h) +
        inverseDistancePow (p + 1 + 1) 0 h • g (x - h)) -
      (2 : ℝ) • (inverseDistancePow (p + 1 + 1) 0 h • g x) := by
    funext h
    change inverseDistancePow (p + 1 + 1) 0 h •
      (g (x + h) + g (x - h) - (2 : ℝ) • g x) = _
    exact (smul_sub (inverseDistancePow (p + 1 + 1) 0 h)
      (g (x + h) + g (x - h)) ((2 : ℝ) • g x)).trans
      (congrArg₂ (fun a b : ℂ => a - b)
        (smul_add (inverseDistancePow (p + 1 + 1) 0 h) (g (x + h)) (g (x - h)))
        (smul_comm (inverseDistancePow (p + 1 + 1) 0 h) (2 : ℝ) (g x)))
  have hpm : IntegrableOn (fun h => inverseDistancePow (p + 1 + 1) 0 h • g (x + h) +
      inverseDistancePow (p + 1 + 1) 0 h • g (x - h)) (closedExterior 0 R) := hp.add hm
  have hcc : IntegrableOn (fun h : Ambient (p + 1) =>
      (2 : ℝ) • (inverseDistancePow (p + 1 + 1) 0 h • g x))
      (closedExterior 0 R) := hc.smul (2 : ℝ)
  have hci : (∫ h in closedExterior (0 : Ambient (p + 1)) R,
      (2 : ℝ) • (inverseDistancePow (p + 1 + 1) 0 h • g x)) =
      (2 : ℝ) • ((∫ h in closedExterior (0 : Ambient (p + 1)) R,
        inverseDistancePow (p + 1 + 1) 0 h) • g x) := by
    calc
      _ = (2 : ℝ) • (∫ h in closedExterior (0 : Ambient (p + 1)) R,
          inverseDistancePow (p + 1 + 1) 0 h • g x) := integral_smul (2 : ℝ) _
      _ = _ := congrArg (fun z : ℂ => (2 : ℝ) • z)
        (integral_smul_const (inverseDistancePow (p + 1 + 1) (0 : Ambient (p + 1))) (g x))
  rw [heq, integral_sub hpm hcc, integral_add hp hm, hci, heqplus, heqminus]
  norm_num [RCLike.real_smul_eq_coe_mul]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_DerivativeTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Analytic bounds for Schwartz test functions

Integration by parts shows that a Schwartz directional derivative has zero
integral. The zeroth Schwartz seminorms of a test function and its Fréchet
derivative also give global boundedness and Lipschitz constants.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set SchwartzMap
open scoped NNReal LineDeriv ContDiff

theorem schwartz_real_bounded_lipschitz {d : ℕ} (g : 𝓢(Ambient d, ℝ)) :
    ∃ L B : ℝ≥0, LipschitzWith L g ∧ ∀ x, |g x| ≤ (B : ℝ) := by
  let G := fderivCLM ℝ (Ambient d) ℝ g
  let L : ℝ≥0 := Real.toNNReal (SchwartzMap.seminorm ℝ 0 0 G)
  let B : ℝ≥0 := Real.toNNReal (SchwartzMap.seminorm ℝ 0 0 g)
  refine ⟨L, B, lipschitzWith_of_nnnorm_fderiv_le g.differentiable ?_, ?_⟩
  · intro x
    have h : ‖fderiv ℝ g x‖ ≤ (L : ℝ) :=
      (G.norm_le_seminorm ℝ x).trans (Real.le_coe_toNNReal _)
    exact_mod_cast h
  · intro x
    exact (g.norm_le_seminorm ℝ x).trans (Real.le_coe_toNNReal _)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ExpandingSmoothCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Expanding smooth cutoffs

Dilating a fixed bump gives compactly supported smooth cutoffs equal to one on
balls of increasing radius. Composition with linear contractions bounds all
derivatives by Schwartz seminorms and supplies uniform derivative bounds for
the cutoff errors.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped ContDiff

theorem expandingSmoothCutoff_smooth (d j : ℕ) :
    ContDiff ℝ ∞ (expandingSmoothCutoff d j) := by
  apply (unitSmoothCutoff d).contDiff.comp
  exact (contDiff_id : ContDiff ℝ ∞ (fun x : Ambient d => x)).const_smul _

theorem expandingSmoothCutoff_compact (d j : ℕ) :
    HasCompactSupport (expandingSmoothCutoff d j) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Ambient d) (2 * ((j : ℝ) + 1)))
  intro x hx
  apply (unitSmoothCutoff d).zero_of_le_dist
  have hR : 0 < (j : ℝ) + 1 := by positivity
  have hx' : 2 * ((j : ℝ) + 1) < ‖x‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using! hx
  change 2 ≤ dist (((j : ℝ) + 1)⁻¹ • x) 0
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  exact (le_div_iff₀ hR).2 hx'.le |>.trans_eq (div_eq_inv_mul _ _)

theorem expandingSmoothCutoff_one (d j : ℕ) (x : Ambient d)
    (hx : x ∈ ball (0 : Ambient d) ((j : ℝ) + 1)) :
    expandingSmoothCutoff d j x = 1 := by
  apply (unitSmoothCutoff d).one_of_mem_closedBall
  have hR : 0 < (j : ℝ) + 1 := by positivity
  have hx' : ‖x‖ < (j : ℝ) + 1 := by
    simpa only [mem_ball, dist_zero_right] using! hx
  change dist (((j : ℝ) + 1)⁻¹ • x) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  have hh : ‖x‖ / ((j : ℝ) + 1) ≤ 1 := (div_le_one hR).2 hx'.le
  simpa only [div_eq_inv_mul] using! hh

theorem schwartz_contraction_derivative_bound {d : ℕ} (g : 𝓢(Ambient d, ℝ))
    (S : Ambient d →L[ℝ] Ambient d) (hS : ‖S‖ ≤ 1) (n : ℕ) (x : Ambient d) :
    ‖iteratedFDeriv ℝ n (g ∘ S) x‖ ≤ SchwartzMap.seminorm ℝ 0 n g := by
  rw [S.iteratedFDeriv_comp_right (g.smooth n) x le_rfl]
  have hp : (∏ _ : Fin n, ‖S‖) ≤ 1 := by
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hS)
  calc
    _ ≤ ‖iteratedFDeriv ℝ n g (S x)‖ * ∏ _ : Fin n, ‖S‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n g (S x)‖ := by nlinarith [norm_nonneg (iteratedFDeriv ℝ n g (S x))]
    _ ≤ _ := g.norm_iteratedFDeriv_le_seminorm ℝ n (S x)

theorem expandingSmoothCutoff_error_uniform_derivatives (d : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ j n x,
      ‖iteratedFDeriv ℝ n (fun y => expandingSmoothCutoff d j y - 1) x‖ ≤ C n := by
  let β : 𝓢(Ambient d, ℝ) := (unitSmoothCutoff d).hasCompactSupport.toSchwartzMap
    (unitSmoothCutoff d).contDiff
  refine ⟨fun n => SchwartzMap.seminorm ℝ 0 n β + 1, fun n => by positivity, ?_⟩
  intro j n x
  let S : Ambient d →L[ℝ] Ambient d := ((j : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (Ambient d)
  have hR : 1 ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hS : ‖S‖ ≤ 1 := by
    calc
      ‖S‖ ≤ ‖((j : ℝ) + 1)⁻¹‖ * ‖ContinuousLinearMap.id ℝ (Ambient d)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ 1 * 1 := mul_le_mul
        (by rw [Real.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ hR)
        ContinuousLinearMap.norm_id_le (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have heq : (expandingSmoothCutoff d j : Ambient d → ℝ) = β ∘ S := rfl
  have hb := schwartz_contraction_derivative_bound β S hS n x
  have hs : ContDiff ℝ n (expandingSmoothCutoff d j) := by
    rw [heq]
    exact (β.smooth n).comp S.contDiff
  have hc : ‖iteratedFDeriv ℝ n (fun _ : Ambient d => (1 : ℝ)) x‖ ≤ 1 := by
    cases n with
    | zero => simp
    | succ n => simp [iteratedFDeriv_succ_const]
  have hh := iteratedFDeriv_sub_apply hs.contDiffAt
    (contDiffAt_const (c := (1 : ℝ)) : ContDiffAt ℝ n (fun _ : Ambient d => (1 : ℝ)) x)
  change ‖iteratedFDeriv ℝ n ((expandingSmoothCutoff d j) - (fun _ => 1)) x‖ ≤ _
  rw [hh]
  exact (norm_sub_le _ _).trans (add_le_add (by simpa only [heq] using! hb) hc)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_SchwartzCutoffConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped ContDiff

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem schwartz_cutoff_error_seminorm_le
    (g : 𝓢(Ambient d, F)) (q : Ambient d → ℝ) (hq : q.HasTemperateGrowth)
    (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i x, ‖iteratedFDeriv ℝ i q x‖ ≤ C i)
    (R : ℝ) (hR : 0 < R) (hzero : ∀ x ∈ ball (0 : Ambient d) R, q x = 0)
    (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (smulLeftCLM F q g) ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
        SchwartzMap.seminorm ℝ (k + 1) (n - i) g) / R := by
  have hM : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
      SchwartzMap.seminorm ℝ (k + 1) (n - i) g := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hC i))
      (apply_nonneg _ _)
  apply seminorm_le_bound ℝ k n _ (div_nonneg hM hR.le)
  intro x
  rw [smulLeftCLM_apply hq]
  by_cases hx : x ∈ ball (0 : Ambient d) R
  · have heq : (fun y => q y • g y) =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      simp [hzero y hy]
    have he := (heq.iteratedFDeriv ℝ n).eq_of_nhds
    rw [he]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero] using! div_nonneg hM hR.le
  · have hxR : R ≤ ‖x‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using! hx
    have hp := norm_iteratedFDeriv_smul_le hq.1 (g.smooth ⊤) x (n := n) (mod_cast le_top)
    apply (le_div_iff₀ hR).2
    calc
      (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => q y • g y) x‖) * R ≤
          R * ‖x‖ ^ k * (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i q x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) := by
        nlinarith [mul_le_mul_of_nonneg_left hp (pow_nonneg (norm_nonneg x) k)]
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i q x‖ *
            (R * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g x‖)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
          SchwartzMap.seminorm ℝ (k + 1) (n - i) g := by
        apply Finset.sum_le_sum
        intro i _
        have hw : R * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g x‖) ≤
            SchwartzMap.seminorm ℝ (k + 1) (n - i) g := by
          calc
            _ ≤ ‖x‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g x‖) := by gcongr
            _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (n - i) g x‖ := by ring
            _ ≤ _ := le_seminorm ℝ (k + 1) (n - i) g x
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hbound i x) (by positivity)) hw
          (by positivity) (mul_nonneg (by positivity) (hC i))

theorem schwartz_cutoff_errors_tendsto_zero
    (g : 𝓢(Ambient d, F)) (q : ℕ → Ambient d → ℝ)
    (hq : ∀ j, (q j).HasTemperateGrowth)
    (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ j i x, ‖iteratedFDeriv ℝ i (q j) x‖ ≤ C i)
    (R : ℕ → ℝ) (hR : ∀ j, 0 < R j) (hRt : Tendsto R atTop atTop)
    (hzero : ∀ j x, x ∈ ball (0 : Ambient d) (R j) → q j x = 0) :
    Tendsto (fun j => smulLeftCLM F (q j) g) atTop (𝓝 0) := by
  apply (schwartz_withSeminorms ℝ (Ambient d) F).tendsto_nhds _ _ |>.2
  rintro ⟨k, n⟩ ε hε
  let M := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i *
    SchwartzMap.seminorm ℝ (k + 1) (n - i) g
  have ht : Tendsto (fun j => M / R j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using! tendsto_const_nhds.mul hRt.inv_tendsto_atTop
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with j hj
  simpa only [sub_zero, schwartzSeminormFamily_apply] using!
    (schwartz_cutoff_error_seminorm_le g (q j) (hq j) C hC (hbound j)
      (R j) (hR j) (hzero j) k n).trans_lt hj

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactSchwartzApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compactly supported approximation in Schwartz space

Expanding smooth cutoffs approximate Schwartz functions in the Schwartz topology.
Continuity of directional differentiation preserves this convergence, while compact
support ensures the approximating derivatives have zero integral. Consequently,
tempered distributions are determined by their compactly supported Schwartz tests.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped ContDiff LineDeriv

theorem exists_compact_schwartz_approximation {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : 𝓢(Ambient d, F)) :
    ∃ G : ℕ → 𝓢(Ambient d, F), (∀ j, HasCompactSupport (G j)) ∧
      Tendsto G atTop (𝓝 g) := by
  let G : ℕ → 𝓢(Ambient d, F) := fun j => smulLeftCLM F (expandingSmoothCutoff d j) g
  let q : ℕ → Ambient d → ℝ := fun j x => expandingSmoothCutoff d j x - 1
  have hβ : ∀ j, (expandingSmoothCutoff d j).HasTemperateGrowth :=
    fun j => (expandingSmoothCutoff_compact d j).hasTemperateGrowth (expandingSmoothCutoff_smooth d j)
  have hq : ∀ j, (q j).HasTemperateGrowth :=
    fun j => (hβ j).sub (Function.HasTemperateGrowth.const 1)
  obtain ⟨C, hC, hbound⟩ := expandingSmoothCutoff_error_uniform_derivatives d
  have hRt : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hzero : ∀ (j : ℕ) x, x ∈ ball (0 : Ambient d) ((j : ℝ) + 1) → q j x = 0 := by
    intro j x hx
    simp only [q, expandingSmoothCutoff_one d j x hx, sub_self]
  have ht := schwartz_cutoff_errors_tendsto_zero g q hq C hC hbound
    (fun j : ℕ => (j : ℝ) + 1) (fun j => by positivity) hRt hzero
  refine ⟨G, ?_, ?_⟩
  · intro j
    have hc : HasCompactSupport (fun x => expandingSmoothCutoff d j x • g x) :=
      (expandingSmoothCutoff_compact d j).smul_right
    simpa only [G, smulLeftCLM_apply (hβ j)] using! hc
  · have heq : G = fun j => g + smulLeftCLM F (q j) g := by
      funext j
      ext x
      simp only [G, add_apply, smulLeftCLM_apply_apply (hβ j),
        smulLeftCLM_apply_apply (hq j), q, sub_smul, one_smul]
      abel
    rw [heq]
    simpa only [add_zero] using! tendsto_const_nhds.add ht

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_MeanZeroSchwartzApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform

theorem unitSmoothCutoff_integral_pos (d : ℕ) :
    0 < ∫ x : Ambient d, unitSmoothCutoff d x := by
  have hc := ((unitSmoothCutoff d).contDiff (n := ⊤)).continuous
  have hi : Integrable (unitSmoothCutoff d) (volume : Measure (Ambient d)) :=
    hc.integrable_of_hasCompactSupport (unitSmoothCutoff d).hasCompactSupport
  apply integral_pos_of_integrable_nonneg_nonzero hc hi
    (fun x => (unitSmoothCutoff d).nonneg' x)
  have h : unitSmoothCutoff d (0 : Ambient d) = 1 :=
    (unitSmoothCutoff d).one_of_mem_closedBall (by simp [unitSmoothCutoff])
  exact h.trans_ne one_ne_zero

theorem exists_compact_complex_schwartz_unit_integral (d : ℕ) :
    ∃ η : 𝓢(Ambient d, ℂ), HasCompactSupport η ∧ (∫ x, η x) = 1 := by
  let b : Ambient d → ℂ := fun x => (unitSmoothCutoff d x : ℂ)
  have hb : HasCompactSupport b := (unitSmoothCutoff d).hasCompactSupport.comp_left
    (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ b := Complex.ofRealCLM.contDiff.comp
    ((unitSmoothCutoff d).contDiff (n := ⊤))
  let B : 𝓢(Ambient d, ℂ) := hb.toSchwartzMap hs
  have hc : HasCompactSupport B := hb
  have hI : (∫ x, B x) ≠ 0 := by
    change (∫ x : Ambient d, (unitSmoothCutoff d x : ℂ)) ≠ 0
    rw [integral_complex_ofReal]
    exact_mod_cast ne_of_gt (unitSmoothCutoff_integral_pos d)
  refine ⟨(∫ x, B x)⁻¹ • B, ?_, ?_⟩
  · exact hc.smul_left
  · change (∫ x, (∫ y, B y)⁻¹ • B x) = 1
    rw [integral_smul, smul_eq_mul, inv_mul_cancel₀ hI]

theorem exists_compact_mean_zero_schwartz_approximation {d : ℕ}
    (g : 𝓢(Ambient d, ℂ)) (hg : (∫ x, g x) = 0) :
    ∃ G : ℕ → 𝓢(Ambient d, ℂ),
      (∀ j, HasCompactSupport (G j) ∧ (∫ x, G j x) = 0) ∧ Tendsto G atTop (𝓝 g) := by
  obtain ⟨G, hc, ht⟩ := exists_compact_schwartz_approximation g
  obtain ⟨η, hcη, hη⟩ := exists_compact_complex_schwartz_unit_integral d
  let I : 𝓢(Ambient d, ℂ) →L[ℂ] ℂ := integralCLM ℂ volume
  let H : ℕ → 𝓢(Ambient d, ℂ) := fun j => G j - I (G j) • η
  have hIη : I η = 1 := hη
  have hIg : I g = 0 := hg
  refine ⟨H, ?_, ?_⟩
  · intro j
    refine ⟨(hc j).sub hcη.smul_left, ?_⟩
    change I (G j - I (G j) • η) = 0
    rw [map_sub, map_smul, hIη, smul_eq_mul, mul_one, sub_self]
  · have hi : Tendsto (fun j => I (G j)) atTop (𝓝 0) := by
      simpa only [hIg] using! I.continuous.tendsto g |>.comp ht
    have hs := hi.smul (tendsto_const_nhds (x := η))
    simpa only [zero_smul, sub_zero] using! ht.sub hs

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalSchwartzContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Continuity of fractional Schwartz tests

The integral defining a fractional Schwartz test respects addition and scalar
multiplication. Uniform seminorm bounds control these tests and support their
continuity under Schwartz approximation.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped NNReal ENNReal

theorem fractionalSchwartzTest_measurable (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ)) :
    Measurable (fractionalSchwartzTest p g) := by
  have hm : Measurable (fun q : Ambient (p + 1) × Ambient (p + 1) =>
      fractionalSchwartzKernel (p + 1) g q.1 q.2) := by
    unfold fractionalSchwartzKernel symmetricSecondDifference inverseDistancePow
    fun_prop
  unfold fractionalSchwartzTest
  simp_rw [RCLike.real_smul_eq_coe_mul]
  exact measurable_const.mul (hm.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Ambient (p + 1))))).measurable

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalTruncatedTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Truncated fractional Schwartz tests

Restricting the symmetric second-difference kernel to the closed exterior of a
ball gives measurable tests with uniform bounds in Schwartz seminorms. The
integrable full kernel dominates every truncation, so dominated convergence
recovers the fractional Schwartz test as the truncation radii tend to zero.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set

theorem fractionalSchwartzTruncatedTest_measurable (p : ℕ) (ε : ℝ)
    (g : 𝓢(Ambient (p + 1), ℂ)) : Measurable (fractionalSchwartzTruncatedTest p ε g) := by
  have hm : Measurable (fun q : Ambient (p + 1) × Ambient (p + 1) =>
      fractionalSchwartzKernel (p + 1) g q.1 q.2) := by
    unfold fractionalSchwartzKernel symmetricSecondDifference inverseDistancePow
    fun_prop
  unfold fractionalSchwartzTruncatedTest
  simp_rw [RCLike.real_smul_eq_coe_mul]
  exact measurable_const.mul (hm.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Ambient (p + 1))).restrict (closedExterior 0 ε))).measurable

theorem fractionalSchwartzTruncatedTest_uniform_bound (p : ℕ) (ε : ℝ)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) :
    ‖fractionalSchwartzTruncatedTest p ε g x‖ ≤
      4 * (((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal * 2 ^ (p + 1) * 2 ^ p) *
        SchwartzMap.seminorm ℝ 0 2 g +
      8 * (((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal * 2 ^ (p + 1)) *
        SchwartzMap.seminorm ℝ 0 0 g := by
  let K := fractionalSchwartzKernel (p + 1) g x
  have hi : Integrable K := fractionalSchwartzKernel_integrable p g x
  have hb := fractionalSchwartzKernel_integral_norm_bound p _ volume
    (volume_global_upper_growth (p + 1)) g x
  have hn := norm_integral_le_integral_norm (μ := volume.restrict (closedExterior 0 ε)) K
  have hr : (∫ h in closedExterior 0 ε, ‖K h‖) ≤ ∫ h, ‖K h‖ :=
    integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun h => norm_nonneg _) hi.norm
  unfold fractionalSchwartzTruncatedTest
  rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
  norm_num
  nlinarith [norm_nonneg (∫ h in closedExterior 0 ε, K h)]

theorem fractionalSchwartzTruncatedTest_tendsto (p : ℕ)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) :
    Tendsto (fun j => fractionalSchwartzTruncatedTest p (ε j) g x)
      atTop (𝓝 (fractionalSchwartzTest p g x)) := by
  let K := fractionalSchwartzKernel (p + 1) g x
  have hi : Integrable K := fractionalSchwartzKernel_integrable p g x
  have hK0 : K 0 = 0 := by
    dsimp [K, fractionalSchwartzKernel, inverseDistancePow]
    simp
  have hlim (h : Ambient (p + 1)) :
      Tendsto (fun j => (closedExterior 0 (ε j)).indicator K h) atTop (𝓝 (K h)) := by
    by_cases hh : h = 0
    · subst h
      have hz : (fun j => (closedExterior 0 (ε j)).indicator K 0) = fun _ : ℕ => (0 : ℂ) := by
        funext j
        by_cases hs : (0 : Ambient (p + 1)) ∈ closedExterior 0 (ε j)
        · exact (indicator_of_mem hs K).trans hK0
        · exact indicator_of_notMem hs K
      rw [hz, hK0]
      exact tendsto_const_nhds
    · have hp : 0 < ‖h‖ := norm_pos_iff.mpr hh
      apply tendsto_const_nhds.congr'
      filter_upwards [hε.eventually (gt_mem_nhds hp)] with j hj
      have hs : h ∈ closedExterior 0 (ε j) := by
        simpa only [closedExterior, mem_ofPred_eq, dist_zero_left] using! hj.le
      exact (indicator_of_mem hs K).symm
  have ht := tendsto_integral_of_dominated_convergence (fun h => ‖K h‖)
    (fun j => hi.aestronglyMeasurable.indicator (closedExterior_measurable 0 (ε j))) hi.norm
    (fun j => Eventually.of_forall fun h => norm_indicator_le_norm_self K h)
    (Eventually.of_forall hlim)
  have heq : (fun j => ∫ h in closedExterior 0 (ε j), K h) =
      fun j => ∫ h, (closedExterior 0 (ε j)).indicator K h := by
    funext j
    exact (integral_indicator (f := K) (closedExterior_measurable 0 (ε j))).symm
  change Tendsto (fun j => (-1 / 2 : ℝ) • (∫ h in closedExterior 0 (ε j), K h))
    atTop (𝓝 ((-1 / 2 : ℝ) • ∫ h, K h))
  change Tendsto (fun j => (-1 / 2 : ℝ) • ((fun j => ∫ h in closedExterior 0 (ε j), K h) j)) _ _
  rw [heq]
  exact ht.const_smul (-1 / 2 : ℝ)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalTruncatedRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Set

theorem inverseDistancePow_exterior_mass_translation {d : ℕ} (m : ℕ)
    (x : Ambient d) (ε : ℝ) :
    (∫ y in closedExterior x ε, inverseDistancePow (m + 1) x y) =
      ∫ h in closedExterior (0 : Ambient d) ε, inverseDistancePow (m + 1) 0 h := by
  have hp := measurePreserving_add_left (volume : Measure (Ambient d)) x
  have he := (MeasurableEquiv.addLeft x).measurableEmbedding
  have hs : (fun h => x + h) ⁻¹' closedExterior x ε = closedExterior 0 ε := by
    ext h
    simp [closedExterior, dist_eq_norm]
  have hk : ∀ h : Ambient d, inverseDistancePow (m + 1) x (x + h) = inverseDistancePow (m + 1) 0 h := by
    intro h
    simp [inverseDistancePow, dist_eq_norm]
  simpa only [hs, hk] using! (hp.setIntegral_preimage_emb he
    (inverseDistancePow (m + 1) x) (closedExterior x ε)).symm

theorem fractionalSchwartz_single_increment_integrable (p : ℕ) (ε : ℝ) (hε : 0 < ε)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) :
    IntegrableOn (fun y => inverseDistancePow (p + 1 + 1) x y • (g x - g y))
      (closedExterior x ε) volume := by
  have hk := (inverseDistancePow_closedExterior_integrable_and_bound (p + 1) _ volume
    (volume_global_upper_growth (p + 1)) x ε hε).1
  have hraw := raw_far_test_kernel_integrable volume g g.integrable (p + 1) x ε hε
  have hsub := (hk.smul_const (g x)).sub hraw
  have heq : (fun y => inverseDistancePow (p + 1 + 1) x y • (g x - g y)) =
      fun y => inverseDistancePow (p + 1 + 1) x y • g x - inverseDistancePow (p + 1 + 1) x y • g y := by
    funext y
    exact smul_sub (inverseDistancePow (p + 1 + 1) x y) (g x) (g y)
  rw [heq]
  exact hsub

theorem fractionalSchwartzTruncatedTest_eq_single_increment (p : ℕ) (ε : ℝ) (hε : 0 < ε)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) :
    fractionalSchwartzTruncatedTest p ε g x =
      ∫ y in closedExterior x ε, inverseDistancePow (p + 1 + 1) x y • (g x - g y) := by
  have hk := (inverseDistancePow_closedExterior_integrable_and_bound (p + 1) _ volume
    (volume_global_upper_growth (p + 1)) x ε hε).1
  have hraw := raw_far_test_kernel_integrable volume g g.integrable (p + 1) x ε hε
  have hc : IntegrableOn (fun y => inverseDistancePow (p + 1 + 1) x y • g x)
      (closedExterior x ε) := hk.smul_const (g x)
  have heq : (fun y => inverseDistancePow (p + 1 + 1) x y • (g x - g y)) =
      fun y => inverseDistancePow (p + 1 + 1) x y • g x - inverseDistancePow (p + 1 + 1) x y • g y := by
    funext y
    exact smul_sub (inverseDistancePow (p + 1 + 1) x y) (g x) (g y)
  rw [heq, integral_sub hc hraw]
  have hconst : (∫ y in closedExterior x ε, inverseDistancePow (p + 1 + 1) x y • g x) =
      (∫ h in closedExterior (0 : Ambient (p + 1)) ε, inverseDistancePow (p + 1 + 1) 0 h) • g x := by
    calc
      _ = (∫ y in closedExterior x ε, inverseDistancePow (p + 1 + 1) x y) • g x :=
        integral_smul_const _ (g x)
      _ = _ := congrArg (fun z : ℝ => z • g x)
        (inverseDistancePow_exterior_mass_translation (p + 1) x ε)
  rw [hconst]
  exact fractionalSchwartz_far_integral_identity p g x ε hε

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SymmetricHeightKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter

theorem real_smul_double_difference (a b r : ℝ) (u v : ℂ) :
    (a - b) • (r • (u - v)) = a • (r • (u - v)) + b • (r • (v - u)) := by
  simp only [RCLike.real_smul_eq_coe_mul, map_sub]
  ring

theorem bounded_kernel_height_integrable {d : ℕ}
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (w : Ambient d → ℝ) (hwm : Measurable w) (hw : Integrable w ν)
    (g : Ambient d → ℂ) (hgm : Measurable g) (B : ℝ) (hB : 0 ≤ B) (hg : ∀ x, ‖g x‖ ≤ B)
    (k : Ambient d × Ambient d → ℝ) (hkm : Measurable k)
    (C : ℝ) (hk : ∀ q, |k q| ≤ C) :
    Integrable (fun q : Ambient d × Ambient d => w q.1 • (k q • (g q.1 - g q.2))) (ν.prod ν) := by
  have hdom := (hw.norm.mul_prod (integrable_const (μ := ν) (1 : ℝ))).mul_const (2 * C * B)
  have hm : Measurable (fun q : Ambient d × Ambient d => w q.1 • (k q • (g q.1 - g q.2))) := by
    simp_rw [RCLike.real_smul_eq_coe_mul]
    exact (Complex.continuous_ofReal.measurable.comp (hwm.comp measurable_fst)).mul
      ((Complex.continuous_ofReal.measurable.comp hkm).mul
        ((hgm.comp measurable_fst).sub (hgm.comp measurable_snd)))
  apply hdom.mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro q
  have hd : ‖g q.1 - g q.2‖ ≤ 2 * B := by
    have hh := norm_sub_le (g q.1) (g q.2)
    linarith [hg q.1, hg q.2]
  simp only [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal, Real.norm_eq_abs, mul_one]
  calc
    _ ≤ |w q.1| * (C * (2 * B)) := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hd (abs_nonneg (k q))).trans
        (mul_le_mul_of_nonneg_right (hk q) (mul_nonneg (by norm_num) hB))) (abs_nonneg _)
    _ = _ := by ring

theorem finite_symmetric_height_kernel_pairing {d : ℕ}
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (w : Ambient d → ℝ) (hwm : Measurable w) (hw : Integrable w ν)
    (g : Ambient d → ℂ) (hgm : Measurable g) (B : ℝ) (hB : 0 ≤ B) (hg : ∀ x, ‖g x‖ ≤ B)
    (k : Ambient d × Ambient d → ℝ) (hkm : Measurable k)
    (C : ℝ) (hk : ∀ q, |k q| ≤ C) (hsym : ∀ q, k q.swap = k q) :
    Integrable (fun q : Ambient d × Ambient d =>
      (w q.1 - w q.2) • (k q • (g q.1 - g q.2))) (ν.prod ν) ∧
    (1 / 2 : ℝ) • (∫ q : Ambient d × Ambient d,
      (w q.1 - w q.2) • (k q • (g q.1 - g q.2)) ∂ν.prod ν) =
        ∫ x, w x • (∫ y, k (x, y) • (g x - g y) ∂ν) ∂ν := by
  let H := fun q : Ambient d × Ambient d => w q.1 • (k q • (g q.1 - g q.2))
  have hH : Integrable H (ν.prod ν) := bounded_kernel_height_integrable
    ν w hwm hw g hgm B hB hg k hkm C hk
  have hswap : Integrable (fun q : Ambient d × Ambient d => H q.swap) (ν.prod ν) := hH.swap
  have heq : (fun q : Ambient d × Ambient d =>
      (w q.1 - w q.2) • (k q • (g q.1 - g q.2))) = fun q => H q + H q.swap := by
    funext q
    dsimp only [H, Prod.swap]
    rw [show k (q.2, q.1) = k q from hsym q]
    exact real_smul_double_difference (w q.1) (w q.2) (k q) (g q.1) (g q.2)
  rw [heq]
  refine ⟨hH.add hswap, ?_⟩
  rw [integral_add hH hswap, integral_prod_swap]
  have hhalf : (1 / 2 : ℝ) • ((∫ q, H q ∂ν.prod ν) + (∫ q, H q ∂ν.prod ν)) =
      ∫ q, H q ∂ν.prod ν := by
    norm_num [RCLike.real_smul_eq_coe_mul]
    ring
  rw [hhalf, integral_prod H hH]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  exact integral_smul (w x) (fun y => k (x, y) • (g x - g y))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FiniteFractionalHeightPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Symmetrization of finite fractional height pairings

The distance cutoff defines a measurable, bounded kernel invariant under
swapping its two variables. Applying the symmetric height-kernel identity and
rewriting the cutoff as an indicator identifies the bilinear pairing with an
iterated integral over the closed exterior region.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Set

theorem symmetricFractionalCutoffKernel_measurable {d : ℕ} (m : ℕ) (ε : ℝ) :
    Measurable (symmetricFractionalCutoffKernel (d := d) m ε) := by
  unfold symmetricFractionalCutoffKernel inverseDistancePow
  apply Measurable.ite (measurableSet_le measurable_const (continuous_fst.dist continuous_snd).measurable)
  · fun_prop
  · exact measurable_const

theorem symmetricFractionalCutoffKernel_bound {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (q : Ambient d × Ambient d) :
    |symmetricFractionalCutoffKernel m ε q| ≤ (ε ^ (m + 1))⁻¹ := by
  unfold symmetricFractionalCutoffKernel
  split_ifs with h
  · rw [abs_of_nonneg (inverseDistancePow_nonneg _ _ _)]
    exact inverseDistancePow_bound_of_separation (m + 1) q.1 q.2 ε hε h
  · simp only [abs_zero]
    positivity

theorem symmetricFractionalCutoffKernel_swap {d : ℕ} (m : ℕ) (ε : ℝ)
    (q : Ambient d × Ambient d) :
    symmetricFractionalCutoffKernel m ε q.swap = symmetricFractionalCutoffKernel m ε q := by
  simp only [symmetricFractionalCutoffKernel, Prod.swap, inverseDistancePow, dist_comm q.2 q.1]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_KernelTestSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter

theorem kernel_test_integrable_from_separated_support {d : ℕ}
    (ν : Measure (Ambient d)) (g : Ambient d → ℂ) (hgm : Measurable g) (hg : Integrable g ν)
    (m : ℕ) (y : Ambient d) (R : ℝ) (hR : 0 < R)
    (hsep : ∀ᵐ x ∂ν, g x ≠ 0 → R ≤ dist x y) :
    Integrable (fun x => inverseDistancePow (m + 1) x y • g x) ν := by
  have hm : Measurable (fun x => inverseDistancePow (m + 1) x y • g x) := by
    unfold inverseDistancePow
    simp_rw [Complex.real_smul]
    fun_prop
  apply (hg.norm.const_mul ((R ^ (m + 1))⁻¹)).mono' hm.aestronglyMeasurable
  filter_upwards [hsep] with x hx
  by_cases hgx : g x = 0
  · rw [hgx]
    simp
  · rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal,
      abs_of_nonneg (inverseDistancePow_nonneg _ _ _)]
    exact mul_le_mul_of_nonneg_right
      (inverseDistancePow_bound_of_separation (m + 1) x y R hR (hx hgx)) (norm_nonneg _)

theorem far_kernel_test_integrable_of_support {d : ℕ}
    (ν : Measure (Ambient d)) (g : Ambient d → ℂ) (hgm : Measurable g) (hg : Integrable g ν)
    (m : ℕ) (a y : Ambient d) (H R : ℝ) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hnear : ∀ᵐ x ∂ν, g x ≠ 0 → dist x a ≤ H) (hfar : R ≤ dist a y) :
    Integrable (fun x => inverseDistancePow (m + 1) x y • g x) ν := by
  have hy : 0 < dist a y := hR.trans_le hfar
  apply kernel_test_integrable_from_separated_support ν g hgm hg m y (dist a y / 2) (by positivity)
  filter_upwards [hnear] with x hx
  intro hgx
  have ht := dist_triangle a x y
  rw [dist_comm a x] at ht
  linarith [hx hgx]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ComplexExteriorIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter

theorem complexRenormalizedNormalIntegrand_norm {d : ℕ} (m : ℕ)
    (w : Ambient d → ℝ) (g : Ambient d → ℂ) (a : Ambient d) (q : Ambient d × Ambient d) :
    ‖complexRenormalizedNormalIntegrand m w g a q‖ =
      |renormalizedNormalIntegrand m w (fun x => ‖g x‖) a q| := by
  unfold complexRenormalizedNormalIntegrand renormalizedNormalIntegrand
  rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal, abs_mul,
    abs_of_nonneg (norm_nonneg (g q.1))]
  ring

theorem complex_renormalized_exterior_integrable {d : ℕ} (m : ℕ) (C : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasure ν]
    (hgrowth : GlobalUpperGrowth m C μ) (w : Ambient d → ℝ) (g : Ambient d → ℂ)
    (hw : Measurable w) (hgm : Measurable g) (hgn : Integrable (fun x => ‖g x‖) ν)
    (hgnw : Integrable (fun x => ‖g x‖ * w x) ν)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hnear : ∀ᵐ x ∂ν, g x ≠ 0 → dist x a ≤ H)
    (hweighted : IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y)
      (closedExterior a R) μ) :
    Integrable (complexRenormalizedNormalIntegrand m w g a)
      (ν.prod (μ.restrict (closedExterior a R))) := by
  have hnormnear : ∀ᵐ x ∂ν, ‖g x‖ ≠ 0 → dist x a ≤ H := by
    filter_upwards [hnear] with x hx
    exact fun hgx => hx (norm_ne_zero_iff.mp hgx)
  have hi := (renormalized_far_pairing_integrable_and_bound m C μ ν hgrowth w
    (fun x => ‖g x‖) hw hgm.norm hgn hgnw a H R hH hR hHR hnormnear hweighted
    (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) le_rfl).1
  have hm : Measurable (complexRenormalizedNormalIntegrand m w g a) := by
    unfold complexRenormalizedNormalIntegrand inverseDistancePow
    simp_rw [Complex.real_smul]
    fun_prop
  apply hi.abs.mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun q => (complexRenormalizedNormalIntegrand_norm m w g a q).le

theorem direct_height_exterior_integrable {d : ℕ} (m : ℕ) (C : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasure ν]
    (hgrowth : GlobalUpperGrowth m C μ) (w : Ambient d → ℝ) (g : Ambient d → ℂ)
    (hw : Measurable w) (hgm : Measurable g)
    (hgnw : Integrable (fun x => ‖g x‖ * w x) ν)
    (a : Ambient d) (H R : ℝ) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hnear : ∀ᵐ x ∂ν, g x ≠ 0 → dist x a ≤ H) :
    Integrable (fun q : Ambient d × Ambient d =>
      w q.1 • (inverseDistancePow (m + 1) q.1 q.2 • g q.1))
      (ν.prod (μ.restrict (closedExterior a R))) := by
  have hk := (inverseDistancePow_closedExterior_integrable_and_bound m C μ hgrowth a R hR).1
  have hdom := (hgnw.abs.mul_prod hk).const_mul ((2 : ℝ) ^ (m + 1))
  have hm : Measurable (fun q : Ambient d × Ambient d =>
      w q.1 • (inverseDistancePow (m + 1) q.1 q.2 • g q.1)) := by
    unfold inverseDistancePow
    simp_rw [Complex.real_smul]
    fun_prop
  apply hdom.mono' hm.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hnear,
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (closedExterior_measurable a R))] with q hx hy
  by_cases hgx : g q.1 = 0
  · rw [hgx]
    simp
  · have hy' : R ≤ dist a q.2 := hy
    have hfar : 2 * dist q.1 a ≤ dist a q.2 := by linarith [hx hgx]
    have hbound := inverseDistancePow_far_le (m + 1) a q.1 q.2 (hR.trans_le hy) hfar
    simp only [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal,
      abs_of_nonneg (inverseDistancePow_nonneg _ _ _), abs_mul, abs_norm]
    calc
      _ ≤ |w q.1| * ((2 ^ (m + 1) * inverseDistancePow (m + 1) a q.2) * ‖g q.1‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbound (norm_nonneg _)) (abs_nonneg _)
      _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ComplexInteriorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap

theorem complex_height_interior_re {d : ℕ} (m : ℕ)
    (w : Ambient d → ℝ) (g : Ambient d → ℂ) (q : Ambient d × Ambient d) :
    (complexHeightInteriorIntegrand m w g q).re =
      fractionalBilinear m w (fun x => (g x).re) q.1 q.2 := by
  unfold complexHeightInteriorIntegrand fractionalBilinear inverseDistancePow
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.sub_re]
  ring

theorem complex_height_interior_im {d : ℕ} (m : ℕ)
    (w : Ambient d → ℝ) (g : Ambient d → ℂ) (q : Ambient d × Ambient d) :
    (complexHeightInteriorIntegrand m w g q).im =
      fractionalBilinear m w (fun x => (g x).im) q.1 q.2 := by
  unfold complexHeightInteriorIntegrand fractionalBilinear inverseDistancePow
  simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.sub_im]
  ring

theorem complex_height_interior_integrable_of_energy {d : ℕ} (p : ℕ) (C : ℝ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (hgrowth : GlobalUpperGrowth (p + 1) C ν)
    (w : Ambient d → ℝ) (hwm : Measurable w) (hw : Integrable w ν)
    (g : 𝓢(Ambient d, ℂ))
    (henergy : Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) w q.1 q.2) (ν.prod ν)) :
    Integrable (complexHeightInteriorIntegrand (p + 1) w g) (ν.prod ν) := by
  let gr : 𝓢(Ambient d, ℝ) := g.postcompCLM Complex.reCLM
  let gi : 𝓢(Ambient d, ℝ) := g.postcompCLM Complex.imCLM
  obtain ⟨Lr, Br, hLr, hBr⟩ := schwartz_real_bounded_lipschitz gr
  obtain ⟨Li, Bi, hLi, hBi⟩ := schwartz_real_bounded_lipschitz gi
  have hr := (fractional_bilinear_integrable_and_cap_error p C ν hgrowth w gr hwm hw
    Lr Br hLr hBr henergy 1 zero_lt_one).1
  have hi := (fractional_bilinear_integrable_and_cap_error p C ν hgrowth w gi hwm hw
    Li Bi hLi hBi henergy 1 zero_lt_one).1
  apply Integrable.re_im_iff.mp
  constructor
  · change Integrable (fun q => (complexHeightInteriorIntegrand (p + 1) w g q).re) (ν.prod ν)
    simpa only [complex_height_interior_re] using! hr
  · change Integrable (fun q => (complexHeightInteriorIntegrand (p + 1) w g q).im) (ν.prod ν)
    simpa only [complex_height_interior_im] using! hi

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ComplexPairingRealComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter

theorem complex_renormalized_normal_re {d : ℕ} (m : ℕ)
    (w : Ambient d → ℝ) (g : Ambient d → ℂ) (a : Ambient d) (q : Ambient d × Ambient d) :
    (complexRenormalizedNormalIntegrand m w g a q).re =
      renormalizedNormalIntegrand m w (fun x => (g x).re) a q := by
  unfold complexRenormalizedNormalIntegrand renormalizedNormalIntegrand
  rw [Complex.smul_re, smul_eq_mul]
  ring

theorem complex_renormalized_normal_im {d : ℕ} (m : ℕ)
    (w : Ambient d → ℝ) (g : Ambient d → ℂ) (a : Ambient d) (q : Ambient d × Ambient d) :
    (complexRenormalizedNormalIntegrand m w g a q).im =
      renormalizedNormalIntegrand m w (fun x => (g x).im) a q := by
  unfold complexRenormalizedNormalIntegrand renormalizedNormalIntegrand
  rw [Complex.smul_im, smul_eq_mul]
  ring

theorem complex_height_pairing_re {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s : Set (Ambient d)) (w : Ambient d → ℝ) (g : Ambient d → ℂ)
    (hI : Integrable (complexHeightInteriorIntegrand m w g) ((μ.restrict s).prod (μ.restrict s)))
    (hN : Integrable (complexRenormalizedNormalIntegrand m w g a)
      ((μ.restrict s).prod (μ.restrict sᶜ))) :
    (complexHeightPairingOn m μ a s w g).re =
      heightPairingOn m μ a s w (fun x => (g x).re) := by
  have hi : (∫ q, complexHeightInteriorIntegrand m w g q ∂(μ.restrict s).prod (μ.restrict s)).re =
      ∫ q, fractionalBilinear m w (fun x => (g x).re) q.1 q.2 ∂(μ.restrict s).prod (μ.restrict s) := by
    calc
      _ = ∫ q, (complexHeightInteriorIntegrand m w g q).re ∂(μ.restrict s).prod (μ.restrict s) :=
        (Complex.reCLM.integral_comp_comm hI).symm
      _ = _ := integral_congr_ae (Eventually.of_forall (complex_height_interior_re m w g))
  have hn : (∫ q, complexRenormalizedNormalIntegrand m w g a q
      ∂(μ.restrict s).prod (μ.restrict sᶜ)).re =
      ∫ q, renormalizedNormalIntegrand m w (fun x => (g x).re) a q
        ∂(μ.restrict s).prod (μ.restrict sᶜ) := by
    calc
      _ = ∫ q, (complexRenormalizedNormalIntegrand m w g a q).re
          ∂(μ.restrict s).prod (μ.restrict sᶜ) := (Complex.reCLM.integral_comp_comm hN).symm
      _ = _ := integral_congr_ae (Eventually.of_forall (complex_renormalized_normal_re m w g a))
  unfold complexHeightPairingOn heightPairingOn
  rw [Complex.add_re, Complex.smul_re, hi, hn, smul_eq_mul]

theorem complex_height_pairing_im {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s : Set (Ambient d)) (w : Ambient d → ℝ) (g : Ambient d → ℂ)
    (hI : Integrable (complexHeightInteriorIntegrand m w g) ((μ.restrict s).prod (μ.restrict s)))
    (hN : Integrable (complexRenormalizedNormalIntegrand m w g a)
      ((μ.restrict s).prod (μ.restrict sᶜ))) :
    (complexHeightPairingOn m μ a s w g).im =
      heightPairingOn m μ a s w (fun x => (g x).im) := by
  have hi : (∫ q, complexHeightInteriorIntegrand m w g q ∂(μ.restrict s).prod (μ.restrict s)).im =
      ∫ q, fractionalBilinear m w (fun x => (g x).im) q.1 q.2 ∂(μ.restrict s).prod (μ.restrict s) := by
    calc
      _ = ∫ q, (complexHeightInteriorIntegrand m w g q).im ∂(μ.restrict s).prod (μ.restrict s) :=
        (Complex.imCLM.integral_comp_comm hI).symm
      _ = _ := integral_congr_ae (Eventually.of_forall (complex_height_interior_im m w g))
  have hn : (∫ q, complexRenormalizedNormalIntegrand m w g a q
      ∂(μ.restrict s).prod (μ.restrict sᶜ)).im =
      ∫ q, renormalizedNormalIntegrand m w (fun x => (g x).im) a q
        ∂(μ.restrict s).prod (μ.restrict sᶜ) := by
    calc
      _ = ∫ q, (complexRenormalizedNormalIntegrand m w g a q).im
          ∂(μ.restrict s).prod (μ.restrict sᶜ) := (Complex.imCLM.integral_comp_comm hN).symm
      _ = _ := integral_congr_ae (Eventually.of_forall (complex_renormalized_normal_im m w g a))
  unfold complexHeightPairingOn heightPairingOn
  rw [Complex.add_im, Complex.smul_im, hi, hn, smul_eq_mul]

theorem complex_height_pairing_zero_of_real_equations {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s : Set (Ambient d)) (w : Ambient d → ℝ) (g : Ambient d → ℂ)
    (hI : Integrable (complexHeightInteriorIntegrand m w g) ((μ.restrict s).prod (μ.restrict s)))
    (hN : Integrable (complexRenormalizedNormalIntegrand m w g a)
      ((μ.restrict s).prod (μ.restrict sᶜ)))
    (hr : heightPairingOn m μ a s w (fun x => (g x).re) = 0)
    (hi : heightPairingOn m μ a s w (fun x => (g x).im) = 0) :
    complexHeightPairingOn m μ a s w g = 0 := by
  apply Complex.ext
  · rw [complex_height_pairing_re m μ a s w g hI hN, hr]
    rfl
  · rw [complex_height_pairing_im m μ a s w g hI hN, hi]
    rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_ComplexInteriorCutoffLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing the complex interior cutoff

The hard-truncated complex height integrand is the indicator restriction of the
full interior integrand to pairs separated by at least the truncation radius.
Integrability of the full integrand then yields convergence of the truncated
pair integrals as the radii tend to zero.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem complex_height_interior_cutoff_eq_indicator {d : ℕ}
    (m : ℕ) (ε : ℝ) (w : Ambient d → ℝ) (g : Ambient d → ℂ) :
    (fun q : Ambient d × Ambient d => (w q.1 - w q.2) •
      (symmetricFractionalCutoffKernel m ε q • (g q.1 - g q.2))) =
      {q : Ambient d × Ambient d | ε ≤ dist q.1 q.2}.indicator
        (complexHeightInteriorIntegrand m w g) := by
  funext q
  by_cases h : ε ≤ dist q.1 q.2
  · rw [indicator_of_mem (show q ∈ {q : Ambient d × Ambient d | ε ≤ dist q.1 q.2} from h)]
    simp only [symmetricFractionalCutoffKernel, ite_eq_left h, complexHeightInteriorIntegrand]
  · rw [indicator_of_notMem (show q ∉ {q : Ambient d × Ambient d | ε ≤ dist q.1 q.2} from h)]
    simp only [symmetricFractionalCutoffKernel, ite_eq_right h]
    exact (congrArg (fun z : ℂ => (w q.1 - w q.2) • z)
      (zero_smul ℝ (g q.1 - g q.2))).trans (smul_zero (w q.1 - w q.2))

theorem complex_height_interior_cutoff_integral_tendsto {d : ℕ}
    (m : ℕ) (ν : Measure (Ambient d)) (w : Ambient d → ℝ) (g : Ambient d → ℂ)
    (hi : Integrable (complexHeightInteriorIntegrand m w g) (ν.prod ν))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => ∫ q : Ambient d × Ambient d, (w q.1 - w q.2) •
      (symmetricFractionalCutoffKernel m (ε j) q • (g q.1 - g q.2)) ∂ν.prod ν)
      atTop (𝓝 (∫ q, complexHeightInteriorIntegrand m w g q ∂ν.prod ν)) := by
  let F := complexHeightInteriorIntegrand m w g
  let S := fun j => {q : Ambient d × Ambient d | ε j ≤ dist q.1 q.2}
  have hS (j : ℕ) : MeasurableSet (S j) :=
    measurableSet_le measurable_const (continuous_fst.dist continuous_snd).measurable
  have hlim (q : Ambient d × Ambient d) :
      Tendsto (fun j => (S j).indicator F q) atTop (𝓝 (F q)) := by
    by_cases hd : q.1 = q.2
    · have hF : F q = 0 := by
        dsimp only [F, complexHeightInteriorIntegrand]
        rw [hd, sub_self]
        exact zero_smul ℝ _
      have hz : (fun j => (S j).indicator F q) = fun _ : ℕ => (0 : ℂ) := by
        funext j
        by_cases hs : q ∈ S j
        · exact (indicator_of_mem hs F).trans hF
        · exact indicator_of_notMem hs F
      rw [hz, hF]
      exact tendsto_const_nhds
    · have hp := dist_pos.mpr hd
      apply tendsto_const_nhds.congr'
      filter_upwards [hε.eventually (gt_mem_nhds hp)] with j hj
      exact (indicator_of_mem (show q ∈ S j from hj.le) F).symm
  have ht := tendsto_integral_of_dominated_convergence (fun q => ‖F q‖)
    (fun j => hi.aestronglyMeasurable.indicator (hS j)) hi.norm
    (fun j => Eventually.of_forall fun q => norm_indicator_le_norm_self F q)
    (Eventually.of_forall hlim)
  have heq : (fun j => ∫ q : Ambient d × Ambient d, (w q.1 - w q.2) •
      (symmetricFractionalCutoffKernel m (ε j) q • (g q.1 - g q.2)) ∂ν.prod ν) =
      fun j => ∫ q, (S j).indicator F q ∂ν.prod ν := by
    funext j
    rw [complex_height_interior_cutoff_eq_indicator]
  rw [heq]
  exact ht

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_TemperedHeightWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

theorem polynomialDecay_le_one {d : ℕ} (q : ℕ) (x : Ambient d) : polynomialDecay q x ≤ 1 := by
  unfold polynomialDecay
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by linarith [norm_nonneg x] : (1 : ℝ) ≤ 1 + ‖x‖)

theorem polynomialDecay_le_far {d : ℕ} (q : ℕ) (a x : Ambient d) (hx : 0 < dist a x) :
    polynomialDecay q x ≤ (1 + ‖a‖) ^ q * inverseDistancePow q a x := by
  have hd : dist a x ≤ (1 + ‖a‖) * (1 + ‖x‖) := by
    have h : dist a x ≤ ‖a‖ + ‖x‖ := by
      rw [dist_eq_norm]
      exact norm_sub_le a x
    nlinarith [norm_nonneg a, norm_nonneg x, mul_nonneg (norm_nonneg a) (norm_nonneg x)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ dist a x) hd q
  rw [inverseDistancePow, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hx q)).mpr
  calc
    _ ≤ polynomialDecay q x * ((1 + ‖a‖) * (1 + ‖x‖)) ^ q :=
      mul_le_mul_of_nonneg_left hp (polynomialDecay_nonneg q x)
    _ = _ := by
      unfold polynomialDecay
      rw [mul_pow]
      field_simp

theorem polynomial_weight_integrable_from_height_tail {d : ℕ} (q : ℕ)
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f)
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hnear : IntegrableOn f (ball a R) μ)
    (hfar : IntegrableOn (fun x => |f x| * inverseDistancePow q a x) (closedExterior a R) μ) :
    Integrable (fun x => |f x| * polynomialDecay q x) μ := by
  have hm : Measurable (fun x => |f x| * polynomialDecay q x) :=
    hf.abs.mul (polynomialDecay_measurable q)
  have hi : IntegrableOn (fun x => |f x| * polynomialDecay q x) (ball a R) μ := by
    apply hnear.abs.mono' hm.aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (polynomialDecay_nonneg q x))]
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left (polynomialDecay_le_one q x) (abs_nonneg _)
  have ho : IntegrableOn (fun x => |f x| * polynomialDecay q x) (closedExterior a R) μ := by
    apply (hfar.const_mul ((1 + ‖a‖) ^ q)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with x hx
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (polynomialDecay_nonneg q x))]
    calc
      _ ≤ |f x| * ((1 + ‖a‖) ^ q * inverseDistancePow q a x) :=
        mul_le_mul_of_nonneg_left (polynomialDecay_le_far q a x (hR.trans_le hx)) (abs_nonneg _)
      _ = _ := by ring
  have hu := hi.union ho
  rw [closedExterior_eq_compl_ball, union_compl_self, integrableOn_univ] at hu
  exact hu

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_PolynomialDecayBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem polynomial_decay_from_uniform_and_far_bound {d : ℕ} (q : ℕ)
    (f : Ambient d → ℂ) (U D : ℝ) (hU : 0 ≤ U) (hD : 0 ≤ D)
    (hu : ∀ x, ‖f x‖ ≤ U)
    (hd : ∀ x, 0 < ‖x‖ → ‖f x‖ ≤ D / ‖x‖ ^ q) (x : Ambient d) :
    ‖f x‖ ≤ (2 ^ q * (U + D)) * polynomialDecay q x := by
  rw [polynomialDecay, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖x‖) q)).2
  by_cases hx : 1 ≤ ‖x‖
  · have hp : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
    have hb : (1 + ‖x‖) ^ q ≤ (2 * ‖x‖) ^ q :=
      pow_le_pow_left₀ (by positivity) (by linarith) q
    calc
      _ ≤ (D / ‖x‖ ^ q) * (2 * ‖x‖) ^ q :=
        mul_le_mul (hd x hp) hb (by positivity) (div_nonneg hD (by positivity))
      _ = 2 ^ q * D := by
        rw [mul_pow]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith : D ≤ U + D) (by positivity)
  · have hb : (1 + ‖x‖) ^ q ≤ (2 : ℝ) ^ q :=
      pow_le_pow_left₀ (by positivity) (by linarith) q
    calc
      _ ≤ U * 2 ^ q := mul_le_mul (hu x) hb (by positivity) hU
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (by linarith : U ≤ U + D)
          (by positivity : 0 ≤ (2 : ℝ) ^ q)
        simpa only [mul_comm] using! hh

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SchwartzFirstMomentTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set

theorem first_absolute_moment_bound_on_set {d : ℕ}
    (μ : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g μ)
    (hm : Integrable (fun y => ‖y‖ * ‖g y‖) μ)
    (s : Set (Ambient d)) (hs : MeasurableSet s) (R : ℝ) (hR : 0 < R)
    (hsep : ∀ y ∈ s, R ≤ ‖y‖) :
    (∫ y in s, ‖g y‖ ∂μ) ≤ (∫ y, ‖y‖ * ‖g y‖ ∂μ) / R := by
  calc
    _ ≤ ∫ y in s, (‖y‖ * ‖g y‖) / R ∂μ := by
      apply integral_mono_ae hg.norm.restrict (hm.div_const R).restrict
      filter_upwards [ae_restrict_mem hs] with y hy
      apply (le_div_iff₀ hR).2
      nlinarith [mul_le_mul_of_nonneg_right (hsep y hy) (norm_nonneg (g y))]
    _ = (∫ y in s, ‖y‖ * ‖g y‖ ∂μ) / R := integral_div R _
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hR.le
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg y) (norm_nonneg (g y))) hm

theorem schwartz_first_absolute_moment_integrable {d : ℕ} (g : 𝓢(Ambient d, ℂ)) :
    Integrable (fun y : Ambient d => ‖y‖ * ‖g y‖) := by
  simpa only [pow_one] using! g.integrable_pow_mul (volume : Measure (Ambient d)) 1

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_SchwartzMomentContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Filter Topology

theorem schwartz_first_absolute_moment_seminorm_bound {d : ℕ} (g : 𝓢(Ambient d, ℂ)) :
    (∫ y : Ambient d, ‖y‖ * ‖g y‖) ≤
      2 ^ (volume : Measure (Ambient d)).integrablePower *
        (∫ y : Ambient d, (1 + ‖y‖) ^ (-((volume : Measure (Ambient d)).integrablePower : ℝ))) *
        (SchwartzMap.seminorm ℝ 0 0 g +
          SchwartzMap.seminorm ℝ (1 + (volume : Measure (Ambient d)).integrablePower) 0 g) := by
  simpa only [pow_one, norm_iteratedFDeriv_zero] using!
    SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ (volume : Measure (Ambient d)) g 1 0

theorem schwartz_seminorm_tendsto_zero {d : ℕ} (G : ℕ → 𝓢(Ambient d, ℂ))
    (ht : Tendsto G atTop (𝓝 0)) (k n : ℕ) :
    Tendsto (fun j => SchwartzMap.seminorm ℝ k n (G j)) atTop (𝓝 0) := by
  simpa only [schwartzSeminormFamily_apply, map_zero] using!
    ((schwartz_withSeminorms ℝ (Ambient d) ℂ).continuous_seminorm (k, n)).tendsto 0 |>.comp ht

theorem schwartz_first_absolute_moment_tendsto_zero {d : ℕ}
    (G : ℕ → 𝓢(Ambient d, ℂ)) (ht : Tendsto G atTop (𝓝 0)) :
    Tendsto (fun j => ∫ y : Ambient d, ‖y‖ * ‖G j y‖) atTop (𝓝 0) := by
  let C := 2 ^ (volume : Measure (Ambient d)).integrablePower *
    (∫ y : Ambient d, (1 + ‖y‖) ^ (-((volume : Measure (Ambient d)).integrablePower : ℝ)))
  have h0 := schwartz_seminorm_tendsto_zero G ht 0 0
  have h1 := schwartz_seminorm_tendsto_zero G ht
    (1 + (volume : Measure (Ambient d)).integrablePower) 0
  have hb : Tendsto (fun j => C * (SchwartzMap.seminorm ℝ 0 0 (G j) +
      SchwartzMap.seminorm ℝ (1 + (volume : Measure (Ambient d)).integrablePower) 0 (G j)))
      atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using! (h0.add h1).const_mul C
  exact squeeze_zero (fun j => integral_nonneg fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun j => schwartz_first_absolute_moment_seminorm_bound (G j)) hb

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SubtractedFarTestEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# First-moment control of the subtracted far test

The far-region integral splits at the ball of radius `‖x‖ / 2` about the origin.
The central part uses the kernel difference estimate, while the outer part uses
the first absolute moment to gain the same decay of order `‖x‖ ^ (m + 2)`.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set

theorem subtracted_far_test_integral_norm_bound {d : ℕ}
    (μ : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g μ)
    (hm : Integrable (fun y => ‖y‖ * ‖g y‖) μ) (m : ℕ)
    (x : Ambient d) (hx : 0 < ‖x‖) :
    (∫ y in closedExterior x (‖x‖ / 2),
      ‖(inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x) • g y‖ ∂μ) ≤
      (((m + 1 : ℝ) * 2 ^ (m + 2) + 2 ^ (m + 3)) *
        (∫ y, ‖y‖ * ‖g y‖ ∂μ)) / ‖x‖ ^ (m + 2) := by
  let R := ‖x‖ / 2
  let E := closedExterior x R
  let B := closedBall (0 : Ambient d) R
  let F := fun y => (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x) • g y
  let M := ∫ y, ‖y‖ * ‖g y‖ ∂μ
  let D := (m + 1 : ℝ) * 2 ^ (m + 2) * inverseDistancePow (m + 2) 0 x
  let A := 2 * (R ^ (m + 1))⁻¹
  have hR : 0 < R := by dsimp [R] <;> positivity
  have hxR : R ≤ ‖x‖ := by dsimp [R] <;> linarith
  have hD : 0 ≤ D := mul_nonneg (by positivity) (inverseDistancePow_nonneg _ _ _)
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  have hF : IntegrableOn F E μ := subtracted_far_test_kernel_integrable μ g hg m x R hR hxR
  have hcentral : (∫ y in E ∩ B, ‖F y‖ ∂μ) ≤ D * M := by
    have hf : IntegrableOn (fun y => ‖F y‖) (E ∩ B) μ :=
      hF.norm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
    have hmi := hm.restrict (s := E ∩ B)
    calc
      _ ≤ ∫ y in E ∩ B, D * (‖y‖ * ‖g y‖) ∂μ := by
        apply integral_mono_ae hf (hmi.const_mul D)
        filter_upwards [ae_restrict_mem ((closedExterior_measurable x R).inter measurableSet_closedBall)] with y hy
        have hyR : ‖y‖ ≤ ‖x‖ / 2 := by simpa only [B, mem_closedBall, dist_zero_right] using! hy.2
        have hb := subtracted_far_test_kernel_central_bound m x y hx hyR
        change ‖(inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x) • g y‖ ≤ _
        rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
        calc
          _ ≤ ((m + 1 : ℝ) * 2 ^ (m + 2) * ‖y‖ * inverseDistancePow (m + 2) 0 x) * ‖g y‖ :=
            mul_le_mul_of_nonneg_right hb (norm_nonneg _)
          _ = _ := by dsimp [D] <;> ring
      _ = D * (∫ y in E ∩ B, ‖y‖ * ‖g y‖ ∂μ) := integral_const_mul _ _
      _ ≤ D * M := mul_le_mul_of_nonneg_left
        (integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg y) (norm_nonneg (g y))) hm) hD
  have houter : (∫ y in E \ B, ‖F y‖ ∂μ) ≤ A * (M / R) := by
    have hf : IntegrableOn (fun y => ‖F y‖) (E \ B) μ :=
      hF.norm.mono_measure (Measure.restrict_mono sdiff_subset le_rfl)
    have hsep : ∀ y ∈ E \ B, R ≤ ‖y‖ := by
      intro y hy
      exact (lt_of_not_ge (by simpa only [B, mem_closedBall, dist_zero_right] using! hy.2)).le
    have ht := first_absolute_moment_bound_on_set μ g hg hm (E \ B)
      ((closedExterior_measurable x R).diff measurableSet_closedBall) R hR hsep
    calc
      _ ≤ ∫ y in E \ B, A * ‖g y‖ ∂μ := by
        apply integral_mono_ae hf (hg.norm.restrict.const_mul A)
        filter_upwards [ae_restrict_mem ((closedExterior_measurable x R).diff measurableSet_closedBall)] with y hy
        change ‖(inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) 0 x) • g y‖ ≤ _
        rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
        exact mul_le_mul_of_nonneg_right (subtracted_far_test_kernel_uniform_bound m x y R hR hxR hy.1)
          (norm_nonneg _)
      _ = A * (∫ y in E \ B, ‖g y‖ ∂μ) := integral_const_mul _ _
      _ ≤ A * (M / R) := mul_le_mul_of_nonneg_left ht hA
  calc
    _ = (∫ y in E ∩ B, ‖F y‖ ∂μ) + ∫ y in E \ B, ‖F y‖ ∂μ :=
      (integral_inter_add_sdiff measurableSet_closedBall hF.norm).symm
    _ ≤ D * M + A * (M / R) := add_le_add hcentral houter
    _ = _ := by
      dsimp [D, A, R, M]
      simp only [inverseDistancePow, dist_zero_left, pow_add, div_pow]
      field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_MeanZeroFarTestEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean-zero decay of the far test integral

Subtracting the kernel value at the origin exposes a first-moment bound.
The mean-zero hypothesis replaces the remaining far-region integral by its
complement, whose distance from the origin gives the same extra decay power.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set

theorem mean_zero_far_test_integral_bound {d : ℕ}
    (μ : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g μ)
    (hm : Integrable (fun y => ‖y‖ * ‖g y‖) μ) (hmean : (∫ y, g y ∂μ) = 0)
    (m : ℕ) (x : Ambient d) (hx : 0 < ‖x‖) :
    ‖∫ y in closedExterior x (‖x‖ / 2), inverseDistancePow (m + 1) x y • g y ∂μ‖ ≤
      (((m + 1 : ℝ) * 2 ^ (m + 2) + 2 ^ (m + 3) + 2) *
        (∫ y, ‖y‖ * ‖g y‖ ∂μ)) / ‖x‖ ^ (m + 2) := by
  let R := ‖x‖ / 2
  let E := closedExterior x R
  let K := inverseDistancePow (m + 1) 0 x
  let F := fun y => (inverseDistancePow (m + 1) x y - K) • g y
  let M := ∫ y, ‖y‖ * ‖g y‖ ∂μ
  have hR : 0 < R := by dsimp [R] <;> positivity
  have hE : MeasurableSet E := closedExterior_measurable x R
  have hK : 0 ≤ K := inverseDistancePow_nonneg _ _ _
  have hF : IntegrableOn F E μ := subtracted_far_test_kernel_integrable μ g hg m x R hR
    (by dsimp [R] <;> linarith)
  have hmissing : (∫ y in Eᶜ, ‖g y‖ ∂μ) ≤ M / R := by
    apply first_absolute_moment_bound_on_set μ g hg hm Eᶜ hE.compl R hR
    intro y hy
    have hd : dist x y < R := by
      simpa only [E, closedExterior, mem_compl_iff, mem_ofPred_eq, not_le] using! hy
    have hn := norm_sub_norm_le x y
    rw [← dist_eq_norm] at hn
    dsimp [R] at hd ⊢
    linarith
  have hmeanE : (∫ y in E, g y ∂μ) = -(∫ y in Eᶜ, g y ∂μ) := by
    apply eq_neg_iff_add_eq_zero.mpr
    exact (integral_add_compl hE hg).trans hmean
  have hdecomp : (∫ y in E, inverseDistancePow (m + 1) x y • g y ∂μ) =
      (∫ y in E, F y ∂μ) + K • (∫ y in E, g y ∂μ) := by
    have heq : (fun y => inverseDistancePow (m + 1) x y • g y) = fun y => F y + K • g y := by
      funext y
      dsimp only [F]
      simp only [RCLike.real_smul_eq_coe_mul, map_sub]
      ring
    have hKg : IntegrableOn (fun y => K • g y) E μ := hg.restrict.smul K
    rw [heq, integral_add hF hKg]
    congr 1
    exact integral_smul K g
  have hsub := (norm_integral_le_integral_norm (μ := μ.restrict E) F).trans
    (subtracted_far_test_integral_norm_bound μ g hg hm m x hx)
  have hcorrection : ‖K • (-(∫ y in Eᶜ, g y ∂μ))‖ ≤ K * (M / R) := by
    rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hK, norm_neg]
    exact mul_le_mul_of_nonneg_left
      ((norm_integral_le_integral_norm (μ := μ.restrict Eᶜ) g).trans hmissing) hK
  rw [hdecomp, hmeanE]
  calc
    _ ≤ ‖∫ y in E, F y ∂μ‖ + ‖K • (-(∫ y in Eᶜ, g y ∂μ))‖ := norm_add_le _ _
    _ ≤ (((m + 1 : ℝ) * 2 ^ (m + 2) + 2 ^ (m + 3)) * M) / ‖x‖ ^ (m + 2) + K * (M / R) :=
      add_le_add hsub hcorrection
    _ = _ := by
      dsimp [K, R, M]
      simp only [inverseDistancePow, dist_zero_left, pow_add]
      field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalFarSpatialDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Set

theorem far_kernel_mass_times_schwartz_value {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth m C μ)
    (g : 𝓢(Ambient d, ℂ)) (x : Ambient d) (hx : 0 < ‖x‖) :
    ‖(∫ h in closedExterior (0 : Ambient d) (‖x‖ / 2),
      inverseDistancePow (m + 1) 0 h ∂μ) • g x‖ ≤
      (4 * C * 2 ^ m * SchwartzMap.seminorm ℝ (m + 1) 0 g) / ‖x‖ ^ (m + 2) := by
  have hR : 0 < ‖x‖ / 2 := by positivity
  have hC := hgrowth.1
  have hI : 0 ≤ ∫ h in closedExterior (0 : Ambient d) (‖x‖ / 2),
      inverseDistancePow (m + 1) 0 h ∂μ := integral_nonneg fun h => inverseDistancePow_nonneg _ _ _
  have htail := (inverseDistancePow_closedExterior_integrable_and_bound m C μ
    hgrowth 0 (‖x‖ / 2) hR).2
  have hg : ‖g x‖ ≤ SchwartzMap.seminorm ℝ (m + 1) 0 g / ‖x‖ ^ (m + 1) := by
    apply (le_div_iff₀ (pow_pos hx _)).2
    simpa only [mul_comm] using! SchwartzMap.norm_pow_mul_le_seminorm ℝ g (m + 1) x
  rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hI]
  calc
    _ ≤ (2 * (C * 2 ^ m / (‖x‖ / 2))) *
        (SchwartzMap.seminorm ℝ (m + 1) 0 g / ‖x‖ ^ (m + 1)) :=
      mul_le_mul htail hg (norm_nonneg _) (by positivity)
    _ = _ := by
      simp only [pow_add]
      field_simp
      ring

theorem fractionalSchwartz_far_spatial_decay (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (hmean : (∫ y, g y) = 0) (x : Ambient (p + 1)) (hx : 0 < ‖x‖) :
    ‖(-1 / 2 : ℝ) • (∫ h in closedExterior 0 (‖x‖ / 2),
      fractionalSchwartzKernel (p + 1) g x h)‖ ≤
      (4 * (((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal) * 2 ^ (p + 1) *
          SchwartzMap.seminorm ℝ (p + 2) 0 g +
        (((p + 1 : ℝ) + 1) * 2 ^ (p + 3) + 2 ^ (p + 4) + 2) *
          (∫ y : Ambient (p + 1), ‖y‖ * ‖g y‖)) / ‖x‖ ^ (p + 3) := by
  rw [fractionalSchwartz_far_integral_identity p g x (‖x‖ / 2) (by positivity)]
  have hmass := far_kernel_mass_times_schwartz_value (p + 1) _ volume
    (volume_global_upper_growth (p + 1)) g x hx
  have hraw := mean_zero_far_test_integral_bound volume g g.integrable
    (schwartz_first_absolute_moment_integrable g) hmean (p + 1) x hx
  have hn := norm_sub_le
    ((∫ h in closedExterior (0 : Ambient (p + 1)) (‖x‖ / 2),
      inverseDistancePow (p + 1 + 1) 0 h) • g x)
    (∫ y in closedExterior x (‖x‖ / 2), inverseDistancePow (p + 1 + 1) x y • g y)
  simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one, ← add_div] using!
    hn.trans (add_le_add hmass hraw)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LocalSchwartzSecondDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set
open scoped NNReal

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem first_order_remainder_from_segment_hessian
    (g : Ambient d → F) (hg : Differentiable ℝ g)
    (hdg : Differentiable ℝ (fderiv ℝ g)) (M : ℝ) (hM : 0 ≤ M)
    (x h : Ambient d)
    (hbound : ∀ z ∈ segment ℝ x (x + h), ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ M) :
    ‖g (x + h) - g x - fderiv ℝ g x h‖ ≤ M * ‖h‖ ^ 2 := by
  have hgrad : ∀ z ∈ segment ℝ x (x + h),
      ‖fderiv ℝ g z - fderiv ℝ g x‖ ≤ M * ‖h‖ := by
    intro z hz
    have hh := (convex_segment x (x + h)).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hdg y) hbound (left_mem_segment ℝ x (x + h)) hz
    calc
      _ ≤ M * ‖z - x‖ := hh
      _ ≤ M * ‖h‖ := mul_le_mul_of_nonneg_left
        (by simpa only [add_sub_cancel_left] using! norm_sub_le_of_mem_segment hz) hM
  have hh := (convex_segment x (x + h)).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => hg y) hgrad (left_mem_segment ℝ x (x + h)) (right_mem_segment ℝ x (x + h))
  simpa only [add_sub_cancel_left, pow_two, mul_assoc] using! hh

theorem schwartz_hessian_bound_on_short_segment
    (g : 𝓢(Ambient d, F)) (k : ℕ) (x h : Ambient d) (hx : 0 < ‖x‖)
    (hh : ‖h‖ ≤ ‖x‖ / 2) (z : Ambient d) (hz : z ∈ segment ℝ x (x + h)) :
    ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ SchwartzMap.seminorm ℝ k 2 g / (‖x‖ / 2) ^ k := by
  have hzx : ‖z - x‖ ≤ ‖h‖ := by
    simpa only [add_sub_cancel_left] using! norm_sub_le_of_mem_segment hz
  have hnorm := norm_sub_norm_le x z
  rw [norm_sub_rev x z] at hnorm
  have hzlow : ‖x‖ / 2 ≤ ‖z‖ := by linarith
  have hbase : 0 < ‖x‖ / 2 := by positivity
  have he : ‖fderiv ℝ (fderiv ℝ g) z‖ = ‖iteratedFDeriv ℝ 2 g z‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  rw [he]
  apply (le_div_iff₀ (pow_pos hbase k)).2
  calc
    _ = (‖x‖ / 2) ^ k * ‖iteratedFDeriv ℝ 2 g z‖ := mul_comm _ _
    _ ≤ ‖z‖ ^ k * ‖iteratedFDeriv ℝ 2 g z‖ := by gcongr
    _ ≤ _ := le_seminorm ℝ k 2 g z

theorem schwartz_second_difference_spatial_bound
    (g : 𝓢(Ambient d, F)) (k : ℕ) (x h : Ambient d) (hx : 0 < ‖x‖)
    (hh : ‖h‖ ≤ ‖x‖ / 2) :
    ‖symmetricSecondDifference g x h‖ ≤
      2 * (SchwartzMap.seminorm ℝ k 2 g / (‖x‖ / 2) ^ k) * ‖h‖ ^ 2 := by
  let M := SchwartzMap.seminorm ℝ k 2 g / (‖x‖ / 2) ^ k
  have hM : 0 ≤ M := by dsimp [M] <;> positivity
  have hdg : Differentiable ℝ (fderiv ℝ g) :=
    (fderivCLM ℝ (Ambient d) F g).differentiable
  have hp := first_order_remainder_from_segment_hessian g g.differentiable hdg M hM x h
    (schwartz_hessian_bound_on_short_segment g k x h hx hh)
  have hn : ‖-h‖ ≤ ‖x‖ / 2 := by simpa only [norm_neg] using! hh
  have hm := first_order_remainder_from_segment_hessian g g.differentiable hdg M hM x (-h)
    (schwartz_hessian_bound_on_short_segment g k x (-h) hx hn)
  have heq : symmetricSecondDifference g x h =
      (g (x + h) - g x - fderiv ℝ g x h) +
      (g (x + -h) - g x - fderiv ℝ g x (-h)) := by
    simp only [symmetricSecondDifference, map_neg, sub_eq_add_neg, two_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖g (x + h) - g x - fderiv ℝ g x h‖ +
        ‖g (x + -h) - g x - fderiv ℝ g x (-h)‖ := norm_add_le _ _
    _ ≤ M * ‖h‖ ^ 2 + M * ‖-h‖ ^ 2 := add_le_add hp hm
    _ = _ := by rw [norm_neg]; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalNearSpatialDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

theorem fractional_kernel_bound_from_quadratic_difference {d : ℕ}
    (p : ℕ) (g : Ambient d → ℂ) (x h : Ambient d) (M : ℝ) (hM : 0 ≤ M)
    (hb : ‖symmetricSecondDifference g x h‖ ≤ M * ‖h‖ ^ 2) :
    ‖fractionalSchwartzKernel (p + 1) g x h‖ ≤ M * inverseDistancePow p 0 h := by
  rw [fractionalSchwartzKernel, norm_smul,
    Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  by_cases hh : h = 0
  · subst h
    simp only [inverseDistancePow, dist_self, zero_pow (by omega : p + 1 + 1 ≠ 0), inv_zero, zero_mul]
    positivity
  · have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh
    calc
      _ ≤ inverseDistancePow (p + 1 + 1) 0 h * (M * ‖h‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hb (inverseDistancePow_nonneg _ _ _)
      _ = _ := by
        simp only [inverseDistancePow, dist_zero_left, pow_succ]
        field_simp

theorem fractionalSchwartzKernel_near_spatial_decay {d : ℕ}
    (p : ℕ) (C : ℝ) (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth (p + 1) C μ)
    (g : 𝓢(Ambient d, ℂ)) (x : Ambient d) (hx : 0 < ‖x‖) :
    (∫ h in closedBall 0 (‖x‖ / 2), ‖fractionalSchwartzKernel (p + 1) g x h‖ ∂μ) ≤
      (4 * (C * 2 ^ (p + 1) * 2 ^ p) * 2 ^ (p + 3) *
        SchwartzMap.seminorm ℝ (p + 4) 2 g) / ‖x‖ ^ (p + 3) := by
  let R := ‖x‖ / 2
  let M := SchwartzMap.seminorm ℝ (p + 4) 2 g / R ^ (p + 4)
  have hR : 0 < R := by dsimp [R] <;> positivity
  have hM : 0 ≤ M := by dsimp [M] <;> positivity
  have hK := fractionalSchwartzKernel_integrable_of_growth p C μ hgrowth g x
  obtain ⟨hi, _⟩ := inverseDistancePow_near_integrable_and_bound p C μ hgrowth 0 R hR
  have hb' : (∫ h in closedBall 0 R, inverseDistancePow p 0 h ∂μ) ≤
      2 * (C * 2 ^ (p + 1) * 2 ^ p * R) :=
    inverseDistancePow_near_integral_bound p C μ hgrowth 0 R hR
  calc
    _ ≤ ∫ h in closedBall 0 R, (2 * M) * inverseDistancePow p 0 h ∂μ := by
      apply integral_mono_ae hK.norm.restrict (hi.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with h hh
      have hh' : ‖h‖ ≤ ‖x‖ / 2 := by simpa only [mem_closedBall, dist_zero_right] using! hh
      exact fractional_kernel_bound_from_quadratic_difference p g x h (2 * M) (by positivity)
        (schwartz_second_difference_spatial_bound g (p + 4) x h hx hh')
    _ = (2 * M) * ∫ h in closedBall 0 R, inverseDistancePow p 0 h ∂μ := integral_const_mul _ _
    _ ≤ (2 * M) * (2 * (C * 2 ^ (p + 1) * 2 ^ p * R)) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by
      dsimp [M, R]
      simp only [pow_add, div_pow]
      field_simp
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalSpatialDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Set

theorem fractionalSchwartzDecaySize_nonneg (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ)) :
    0 ≤ fractionalSchwartzDecaySize p g := by
  unfold fractionalSchwartzDecaySize
  positivity

theorem fractionalSchwartzTest_spatial_decay (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (hmean : (∫ y, g y) = 0) (x : Ambient (p + 1)) (hx : 0 < ‖x‖) :
    ‖fractionalSchwartzTest p g x‖ ≤ fractionalSchwartzDecaySize p g / ‖x‖ ^ (p + 3) := by
  let C := ((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal
  let N := 4 * (C * 2 ^ (p + 1) * 2 ^ p) * 2 ^ (p + 3) *
    SchwartzMap.seminorm ℝ (p + 4) 2 g
  let R := ‖x‖ / 2
  let K := fractionalSchwartzKernel (p + 1) g x
  have hi : Integrable K := fractionalSchwartzKernel_integrable p g x
  have hsplit : (∫ h, K h) = (∫ h in ball 0 R, K h) +
      (∫ h in closedExterior 0 R, K h) := by
    rw [closedExterior_eq_compl_ball]
    exact (integral_add_compl measurableSet_ball hi).symm
  have hnear : ‖(-1 / 2 : ℝ) • (∫ h in ball 0 R, K h)‖ ≤ N / ‖x‖ ^ (p + 3) := by
    calc
      _ ≤ ‖∫ h in ball 0 R, K h‖ := by
        rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
        norm_num
        linarith [norm_nonneg (∫ h in ball 0 R, K h)]
      _ ≤ ∫ h in ball 0 R, ‖K h‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ h in closedBall 0 R, ‖K h‖ :=
        integral_mono_measure (Measure.restrict_mono ball_subset_closedBall le_rfl)
          (Filter.Eventually.of_forall fun h => norm_nonneg (K h)) hi.norm.restrict
      _ ≤ _ := fractionalSchwartzKernel_near_spatial_decay p C volume
        (volume_global_upper_growth (p + 1)) g x hx
  have hfar := fractionalSchwartz_far_spatial_decay p g hmean x hx
  have he : fractionalSchwartzTest p g x =
      (-1 / 2 : ℝ) • (∫ h in ball 0 R, K h) +
      (-1 / 2 : ℝ) • (∫ h in closedExterior 0 R, K h) := by
    change (-1 / 2 : ℝ) • (∫ h, K h) = _
    rw [hsplit]
    exact smul_add (-1 / 2 : ℝ) _ _
  rw [he]
  calc
    _ ≤ ‖(-1 / 2 : ℝ) • (∫ h in ball 0 R, K h)‖ +
        ‖(-1 / 2 : ℝ) • (∫ h in closedExterior 0 R, K h)‖ := norm_add_le _ _
    _ ≤ _ := by
      have hh := add_le_add hnear hfar
      simpa only [← add_div, N, C, fractionalSchwartzDecaySize] using! hh

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalWeightedDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology

theorem fractionalSchwartzTest_polynomial_decay (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (hmean : (∫ y, g y) = 0) (x : Ambient (p + 1)) :
    ‖fractionalSchwartzTest p g x‖ ≤
      fractionalSchwartzWeightedSize p g * polynomialDecay (p + 3) x := by
  apply polynomial_decay_from_uniform_and_far_bound (p + 3) (fractionalSchwartzTest p g)
    (fractionalSchwartzUniformSize p g) (fractionalSchwartzDecaySize p g)
  · unfold fractionalSchwartzUniformSize
    positivity
  · exact fractionalSchwartzDecaySize_nonneg p g
  · exact fractionalSchwartzTest_uniform_bound p g
  · exact fractionalSchwartzTest_spatial_decay p g hmean

theorem fractionalSchwartzWeightedSize_tendsto_zero (p : ℕ)
    (G : ℕ → 𝓢(Ambient (p + 1), ℂ)) (ht : Tendsto G atTop (𝓝 0)) :
    Tendsto (fun j => fractionalSchwartzWeightedSize p (G j)) atTop (𝓝 0) := by
  let C := ((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal
  have hsem := schwartz_seminorm_tendsto_zero G ht
  have hmoment := schwartz_first_absolute_moment_tendsto_zero G ht
  have hU : Tendsto (fun j => fractionalSchwartzUniformSize p (G j)) atTop (𝓝 0) := by
    simpa only [fractionalSchwartzUniformSize, C, mul_zero, add_zero] using!
      ((hsem 0 2).const_mul (4 * (C * 2 ^ (p + 1) * 2 ^ p))).add
        ((hsem 0 0).const_mul (8 * (C * 2 ^ (p + 1))))
  have hD : Tendsto (fun j => fractionalSchwartzDecaySize p (G j)) atTop (𝓝 0) := by
    simpa only [fractionalSchwartzDecaySize, C, mul_zero, add_zero] using!
      ((hsem (p + 4) 2).const_mul (4 * (C * 2 ^ (p + 1) * 2 ^ p) * 2 ^ (p + 3))).add
        (((hsem (p + 2) 0).const_mul (4 * C * 2 ^ (p + 1))).add
          (hmoment.const_mul (((p + 1 : ℝ) + 1) * 2 ^ (p + 3) + 2 ^ (p + 4) + 2)))
  simpa only [fractionalSchwartzWeightedSize, add_zero, mul_zero] using!
    (hU.add hD).const_mul ((2 : ℝ) ^ (p + 3))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalHeightPairingContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology

theorem height_fractional_test_integrable_and_bound (p : ℕ)
    (μ : Measure (Ambient (p + 1))) (f : Ambient (p + 1) → ℝ) (hf : Measurable f)
    (hweight : Integrable (fun x => |f x| * polynomialDecay (p + 3) x) μ)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hmean : (∫ y, g y) = 0) :
    Integrable (fun x => f x • fractionalSchwartzTest p g x) μ ∧
      ‖∫ x, f x • fractionalSchwartzTest p g x ∂μ‖ ≤
        fractionalSchwartzWeightedSize p g * (∫ x, |f x| * polynomialDecay (p + 3) x ∂μ) := by
  let W := fractionalSchwartzWeightedSize p g
  have hm : Measurable (fun x => f x • fractionalSchwartzTest p g x) := by
    simp_rw [RCLike.real_smul_eq_coe_mul]
    exact (Complex.continuous_ofReal.measurable.comp hf).mul (fractionalSchwartzTest_measurable p g)
  have hb (x : Ambient (p + 1)) : ‖f x • fractionalSchwartzTest p g x‖ ≤
      W * (|f x| * polynomialDecay (p + 3) x) := by
    rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
    calc
      _ ≤ |f x| * (W * polynomialDecay (p + 3) x) :=
        mul_le_mul_of_nonneg_left (fractionalSchwartzTest_polynomial_decay p g hmean x) (abs_nonneg _)
      _ = _ := by ring
  have hi : Integrable (fun x => W * (|f x| * polynomialDecay (p + 3) x)) μ := hweight.const_mul W
  have hp : Integrable (fun x => f x • fractionalSchwartzTest p g x) μ :=
    hi.mono' hm.aestronglyMeasurable (Eventually.of_forall hb)
  refine ⟨hp, ?_⟩
  calc
    _ ≤ ∫ x, ‖f x • fractionalSchwartzTest p g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, W * (|f x| * polynomialDecay (p + 3) x) ∂μ := integral_mono hp.norm hi hb
    _ = _ := integral_const_mul W _

theorem height_fractional_test_integral_tendsto (p : ℕ)
    (μ : Measure (Ambient (p + 1))) (f : Ambient (p + 1) → ℝ) (hf : Measurable f)
    (hweight : Integrable (fun x => |f x| * polynomialDecay (p + 3) x) μ)
    (G : ℕ → 𝓢(Ambient (p + 1), ℂ)) (g : 𝓢(Ambient (p + 1), ℂ))
    (ht : Tendsto G atTop (𝓝 g)) (hG : ∀ j, (∫ y, G j y) = 0) (hg : (∫ y, g y) = 0) :
    Tendsto (fun j => ∫ x, f x • fractionalSchwartzTest p (G j) x ∂μ)
      atTop (𝓝 (∫ x, f x • fractionalSchwartzTest p g x ∂μ)) := by
  let H := fun j => G j - g
  have hHt : Tendsto H atTop (𝓝 0) := by
    simpa only [sub_self] using! ht.sub (tendsto_const_nhds (x := g))
  have hHm (j : ℕ) : (∫ y, H j y) = 0 := by
    change (∫ y, G j y - g y) = 0
    rw [integral_sub (G j).integrable g.integrable, hG j, hg, sub_self]
  have hIG (j : ℕ) := (height_fractional_test_integrable_and_bound p μ f hf hweight (G j) (hG j)).1
  have hIg := (height_fractional_test_integrable_and_bound p μ f hf hweight g hg).1
  have hdiff (j : ℕ) : (∫ x, f x • fractionalSchwartzTest p (G j) x ∂μ) -
      (∫ x, f x • fractionalSchwartzTest p g x ∂μ) =
      ∫ x, f x • fractionalSchwartzTest p (H j) x ∂μ := by
    refine (integral_sub (hIG j) hIg).symm.trans (integral_congr_ae (Eventually.of_forall ?_))
    intro x
    calc
      _ = f x • (fractionalSchwartzTest p (G j) x - fractionalSchwartzTest p g x) :=
        (smul_sub (f x) (fractionalSchwartzTest p (G j) x) (fractionalSchwartzTest p g x)).symm
      _ = _ := congrArg (fun z : ℂ => f x • z)
        ((fractionalSchwartzTestCLM p x).map_sub (G j) g).symm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb (j : ℕ) :
      ‖(∫ x, f x • fractionalSchwartzTest p (G j) x ∂μ) -
        (∫ x, f x • fractionalSchwartzTest p g x ∂μ)‖ ≤
      fractionalSchwartzWeightedSize p (H j) *
        (∫ x, |f x| * polynomialDecay (p + 3) x ∂μ) := by
    rw [hdiff j]
    exact (height_fractional_test_integrable_and_bound p μ f hf hweight (H j) (hHm j)).2
  apply squeeze_zero (fun j => norm_nonneg _) hb
  simpa only [zero_mul] using! (fractionalSchwartzWeightedSize_tendsto_zero p H hHt).mul_const
    (∫ x, |f x| * polynomialDecay (p + 3) x ∂μ)

theorem height_fractional_test_zero_on_mean_zero_tests (p : ℕ)
    (μ : Measure (Ambient (p + 1))) (f : Ambient (p + 1) → ℝ) (hf : Measurable f)
    (hweight : Integrable (fun x => |f x| * polynomialDecay (p + 3) x) μ)
    (hcompact : ∀ g : 𝓢(Ambient (p + 1), ℂ), HasCompactSupport g → (∫ y, g y) = 0 →
      (∫ x, f x • fractionalSchwartzTest p g x ∂μ) = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hg : (∫ y, g y) = 0) :
    (∫ x, f x • fractionalSchwartzTest p g x ∂μ) = 0 := by
  obtain ⟨G, hG, ht⟩ := exists_compact_mean_zero_schwartz_approximation g hg
  have hlim := height_fractional_test_integral_tendsto p μ f hf hweight G g ht
    (fun j => (hG j).2) hg
  have hz : (fun j => ∫ x, f x • fractionalSchwartzTest p (G j) x ∂μ) =
      fun _ : ℕ => (0 : ℂ) := funext fun j => hcompact (G j) (hG j).1 (hG j).2
  rw [hz] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalTruncatedSpatialDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spatial decay of truncated fractional tests

For a mean-zero Schwartz function, split the truncated fractional kernel integral
at half the observation-point norm. The local second-difference estimate and the
far-field cancellation bound give decay uniform in smaller truncation radii.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Set

theorem fractionalSchwartzTruncatedTest_spatial_decay (p : ℕ) (ε : ℝ)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hmean : (∫ y, g y) = 0)
    (x : Ambient (p + 1)) (hx : 0 < ‖x‖) (hε : ε ≤ ‖x‖ / 2) :
    ‖fractionalSchwartzTruncatedTest p ε g x‖ ≤
      fractionalSchwartzDecaySize p g / ‖x‖ ^ (p + 3) := by
  let C := ((volume : Measure (Ambient (p + 1))) (ball 0 1)).toReal
  let N := 4 * (C * 2 ^ (p + 1) * 2 ^ p) * 2 ^ (p + 3) *
    SchwartzMap.seminorm ℝ (p + 4) 2 g
  let R := ‖x‖ / 2
  let E : Set (Ambient (p + 1)) := closedExterior 0 ε
  let K := fractionalSchwartzKernel (p + 1) g x
  have hi : Integrable K := fractionalSchwartzKernel_integrable p g x
  have he : E \ ball 0 R = closedExterior 0 R := by
    rw [sdiff_eq, ← closedExterior_eq_compl_ball]
    apply inter_eq_right.mpr
    intro h hh
    exact hε.trans hh
  have hsplit : (∫ h in E, K h) = (∫ h in E ∩ ball 0 R, K h) +
      (∫ h in closedExterior 0 R, K h) := by
    have hh := integral_inter_add_sdiff (t := ball 0 R) measurableSet_ball (hi.restrict (s := E))
    rw [he] at hh
    exact hh.symm
  have hnear : ‖(-1 / 2 : ℝ) • (∫ h in E ∩ ball 0 R, K h)‖ ≤ N / ‖x‖ ^ (p + 3) := by
    calc
      _ ≤ ‖∫ h in E ∩ ball 0 R, K h‖ := by
        rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
        norm_num
        linarith [norm_nonneg (∫ h in E ∩ ball 0 R, K h)]
      _ ≤ ∫ h in E ∩ ball 0 R, ‖K h‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ h in closedBall 0 R, ‖K h‖ :=
        integral_mono_measure
          (Measure.restrict_mono (inter_subset_right.trans ball_subset_closedBall) le_rfl)
          (Filter.Eventually.of_forall fun h => norm_nonneg (K h)) hi.norm.restrict
      _ ≤ _ := fractionalSchwartzKernel_near_spatial_decay p C volume
        (volume_global_upper_growth (p + 1)) g x hx
  have hfar := fractionalSchwartz_far_spatial_decay p g hmean x hx
  have hform : fractionalSchwartzTruncatedTest p ε g x =
      (-1 / 2 : ℝ) • (∫ h in E ∩ ball 0 R, K h) +
      (-1 / 2 : ℝ) • (∫ h in closedExterior 0 R, K h) := by
    change (-1 / 2 : ℝ) • (∫ h in E, K h) = _
    rw [hsplit]
    exact smul_add (-1 / 2 : ℝ) _ _
  rw [hform]
  calc
    _ ≤ ‖(-1 / 2 : ℝ) • (∫ h in E ∩ ball 0 R, K h)‖ +
        ‖(-1 / 2 : ℝ) • (∫ h in closedExterior 0 R, K h)‖ := norm_add_le _ _
    _ ≤ _ := by
      simpa only [← add_div, N, C, fractionalSchwartzDecaySize] using! add_le_add hnear hfar

theorem fractionalSchwartzTruncatedTest_polynomial_decay (p : ℕ) (ε : ℝ) (hε : ε ≤ 1)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hmean : (∫ y, g y) = 0) (x : Ambient (p + 1)) :
    ‖fractionalSchwartzTruncatedTest p ε g x‖ ≤
      (3 ^ (p + 3) * (fractionalSchwartzUniformSize p g + fractionalSchwartzDecaySize p g)) *
        polynomialDecay (p + 3) x := by
  let U := fractionalSchwartzUniformSize p g
  let D := fractionalSchwartzDecaySize p g
  have hU : 0 ≤ U := by dsimp [U, fractionalSchwartzUniformSize] <;> positivity
  have hD : 0 ≤ D := fractionalSchwartzDecaySize_nonneg p g
  have hu : ‖fractionalSchwartzTruncatedTest p ε g x‖ ≤ U :=
    fractionalSchwartzTruncatedTest_uniform_bound p ε g x
  rw [polynomialDecay, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖x‖) (p + 3))).2
  by_cases hx : 2 ≤ ‖x‖
  · have hp : 0 < ‖x‖ := by linarith
    have hd := fractionalSchwartzTruncatedTest_spatial_decay p ε g hmean x hp (by linarith)
    have hb : (1 + ‖x‖) ^ (p + 3) ≤ (2 * ‖x‖) ^ (p + 3) :=
      pow_le_pow_left₀ (by positivity) (by linarith) (p + 3)
    calc
      _ ≤ (D / ‖x‖ ^ (p + 3)) * (2 * ‖x‖) ^ (p + 3) :=
        mul_le_mul hd hb (by positivity) (div_nonneg hD (by positivity))
      _ = 2 ^ (p + 3) * D := by rw [mul_pow]; field_simp
      _ ≤ 3 ^ (p + 3) * (U + D) :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
          (by norm_num : (2 : ℝ) ≤ 3) (p + 3)) (by linarith) hD (by positivity)
  · have hb : (1 + ‖x‖) ^ (p + 3) ≤ (3 : ℝ) ^ (p + 3) :=
      pow_le_pow_left₀ (by positivity) (by linarith) (p + 3)
    calc
      _ ≤ U * 3 ^ (p + 3) := mul_le_mul hu hb (by positivity) hU
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (by linarith : U ≤ U + D)
          (by positivity : 0 ≤ (3 : ℝ) ^ (p + 3))
        simpa only [mul_comm] using! hh

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalTruncatedHeightLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology

theorem height_fractional_truncated_integral_tendsto (p : ℕ)
    (μ : Measure (Ambient (p + 1))) (f : Ambient (p + 1) → ℝ) (hf : Measurable f)
    (hweight : Integrable (fun x => |f x| * polynomialDecay (p + 3) x) μ)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (g : 𝓢(Ambient (p + 1), ℂ)) (hg : (∫ y, g y) = 0) :
    Tendsto (fun j => ∫ x, f x • fractionalSchwartzTruncatedTest p (ε j) g x ∂μ)
      atTop (𝓝 (∫ x, f x • fractionalSchwartzTest p g x ∂μ)) := by
  let W := 3 ^ (p + 3) * (fractionalSchwartzUniformSize p g + fractionalSchwartzDecaySize p g)
  have hm (j : ℕ) : Measurable (fun x => f x • fractionalSchwartzTruncatedTest p (ε j) g x) := by
    simp_rw [RCLike.real_smul_eq_coe_mul]
    exact (Complex.continuous_ofReal.measurable.comp hf).mul
      (fractionalSchwartzTruncatedTest_measurable p (ε j) g)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => W * (|f x| * polynomialDecay (p + 3) x))
  · exact Eventually.of_forall fun j => (hm j).aestronglyMeasurable
  · filter_upwards [hε.eventually (gt_mem_nhds zero_lt_one)] with j hj
    exact Eventually.of_forall fun x => by
      rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal]
      calc
        _ ≤ |f x| * (W * polynomialDecay (p + 3) x) :=
          mul_le_mul_of_nonneg_left
            (fractionalSchwartzTruncatedTest_polynomial_decay p (ε j) hj.le g hg x) (abs_nonneg _)
        _ = _ := by ring
  · exact hweight.const_mul W
  · exact Eventually.of_forall fun x =>
      (fractionalSchwartzTruncatedTest_tendsto p ε hε g x).const_smul (f x)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_RenormalizedCrossCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter

theorem mean_zero_subtracted_kernel_test_integral {d : ℕ}
    (ν : Measure (Ambient d)) (g : Ambient d → ℂ) (hg : Integrable g ν)
    (hzero : (∫ x, g x ∂ν) = 0) (k : Ambient d → ℝ)
    (hk : Integrable (fun x => k x • g x) ν) (c : ℝ) :
    Integrable (fun x => (k x - c) • g x) ν ∧
      (∫ x, (k x - c) • g x ∂ν) = ∫ x, k x • g x ∂ν := by
  have hc : Integrable (fun x => c • g x) ν := hg.smul c
  have heq : (fun x => (k x - c) • g x) = fun x => k x • g x - c • g x := by
    funext x
    exact sub_smul (k x) c (g x)
  rw [heq]
  refine ⟨hk.sub hc, ?_⟩
  rw [integral_sub hk hc]
  have hz : (∫ x, c • g x ∂ν) = 0 := by
    calc
      _ = c • (∫ x, g x ∂ν) := integral_smul c g
      _ = 0 := by rw [hzero]; exact smul_zero c
  rw [hz, sub_zero]

theorem renormalized_complex_cross_integral_identity {d : ℕ} (m : ℕ)
    (ν η : Measure (Ambient d)) [SFinite ν] [SFinite η]
    (w : Ambient d → ℝ) (g : Ambient d → ℂ) (a : Ambient d)
    (hg : Integrable g ν) (hzero : (∫ x, g x ∂ν) = 0)
    (hraw : ∀ᵐ y ∂η, Integrable (fun x => inverseDistancePow (m + 1) x y • g x) ν)
    (hD : Integrable (fun q : Ambient d × Ambient d =>
      w q.1 • (inverseDistancePow (m + 1) q.1 q.2 • g q.1)) (ν.prod η))
    (hN : Integrable (complexRenormalizedNormalIntegrand m w g a) (ν.prod η)) :
    Integrable (fun y => w y • (∫ x, inverseDistancePow (m + 1) x y • g x ∂ν)) η ∧
      (∫ q, complexRenormalizedNormalIntegrand m w g a q ∂ν.prod η) =
        (∫ x, w x • (∫ y, inverseDistancePow (m + 1) x y • g x ∂η) ∂ν) -
          ∫ y, w y • (∫ x, inverseDistancePow (m + 1) x y • g x ∂ν) ∂η := by
  let D := fun q : Ambient d × Ambient d => w q.1 • (inverseDistancePow (m + 1) q.1 q.2 • g q.1)
  let F := fun q : Ambient d × Ambient d => w q.2 •
    ((inverseDistancePow (m + 1) q.1 q.2 - inverseDistancePow (m + 1) a q.2) • g q.1)
  have heq : complexRenormalizedNormalIntegrand m w g a = fun q => D q - F q := by
    funext q
    dsimp only [D, F, complexRenormalizedNormalIntegrand]
    simp only [Complex.real_smul]
    push_cast
    ring
  have hDF : Integrable (fun q => D q - F q) (ν.prod η) := by
    rwa [← heq]
  have hF : Integrable F (ν.prod η) := by
    have hh := hD.sub hDF
    change Integrable (fun q => D q - (D q - F q)) (ν.prod η) at hh
    simpa only [sub_sub_cancel] using! hh
  have hc : (fun y => ∫ x, F (x, y) ∂ν) =ᵐ[η]
      fun y => w y • (∫ x, inverseDistancePow (m + 1) x y • g x ∂ν) := by
    filter_upwards [hraw] with y hy
    have hz := (mean_zero_subtracted_kernel_test_integral ν g hg hzero
      (fun x => inverseDistancePow (m + 1) x y) hy (inverseDistancePow (m + 1) a y)).2
    calc
      _ = w y • (∫ x, (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y) • g x ∂ν) :=
        integral_smul (w y) _
      _ = _ := congrArg (fun z : ℂ => w y • z) hz
  have hFint : (∫ q, F q ∂ν.prod η) =
      ∫ y, w y • (∫ x, inverseDistancePow (m + 1) x y • g x ∂ν) ∂η :=
    (integral_prod_symm F hF).trans (integral_congr_ae hc)
  have hDint : (∫ q, D q ∂ν.prod η) =
      ∫ x, w x • (∫ y, inverseDistancePow (m + 1) x y • g x ∂η) ∂ν := by
    refine (integral_prod D hD).trans (integral_congr_ae (Eventually.of_forall ?_))
    intro x
    exact integral_smul (w x) _
  refine ⟨hF.integral_prod_right.congr hc, ?_⟩
  rw [heq, integral_sub hD hF, hFint, hDint]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SupportedKernelDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter

theorem supported_kernel_integral_decomposition {d : ℕ}
    (μ : Measure (Ambient d)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (g : Ambient d → ℂ) (hgs : ∀ y ∈ sᶜ, g y = 0)
    (k : Ambient d × Ambient d → ℝ) (x : Ambient d)
    (hi : Integrable (fun y => k (x, y) • (g x - g y)) μ) :
    (∫ y, k (x, y) • (g x - g y) ∂μ) =
      (∫ y in s, k (x, y) • (g x - g y) ∂μ) +
        ∫ y in sᶜ, k (x, y) • g x ∂μ := by
  rw [← integral_add_compl hs hi]
  congr 1
  apply setIntegral_congr_fun hs.compl
  intro y hy
  dsimp only
  rw [hgs y hy, sub_zero]

theorem supported_kernel_integral_outside {d : ℕ}
    (μ : Measure (Ambient d)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (g : Ambient d → ℂ) (hgs : ∀ y ∈ sᶜ, g y = 0)
    (k : Ambient d × Ambient d → ℝ) (x : Ambient d) (hx : x ∈ sᶜ)
    (hi : Integrable (fun y => k (x, y) • (g x - g y)) μ) :
    (∫ y, k (x, y) • (g x - g y) ∂μ) =
      -(∫ y in s, k (x, y) • g y ∂μ) := by
  rw [supported_kernel_integral_decomposition μ s hs g hgs k x hi, hgs x hx]
  simp only [Complex.real_smul, zero_sub, mul_neg, mul_zero, integral_zero, add_zero, integral_neg]

theorem supported_height_kernel_integral_decomposition {d : ℕ}
    (μ : Measure (Ambient d)) [SFinite μ]
    (s : Set (Ambient d)) (hs : MeasurableSet s)
    (w : Ambient d → ℝ) (g : Ambient d → ℂ) (hgs : ∀ y ∈ sᶜ, g y = 0)
    (k : Ambient d × Ambient d → ℝ)
    (hi : ∀ x, Integrable (fun y => k (x, y) • (g x - g y)) μ)
    (hL : Integrable (fun q : Ambient d × Ambient d =>
      w q.1 • (k q • (g q.1 - g q.2))) ((μ.restrict s).prod (μ.restrict s)))
    (hD : Integrable (fun q : Ambient d × Ambient d =>
      w q.1 • (k q • g q.1)) ((μ.restrict s).prod (μ.restrict sᶜ)))
    (hO : IntegrableOn (fun y => w y • (∫ x in s, k (y, x) • g x ∂μ)) sᶜ μ) :
    Integrable (fun x => w x • (∫ y, k (x, y) • (g x - g y) ∂μ)) μ ∧
      (∫ x, w x • (∫ y, k (x, y) • (g x - g y) ∂μ) ∂μ) =
        (∫ x in s, w x • (∫ y in s, k (x, y) • (g x - g y) ∂μ) ∂μ) +
        (∫ x in s, w x • (∫ y in sᶜ, k (x, y) • g x ∂μ) ∂μ) -
          ∫ y in sᶜ, w y • (∫ x in s, k (y, x) • g x ∂μ) ∂μ := by
  let T := fun x => w x • (∫ y, k (x, y) • (g x - g y) ∂μ)
  let L := fun x => w x • (∫ y in s, k (x, y) • (g x - g y) ∂μ)
  let D := fun x => w x • (∫ y in sᶜ, k (x, y) • g x ∂μ)
  let O := fun y => w y • (∫ x in s, k (y, x) • g x ∂μ)
  have hLI : IntegrableOn L s μ := by
    apply hL.integral_prod_left.congr
    exact Eventually.of_forall fun x => integral_smul (w x) _
  have hDI : IntegrableOn D s μ := by
    apply hD.integral_prod_left.congr
    exact Eventually.of_forall fun x => integral_smul (w x) _
  have hTin : T =ᵐ[μ.restrict s] fun x => L x + D x := by
    apply Eventually.of_forall
    intro x
    dsimp only [T, L, D]
    rw [supported_kernel_integral_decomposition μ s hs g hgs k x (hi x)]
    exact smul_add (w x) _ _
  have hTout : T =ᵐ[μ.restrict sᶜ] fun x => -(O x) := by
    filter_upwards [ae_restrict_mem hs.compl] with x hx
    dsimp only [T, O]
    rw [supported_kernel_integral_outside μ s hs g hgs k x hx (hi x)]
    exact smul_neg (w x) _
  have hTI : IntegrableOn T s μ := (hLI.add hDI).congr hTin.symm
  have hTE : IntegrableOn T sᶜ μ := hO.neg.congr hTout.symm
  have hT : Integrable T μ := by
    simpa only [union_compl_self, integrableOn_univ] using! hTI.union hTE
  refine ⟨hT, ?_⟩
  change (∫ x, T x ∂μ) = (∫ x in s, L x ∂μ) + (∫ x in s, D x ∂μ) - ∫ x in sᶜ, O x ∂μ
  rw [← integral_add_compl hs hT, integral_congr_ae hTin, integral_congr_ae hTout,
    integral_add hLI hDI, integral_neg, sub_eq_add_neg]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_SupportedFractionalCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fractional cutoffs for supported tests

Separation between the test support and the exterior region makes the cutoff
inactive in cross terms. The cutoff increment is also the closed-exterior
indicator of the full increment, giving its integrability and its equality
with the truncated fractional Schwartz test.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter SchwartzMap

theorem supported_fractional_cutoff_cross {d : ℕ} (m : ℕ) (ε H R : ℝ)
    (a x y : Ambient d) (g : Ambient d → ℂ)
    (hnear : g x ≠ 0 → dist x a ≤ H) (hfar : y ∈ closedExterior a R)
    (hsep : ε + H ≤ R) :
    symmetricFractionalCutoffKernel m ε (x, y) • g x =
      inverseDistancePow (m + 1) x y • g x := by
  by_cases hg : g x = 0
  · rw [hg]
    exact (smul_zero _).trans (smul_zero _).symm
  · have hy : R ≤ dist a y := hfar
    have ht := dist_triangle a x y
    rw [dist_comm a x] at ht
    have hd : ε ≤ dist x y := by linarith [hnear hg]
    simp only [symmetricFractionalCutoffKernel, ite_eq_left hd]

theorem supported_fractional_cutoff_cross_swap {d : ℕ} (m : ℕ) (ε H R : ℝ)
    (a x y : Ambient d) (g : Ambient d → ℂ)
    (hnear : g x ≠ 0 → dist x a ≤ H) (hfar : y ∈ closedExterior a R)
    (hsep : ε + H ≤ R) :
    symmetricFractionalCutoffKernel m ε (y, x) • g x =
      inverseDistancePow (m + 1) x y • g x := by
  rw [show symmetricFractionalCutoffKernel m ε (y, x) =
      symmetricFractionalCutoffKernel m ε (x, y) from
    symmetricFractionalCutoffKernel_swap m ε (x, y)]
  exact supported_fractional_cutoff_cross m ε H R a x y g hnear hfar hsep

theorem test_zero_outside_localization {d : ℕ} (g : Ambient d → ℂ)
    (a : Ambient d) (H R : ℝ) (hHR : H < R)
    (hnear : ∀ x, g x ≠ 0 → dist x a ≤ H) :
    ∀ y ∈ (ball a R)ᶜ, g y = 0 := by
  intro y hy
  by_contra hgy
  have hh := hnear y hgy
  have hf : R ≤ dist y a := by simpa only [mem_compl_iff, mem_ball, not_lt] using! hy
  linarith

theorem fractional_cutoff_increment_eq_indicator {d : ℕ} (m : ℕ) (ε : ℝ)
    (g : Ambient d → ℂ) (x : Ambient d) :
    (fun y => symmetricFractionalCutoffKernel m ε (x, y) • (g x - g y)) =
      (closedExterior x ε).indicator (fun y => inverseDistancePow (m + 1) x y • (g x - g y)) := by
  funext y
  by_cases h : ε ≤ dist x y
  · rw [indicator_of_mem (show y ∈ closedExterior x ε from h)]
    simp only [symmetricFractionalCutoffKernel, ite_eq_left h]
  · rw [indicator_of_notMem (show y ∉ closedExterior x ε from h)]
    simp only [symmetricFractionalCutoffKernel, ite_eq_right h]
    exact zero_smul ℝ (g x - g y)

theorem fractional_cutoff_increment_integrable (p : ℕ) (ε : ℝ) (hε : 0 < ε)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) :
    Integrable (fun y => symmetricFractionalCutoffKernel (p + 1) ε (x, y) • (g x - g y)) volume := by
  rw [fractional_cutoff_increment_eq_indicator]
  exact (integrable_indicator_iff (closedExterior_measurable x ε)).2
    (fractionalSchwartz_single_increment_integrable p ε hε g x)

theorem fractional_cutoff_increment_integral (p : ℕ) (ε : ℝ) (hε : 0 < ε)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) :
    (∫ y, symmetricFractionalCutoffKernel (p + 1) ε (x, y) • (g x - g y)) =
      fractionalSchwartzTruncatedTest p ε g x := by
  rw [fractional_cutoff_increment_eq_indicator, integral_indicator (closedExterior_measurable x ε)]
  exact (fractionalSchwartzTruncatedTest_eq_single_increment p ε hε g x).symm

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_TruncatedRenormalizedHeightIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Truncated height pairing and its renormalized exterior term

For a compactly supported mean-zero Schwartz test, the weighted truncated
fractional pairing splits into a symmetric local pairing and a renormalized
exterior integral. Support separation removes the cutoff in cross terms, and
the weighted exterior hypothesis supplies the integrability needed for cancellation.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter SchwartzMap

theorem compact_schwartz_truncated_height_pairing (p : ℕ)
    (a : Ambient (p + 1)) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (ε : ℝ) (hε : 0 < ε) (hsep : ε + H ≤ R)
    (w : Ambient (p + 1) → ℝ) (hwm : Measurable w)
    (hw : IntegrableOn w (ball a R) volume)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hzero : (∫ x, g x) = 0)
    (hnear : ∀ x, g x ≠ 0 → dist x a ≤ H)
    (B : ℝ) (hB : 0 ≤ B) (hgB : ∀ x, ‖g x‖ ≤ B)
    (hweighted : IntegrableOn (fun y => |w y| * inverseDistancePow (p + 1 + 2) a y)
      (closedExterior a R) volume) :
    Integrable (fun x => w x • fractionalSchwartzTruncatedTest p ε g x) volume ∧
      (∫ x, w x • fractionalSchwartzTruncatedTest p ε g x) =
        (1 / 2 : ℝ) • (∫ q : Ambient (p + 1) × Ambient (p + 1),
          (w q.1 - w q.2) • (symmetricFractionalCutoffKernel (p + 1) ε q • (g q.1 - g q.2))
          ∂(volume.restrict (ball a R)).prod (volume.restrict (ball a R))) +
        ∫ q, complexRenormalizedNormalIntegrand (p + 1) w g a q
          ∂(volume.restrict (ball a R)).prod (volume.restrict (ball a R)ᶜ) := by
  let μ : Measure (Ambient (p + 1)) := volume
  let ν := μ.restrict (ball a R)
  let η := μ.restrict (ball a R)ᶜ
  let C := (volume (ball (0 : Ambient (p + 1)) 1)).toReal
  let k := symmetricFractionalCutoffKernel (d := p + 1) (p + 1) ε
  have hgrowth : GlobalUpperGrowth (p + 1) C μ := volume_global_upper_growth (p + 1)
  let : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hgrowth a R hR
  have hgs := test_zero_outside_localization g a H R (by linarith) hnear
  have hgm : Measurable g := g.continuous.measurable
  have hgn : Integrable (fun x => ‖g x‖) ν := g.integrable.restrict.norm
  have hgnw : Integrable (fun x => ‖g x‖ * w x) ν :=
    hw.bdd_mul hgm.norm.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [norm_norm] using! hgB x)
  have hzν : (∫ x, g x ∂ν) = 0 := by
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hgs).trans hzero
  have hD : Integrable (fun q : Ambient (p + 1) × Ambient (p + 1) =>
      w q.1 • (inverseDistancePow (p + 1 + 1) q.1 q.2 • g q.1)) (ν.prod η) := by
    simpa only [closedExterior_eq_compl_ball] using! direct_height_exterior_integrable
      (p + 1) C μ ν hgrowth w g hwm hgm hgnw a H R hR hHR (Eventually.of_forall hnear)
  have hN : Integrable (complexRenormalizedNormalIntegrand (p + 1) w g a) (ν.prod η) := by
    simpa only [closedExterior_eq_compl_ball] using! complex_renormalized_exterior_integrable
      (p + 1) C μ ν hgrowth w g hwm hgm hgn hgnw a H R hH hR hHR
      (Eventually.of_forall hnear) hweighted
  have hraw : ∀ᵐ y ∂η, Integrable (fun x => inverseDistancePow (p + 1 + 1) x y • g x) ν := by
    filter_upwards [ae_restrict_mem (μ := μ)
      (show MeasurableSet (ball a R)ᶜ from measurableSet_ball.compl)] with y hy
    have hy' : R ≤ dist a y := by
      rwa [← closedExterior_eq_compl_ball] at hy
    exact far_kernel_test_integrable_of_support ν g hgm g.integrable.restrict
      (p + 1) a y H R hR hHR (Eventually.of_forall hnear) hy'
  have hcross := renormalized_complex_cross_integral_identity (p + 1) ν η w g a
    g.integrable.restrict hzν hraw hD hN
  have hcut (x y : Ambient (p + 1)) (hy : y ∈ (ball a R)ᶜ) :
      k (x, y) • g x = inverseDistancePow (p + 1 + 1) x y • g x :=
    supported_fractional_cutoff_cross (p + 1) ε H R a x y g (hnear x)
      (by rwa [closedExterior_eq_compl_ball]) hsep
  have hcutswap (x y : Ambient (p + 1)) (hy : y ∈ (ball a R)ᶜ) :
      k (y, x) • g x = inverseDistancePow (p + 1 + 1) x y • g x :=
    supported_fractional_cutoff_cross_swap (p + 1) ε H R a x y g (hnear x)
      (by rwa [closedExterior_eq_compl_ball]) hsep
  have hDcut : Integrable (fun q : Ambient (p + 1) × Ambient (p + 1) =>
      w q.1 • (k q • g q.1)) (ν.prod η) := by
    apply hD.congr
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (μ := μ) (show MeasurableSet (ball a R)ᶜ from measurableSet_ball.compl))] with q hq
    exact congrArg (fun z : ℂ => w q.1 • z) (hcut q.1 q.2 hq).symm
  have hOeq : (fun y => w y • (∫ x, k (y, x) • g x ∂ν)) =ᵐ[η]
      fun y => w y • (∫ x, inverseDistancePow (p + 1 + 1) x y • g x ∂ν) := by
    filter_upwards [ae_restrict_mem (μ := μ)
      (show MeasurableSet (ball a R)ᶜ from measurableSet_ball.compl)] with y hy
    apply congrArg (fun z : ℂ => w y • z)
    exact integral_congr_ae (Eventually.of_forall fun x => hcutswap x y hy)
  have hO := hcross.1.congr hOeq.symm
  have hL := bounded_kernel_height_integrable ν w hwm hw g hgm B hB hgB k
    (symmetricFractionalCutoffKernel_measurable (p + 1) ε) ((ε ^ (p + 1 + 1))⁻¹)
    (symmetricFractionalCutoffKernel_bound (p + 1) ε hε)
  have hdec := supported_height_kernel_integral_decomposition μ (ball a R) measurableSet_ball
    w g hgs k (fractional_cutoff_increment_integrable p ε hε g) hL hDcut hO
  have hpair := (finite_symmetric_height_kernel_pairing ν w hwm hw g hgm B hB hgB k
    (symmetricFractionalCutoffKernel_measurable (p + 1) ε) ((ε ^ (p + 1 + 1))⁻¹)
    (symmetricFractionalCutoffKernel_bound (p + 1) ε hε)
    (symmetricFractionalCutoffKernel_swap (p + 1) ε)).2
  have hDeq : (∫ x, w x • (∫ y, k (x, y) • g x ∂η) ∂ν) =
      ∫ x, w x • (∫ y, inverseDistancePow (p + 1 + 1) x y • g x ∂η) ∂ν := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    apply congrArg (fun z : ℂ => w x • z)
    apply setIntegral_congr_fun measurableSet_ball.compl
    intro y hy
    exact hcut x y hy
  have hAe : (fun x => w x • (∫ y, k (x, y) • (g x - g y) ∂μ)) =
      fun x => w x • fractionalSchwartzTruncatedTest p ε g x := by
    funext x
    exact congrArg (fun z : ℂ => w x • z) (fractional_cutoff_increment_integral p ε hε g x)
  rw [hAe] at hdec
  refine ⟨hdec.1, ?_⟩
  change (∫ x, w x • fractionalSchwartzTruncatedTest p ε g x ∂μ) =
    (1 / 2 : ℝ) • (∫ q, (w q.1 - w q.2) • (k q • (g q.1 - g q.2)) ∂ν.prod ν) +
      ∫ q, complexRenormalizedNormalIntegrand (p + 1) w g a q ∂ν.prod η
  rw [hdec.2, ← hpair, hDeq, integral_congr_ae hOeq, hcross.2]
  abel

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_RenormalizedFractionalHeightIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology SchwartzMap

theorem compact_schwartz_renormalized_height_identity (p : ℕ)
    (a : Ambient (p + 1)) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (w : Ambient (p + 1) → ℝ) (hwm : Measurable w)
    (hw : IntegrableOn w (ball a R) volume)
    (hweight : Integrable (fun x => |w x| * polynomialDecay (p + 3) x) volume)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hzero : (∫ x, g x) = 0)
    (hnear : ∀ x, g x ≠ 0 → dist x a ≤ H)
    (B : ℝ) (hB : 0 ≤ B) (hgB : ∀ x, ‖g x‖ ≤ B)
    (hweighted : IntegrableOn (fun y => |w y| * inverseDistancePow (p + 1 + 2) a y)
      (closedExterior a R) volume)
    (hinterior : Integrable (complexHeightInteriorIntegrand (p + 1) w g)
      ((volume.restrict (ball a R)).prod (volume.restrict (ball a R)))) :
    (∫ x, w x • fractionalSchwartzTest p g x) =
      complexHeightPairingOn (p + 1) volume a (ball a R) w g := by
  let ε := fun j : ℕ => (1 / 2 : ℝ) ^ j
  have hε : Tendsto ε atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hεpos (j : ℕ) : 0 < ε j := by dsimp [ε] <;> positivity
  let N := ∫ q, complexRenormalizedNormalIntegrand (p + 1) w g a q
    ∂(volume.restrict (ball a R)).prod (volume.restrict (ball a R)ᶜ)
  let I := fun j => ∫ q : Ambient (p + 1) × Ambient (p + 1),
    (w q.1 - w q.2) • (symmetricFractionalCutoffKernel (p + 1) (ε j) q • (g q.1 - g q.2))
      ∂(volume.restrict (ball a R)).prod (volume.restrict (ball a R))
  have hleft := height_fractional_truncated_integral_tendsto p volume w hwm hweight ε hε g hzero
  have hright : Tendsto (fun j => (1 / 2 : ℝ) • I j + N) atTop
      (𝓝 (complexHeightPairingOn (p + 1) volume a (ball a R) w g)) :=
    ((complex_height_interior_cutoff_integral_tendsto (p + 1)
      (volume.restrict (ball a R)) w g hinterior ε hε).const_smul (1 / 2 : ℝ)).add_const N
  have heq : (fun j => ∫ x, w x • fractionalSchwartzTruncatedTest p (ε j) g x) =ᶠ[atTop]
      fun j => (1 / 2 : ℝ) • I j + N := by
    have hp : 0 < R - H := by linarith
    filter_upwards [hε.eventually (gt_mem_nhds hp)] with j hj
    exact (compact_schwartz_truncated_height_pairing p a H R hH hR hHR (ε j)
      (hεpos j) (by linarith) w hwm hw g hzero hnear B hB hgB hweighted).2
  exact tendsto_nhds_unique (hleft.congr' heq) hright

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_HeightEnergyPairingIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Height-energy pairing for compactly supported Schwartz tests

Finite interior fractional energy and a weighted exterior height bound give
integrability of the fractional Schwartz pairing and identify it with the
renormalized complex height pairing on the ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric SchwartzMap

theorem compact_schwartz_height_energy_pairing_identity (p : ℕ)
    (a : Ambient (p + 1)) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (w : Ambient (p + 1) → ℝ) (hwm : Measurable w)
    (hw : IntegrableOn w (ball a R) volume)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hzero : (∫ x, g x) = 0)
    (hnear : ∀ x, g x ≠ 0 → dist x a ≤ H)
    (hweighted : IntegrableOn (fun y => |w y| * inverseDistancePow (p + 1 + 2) a y)
      (closedExterior a R) volume)
    (henergy : Integrable (fun q : Ambient (p + 1) × Ambient (p + 1) =>
      fractionalPairEnergy (p + 1) w q.1 q.2)
      ((volume.restrict (ball a R)).prod (volume.restrict (ball a R)))) :
    Integrable (fun x => w x • fractionalSchwartzTest p g x) volume ∧
      (∫ x, w x • fractionalSchwartzTest p g x) =
        complexHeightPairingOn (p + 1) volume a (ball a R) w g := by
  let C := (volume (ball (0 : Ambient (p + 1)) 1)).toReal
  let ν := (volume : Measure (Ambient (p + 1))).restrict (ball a R)
  have hgrowth : GlobalUpperGrowth (p + 1) C (volume : Measure (Ambient (p + 1))) :=
    volume_global_upper_growth (p + 1)
  let : IsFiniteMeasure ν :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C volume hgrowth a R hR
  have hI := complex_height_interior_integrable_of_energy p C ν
    (globalGrowth_restrict (p + 1) C volume hgrowth (ball a R)) w hwm hw g henergy
  have hweight : Integrable (fun x => |w x| * polynomialDecay (p + 3) x) volume :=
    polynomial_weight_integrable_from_height_tail (p + 3) volume w hwm a R hR hw hweighted
  refine ⟨(height_fractional_test_integrable_and_bound p volume w hwm hweight g hzero).1, ?_⟩
  exact compact_schwartz_renormalized_height_identity p a H R hH hR hHR w hwm hw
    hweight g hzero hnear (SchwartzMap.seminorm ℝ 0 0 g)
    (apply_nonneg (SchwartzMap.seminorm ℝ 0 0) g) (g.norm_le_seminorm ℝ) hweighted hI

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalEquationFromRealPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fractional equations from real height pairings

Vanishing real pairings for compactly supported mean-zero tests give the complex fractional
equation by separating real and imaginary parts. Weighted tail integrability then extends the
equation to all mean-zero Schwartz tests.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter SchwartzMap

theorem compact_fractional_equation_of_real_pairing (p : ℕ)
    (a : Ambient (p + 1)) (w : Ambient (p + 1) → ℝ) (hwm : Measurable w)
    (hw : ∀ R : ℝ, 0 < R → IntegrableOn w (ball a R) volume)
    (htail : ∀ R : ℝ, 0 < R → IntegrableOn
      (fun y => |w y| * inverseDistancePow (p + 1 + 2) a y) (closedExterior a R) volume)
    (henergy : ∀ R : ℝ, 0 < R → Integrable
      (fun q : Ambient (p + 1) × Ambient (p + 1) => fractionalPairEnergy (p + 1) w q.1 q.2)
      ((volume.restrict (ball a R)).prod (volume.restrict (ball a R))))
    (hreal : ∀ φ : 𝓢(Ambient (p + 1), ℝ), HasCompactSupport φ → (∫ x, φ x) = 0 →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        heightPairingOn (p + 1) volume a (ball a R) w φ = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hc : HasCompactSupport g) (hg : (∫ x, g x) = 0) :
    (∫ x, w x • fractionalSchwartzTest p g x) = 0 := by
  let gr : 𝓢(Ambient (p + 1), ℝ) := g.postcompCLM Complex.reCLM
  let gi : 𝓢(Ambient (p + 1), ℝ) := g.postcompCLM Complex.imCLM
  have hcr : HasCompactSupport gr := hc.comp_left (g := Complex.re) rfl
  have hci : HasCompactSupport gi := hc.comp_left (g := Complex.im) rfl
  have hmr : (∫ x, gr x) = 0 := by
    calc
      _ = (∫ x, g x).re := integral_re g.integrable
      _ = 0 := by rw [hg]; rfl
  have hmi : (∫ x, gi x) = 0 := by
    calc
      _ = (∫ x, g x).im := integral_im g.integrable
      _ = 0 := by rw [hg]; rfl
  obtain ⟨Rr, hRr, hr⟩ := hreal gr hcr hmr
  obtain ⟨Ri, hRi, hi⟩ := hreal gi hci hmi
  obtain ⟨H, hH, hball⟩ := hc.isBounded.subset_closedBall_lt 0 a
  have hnear : ∀ x, g x ≠ 0 → dist x a ≤ H := by
    intro x hx
    exact hball (subset_tsupport g hx)
  let R := 2 * H + Rr + Ri + 1
  have hR : 0 < R := by dsimp [R] <;> linarith
  have hHR : 2 * H ≤ R := by dsimp [R] <;> linarith
  let ν := (volume : Measure (Ambient (p + 1))).restrict (ball a R)
  let C := (volume (ball (0 : Ambient (p + 1)) 1)).toReal
  have hvol : GlobalUpperGrowth (p + 1) C (volume : Measure (Ambient (p + 1))) :=
    volume_global_upper_growth (p + 1)
  let : IsFiniteMeasure ν :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C volume hvol a R hR
  have hI := complex_height_interior_integrable_of_energy p C ν
    (globalGrowth_restrict (p + 1) C volume hvol (ball a R)) w hwm (hw R hR) g (henergy R hR)
  have hgnw : Integrable (fun x => ‖g x‖ * w x) ν :=
    (hw R hR).bdd_mul g.continuous.measurable.norm.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [norm_norm] using! g.norm_le_seminorm ℝ x)
  have hN : Integrable (complexRenormalizedNormalIntegrand (p + 1) w g a)
      (ν.prod (volume.restrict (ball a R)ᶜ)) := by
    simpa only [closedExterior_eq_compl_ball] using! complex_renormalized_exterior_integrable
      (p + 1) C volume ν hvol w g hwm g.continuous.measurable g.integrable.restrict.norm
      hgnw a H R hH.le hR hHR (Eventually.of_forall hnear) (htail R hR)
  have hz := complex_height_pairing_zero_of_real_equations (p + 1) volume a (ball a R)
    w g hI hN (hr R (by dsimp [R] <;> linarith)) (hi R (by dsimp [R] <;> linarith))
  exact (compact_schwartz_height_energy_pairing_identity p a H R hH.le hR hHR
    w hwm (hw R hR) g hg hnear (htail R hR) (henergy R hR)).2.trans hz

theorem schwartz_fractional_equation_of_real_pairing_oai (p : ℕ)
    (a : Ambient (p + 1)) (w : Ambient (p + 1) → ℝ) (hwm : Measurable w)
    (hw : ∀ R : ℝ, 0 < R → IntegrableOn w (ball a R) volume)
    (htail : ∀ R : ℝ, 0 < R → IntegrableOn
      (fun y => |w y| * inverseDistancePow (p + 1 + 2) a y) (closedExterior a R) volume)
    (henergy : ∀ R : ℝ, 0 < R → Integrable
      (fun q : Ambient (p + 1) × Ambient (p + 1) => fractionalPairEnergy (p + 1) w q.1 q.2)
      ((volume.restrict (ball a R)).prod (volume.restrict (ball a R))))
    (hreal : ∀ φ : 𝓢(Ambient (p + 1), ℝ), HasCompactSupport φ → (∫ x, φ x) = 0 →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        heightPairingOn (p + 1) volume a (ball a R) w φ = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hg : (∫ x, g x) = 0) :
    (∫ x, w x • fractionalSchwartzTest p g x) = 0 := by
  have hweight : Integrable (fun x => |w x| * polynomialDecay (p + 3) x) volume :=
    polynomial_weight_integrable_from_height_tail (p + 3) volume w hwm a 1 zero_lt_one
      (hw 1 zero_lt_one) (htail 1 zero_lt_one)
  exact height_fractional_test_zero_on_mean_zero_tests p volume w hwm hweight
    (compact_fractional_equation_of_real_pairing p a w hwm hw htail henergy hreal) g hg

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.schwartz_fractional_equation_of_real_pairing_oai := @OAI.RieszRectifiability.schwartz_fractional_equation_of_real_pairing_oai
