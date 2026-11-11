-- Prove2me | solution 1 for OAI.RieszRectifiability.exists_source_planar_unweighted_capped_equation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:24:50.622233+00:00
-- url     : https://prove2.me/submissions/0177ef73-1a6c-4c2c-974f-b9ccf79930ec

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000
import Definitions.Def_OAIQ231Rr001

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_KernelBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Elementary measurability and inverse-distance bounds for the Euclidean Riesz kernel.
Global upper growth records the ball-mass estimate used in kernel integration.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem kernel_measurable_right {d : ℕ} (n : ℕ) (x : Ambient d) :
    Measurable (kernel n x) := by
  have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
  have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
  unfold kernel
  fun_prop

theorem kernel_norm_of_ne {d : ℕ} (n : ℕ) (x y : Ambient d) (hxy : x ≠ y) :
    ‖kernel n x y‖ = (dist x y ^ n)⁻¹ := by
  have hnorm : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hnonneg : 0 ≤ (‖x - y‖ ^ (n + 1))⁻¹ := by positivity
  rw [kernel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg, dist_eq_norm, pow_succ]
  field_simp

theorem kernel_norm_le_truncation {d : ℕ} (n : ℕ) (x y : Ambient d)
    (ε : ℝ) (hε : 0 < ε) (hy : ε ≤ dist x y) :
    ‖kernel n x y‖ ≤ (ε ^ n)⁻¹ := by
  have hd : 0 < dist x y := lt_of_lt_of_le hε hy
  rw [kernel_norm_of_ne n x y (dist_pos.mp hd)]
  simpa only [one_div] using!
    one_div_le_one_div_of_le (pow_pos hε n) (pow_le_pow_left₀ hε.le hy n)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_WeakCellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter Topology

variable {X : Type*} [MeasurableSpace X] [MetricSpace X]
  [OpensMeasurableSpace X] [Nonempty X]

theorem finiteMeasure_cell_mass_tendsto (μ : ℕ → FiniteMeasure X) (ν : FiniteMeasure X)
    (hweak : Tendsto μ atTop (𝓝 ν)) (hν : ν ≠ 0)
    (s : Set X) (hboundary : (ν : Measure X) (frontier s) = 0) :
    Tendsto (fun j => (μ j : Measure X).real s) atTop (𝓝 ((ν : Measure X).real s)) := by
  have hn : Tendsto (fun j => (μ j).normalize) atTop (𝓝 ν.normalize) :=
    FiniteMeasure.tendsto_normalize_of_tendsto hweak hν
  have hb : ν.normalize (frontier s) = 0 := by
    rw [ν.normalize_eq_of_nonzero hν]
    rw [(ν.null_iff_toMeasure_null _).mpr hboundary, mul_zero]
  have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn hb
  have hmass : Tendsto (fun j => (μ j) s) atTop (𝓝 (ν s)) := by
    simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using! hweak.mass.mul hp
  exact NNReal.continuous_coe.continuousAt.tendsto.comp hmass

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_OpenPlaneBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Open projection boxes and coordinate-plane measures

Pulling back open boxes along continuous coordinates gives open subsets of the
ambient space. Coordinate-plane measures satisfy upper growth bounds, which
in turn imply finiteness on compact sets.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem GlobalUpperGrowth.finite_on_compacts {d n : ℕ} {C : ℝ}
    {μ : Measure (Ambient d)} (h : GlobalUpperGrowth n C μ) : IsFiniteMeasureOnCompacts μ := by
  let : IsLocallyFiniteMeasure μ := ⟨fun x => ⟨ball x 1, ball_mem_nhds x (by norm_num),
    (h.2 x 1 (by norm_num)).trans_lt ENNReal.ofReal_lt_top⟩⟩
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_EnergyIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory

theorem centered_coordinate_difference (u v c : ℝ) :
    (u - c) - (v - c) = u - v := by
  ring

theorem normal_coordinate_difference {d : ℕ} (e z x y : Ambient d) :
    inner ℝ e (x - z) - inner ℝ e (y - z) = inner ℝ e (x - y) := by
  simp only [inner_sub_right]
  ring

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

theorem lipschitz_height_bound_on_ball {d : ℕ} (w : Ambient d → ℝ)
    (K : ℝ≥0) (hw : LipschitzWith K w) (a x : Ambient d) (R : ℝ) (hx : x ∈ ball a R) :
    |w x| ≤ |w a| + (K : ℝ) * R := by
  have hdiff : |w x - w a| ≤ (K : ℝ) * dist x a := by
    simpa only [Real.dist_eq] using! hw.dist_le_mul x a
  have habs : |w x| ≤ |w x - w a| + |w a| := by
    simpa only [sub_zero] using! abs_sub_le (w x) (w a) 0
  have hprod := mul_le_mul_of_nonneg_left hx.le K.coe_nonneg
  linarith

theorem lipschitz_height_memLp_on_ball {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    MemLp w 2 (μ.restrict (ball a R)) := by
  have := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  apply MemLp.of_bound hw.continuous.measurable.aestronglyMeasurable (|w a| + (K : ℝ) * R)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  simpa only [Real.norm_eq_abs] using! lipschitz_height_bound_on_ball w K hw a x R hx

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SymmetricKernelL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Function Set

variable {X : Type*} [MeasurableSpace X]

theorem row_weighted_square_integrable_and_bound
    (μ : Measure X) [IsFiniteMeasure μ] (k : X × X → ℝ)
    (hk : Measurable k) (hk0 : ∀ q, 0 ≤ k q)
    (hrow : ∀ x, Integrable (fun y => k (x, y)) μ)
    (B : ℝ) (hB : ∀ x, (∫ y, k (x, y) ∂μ) ≤ B)
    (w : X → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ) :
    Integrable (fun q : X × X => w q.1 ^ 2 * k q) (μ.prod μ) ∧
      (∫ q : X × X, w q.1 ^ 2 * k q ∂μ.prod μ) ≤ B * (∫ x, w x ^ 2 ∂μ) := by
  have hm : AEStronglyMeasurable (fun q : X × X => w q.1 ^ 2 * k q) (μ.prod μ) := by
    fun_prop
  have hi : Integrable (fun q : X × X => w q.1 ^ 2 * k q) (μ.prod μ) := by
    apply (integrable_prod_iff hm).mpr
    refine ⟨Filter.Eventually.of_forall (fun x => (hrow x).const_mul (w x ^ 2)), ?_⟩
    apply (hL2.integrable_sq.const_mul B).mono' hm.norm.integral_prod_right'
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simp_rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hk0 _)), integral_const_mul]
    simpa only [mul_comm B] using! mul_le_mul_of_nonneg_left (hB x) (sq_nonneg (w x))
  refine ⟨hi, ?_⟩
  have houter := hi.integral_prod_left
  simp only [integral_const_mul] at houter
  rw [integral_prod _ hi]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∫ x, B * w x ^ 2 ∂μ :=
      integral_mono houter (hL2.integrable_sq.const_mul B) (fun x => by
        simpa only [mul_comm B] using! mul_le_mul_of_nonneg_left (hB x) (sq_nonneg (w x)))
    _ = _ := integral_const_mul _ _

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FarHeightTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem lipschitz_height_radial_bound {d : ℕ} (w : Ambient d → ℝ)
    (K : ℝ≥0) (hw : LipschitzWith K w) (a y : Ambient d) (R : ℝ)
    (hR : 0 < R) (hy : R ≤ dist a y) :
    |w y| ≤ ((K : ℝ) + |w a| / R) * dist a y := by
  have hdiff : |w y - w a| ≤ (K : ℝ) * dist a y := by
    simpa only [Real.dist_eq, dist_comm y a] using! hw.dist_le_mul y a
  have hconstant : |w a| ≤ (|w a| / R) * dist a y := by
    have h := mul_le_mul_of_nonneg_left hy (div_nonneg (abs_nonneg (w a)) hR.le)
    simpa only [div_mul_cancel₀ _ hR.ne'] using! h
  calc
    _ ≤ |w y - w a| + |w a| := by
      simpa only [sub_add_cancel] using! abs_add_le (w y - w a) (w a)
    _ ≤ (K : ℝ) * dist a y + (|w a| / R) * dist a y := add_le_add hdiff hconstant
    _ = _ := by ring

theorem cancelled_height_far_bound {d : ℕ} (m : ℕ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a x y : Ambient d) (R : ℝ) (hR : 0 < R)
    (hx : 2 * dist x a ≤ R) (hy : R ≤ dist a y) :
    |w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y)| ≤
      (((K : ℝ) + |w a| / R) * (m + 1 : ℝ) * 2 ^ (m + 2) * dist x a) *
        inverseDistancePow (m + 1) a y := by
  have hpos : 0 < dist a y := lt_of_lt_of_le hR hy
  have hdiff := inverseDistancePow_far_difference m a x y hpos (hx.trans hy)
  rw [abs_mul]
  calc
    _ ≤ (((K : ℝ) + |w a| / R) * dist a y) *
        ((m + 1 : ℝ) * 2 ^ (m + 2) * dist x a * inverseDistancePow (m + 2) a y) :=
      mul_le_mul (lipschitz_height_radial_bound w K hw a y R hR hy) hdiff (abs_nonneg _)
        (by positivity)
    _ = _ := by
      unfold inverseDistancePow
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
      field_simp
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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_HeightTailSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Annular integrability for height-tail estimates

Lipschitz height functions are bounded on each dyadic annulus. The finite
annular mass supplied by upper growth then gives the square integrability
needed to apply shell estimates in the height-tail decomposition.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem weighted_height_closed_tail_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ ∧
      (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        ((K : ℝ) + |w a| / R) * (2 * (C * 2 ^ m / R)) := by
  obtain ⟨hweight, hbound⟩ := inverseDistancePow_closedExterior_integrable_and_bound m C μ hg a R hR
  have hm : Measurable (fun y => |w y| * inverseDistancePow (m + 2) a y) :=
    hw.continuous.measurable.abs.mul (inverseDistancePow_measurable _ _)
  have hpoint (y : Ambient d) (hy : y ∈ closedExterior a R) :
      |w y| * inverseDistancePow (m + 2) a y ≤
        ((K : ℝ) + |w a| / R) * inverseDistancePow (m + 1) a y := by
    have hpos : 0 < dist a y := lt_of_lt_of_le hR hy
    calc
      _ ≤ (((K : ℝ) + |w a| / R) * dist a y) * inverseDistancePow (m + 2) a y :=
        mul_le_mul_of_nonneg_right (lipschitz_height_radial_bound w K hw a y R hR hy)
          (inverseDistancePow_nonneg _ _ _)
      _ = _ := by
        unfold inverseDistancePow
        rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
        field_simp
  have hi : IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ := by
    apply (hweight.const_mul ((K : ℝ) + |w a| / R)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (inverseDistancePow_nonneg _ _ _))]
    exact hpoint y hy
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y in closedExterior a R,
        ((K : ℝ) + |w a| / R) * inverseDistancePow (m + 1) a y ∂μ := by
      apply integral_mono_ae hi (hweight.const_mul _)
      filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
      exact hpoint y hy
    _ = ((K : ℝ) + |w a| / R) * (∫ y in closedExterior a R, inverseDistancePow (m + 1) a y ∂μ) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RieszPairingIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar Riesz pairings and affine normal heights

Pairing the Riesz kernel with a fixed normal identifies its interior contribution
with the fractional bilinear form. For mean-zero tests, the exterior correction
integrates to zero, identifying the scalar Riesz pairing with the normal cutoff pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem affineNormalHeight_difference {d : ℕ} (e z : Ambient d) (b : ℝ) (x y : Ambient d) :
    affineNormalHeight e z b x - affineNormalHeight e z b y = inner ℝ e (x - y) := by
  rw [affineNormalHeight, affineNormalHeight, centered_coordinate_difference]
  exact normal_coordinate_difference e z x y

theorem affineNormalHeight_lipschitz {d : ℕ} (e z : Ambient d) (b : ℝ) :
    LipschitzWith ‖e‖₊ (affineNormalHeight e z b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, affineNormalHeight_difference]
  simpa only [Real.norm_eq_abs, coe_nnnorm, dist_eq_norm] using!
    norm_inner_le_norm (𝕜 := ℝ) e (x - y)

theorem kernel_inner_normal_difference {d : ℕ} (m : ℕ) (e : Ambient d)
    (w : Ambient d → ℝ) (hw : ∀ x y, w x - w y = inner ℝ e (x - y)) (x y : Ambient d) :
    inner ℝ e (kernel m x y) = (w x - w y) * inverseDistancePow (m + 1) x y := by
  rw [kernel, real_inner_smul_right, ← hw x y, ← dist_eq_norm]
  unfold inverseDistancePow
  ring

theorem rieszInteriorIntegrand_eq_fractionalBilinear {d : ℕ} (m : ℕ) (e : Ambient d)
    (w φ : Ambient d → ℝ) (hw : ∀ x y, w x - w y = inner ℝ e (x - y))
    (q : Ambient d × Ambient d) :
    rieszInteriorIntegrand m e φ q = fractionalBilinear m w φ q.1 q.2 := by
  rw [rieszInteriorIntegrand, kernel_inner_normal_difference m e w hw]
  unfold inverseDistancePow fractionalBilinear
  ring

theorem rieszFarIntegrand_eq_normal_sub_correction {d : ℕ} (m : ℕ) (e : Ambient d)
    (w φ : Ambient d → ℝ) (hw : ∀ x y, w x - w y = inner ℝ e (x - y))
    (a : Ambient d) (q : Ambient d × Ambient d) :
    rieszFarIntegrand m e φ a q = renormalizedNormalIntegrand m w φ a q -
      (φ q.1 * w a) * inverseDistancePow (m + 1) a q.2 := by
  rw [rieszFarIntegrand, inner_sub_right, kernel_inner_normal_difference m e w hw,
    kernel_inner_normal_difference m e w hw]
  unfold renormalizedNormalIntegrand
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_TruncationIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrability of hard Riesz truncations

Global upper growth makes the Riesz kernel square-integrable outside each positive-radius
ball. Pairing this exterior estimate with an L² input proves integrability of the hard
truncation. For finite measures, integrability instead follows from the bounded exterior
kernel and the inclusion of L² in L¹.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem kernel_sq_norm_le_tail_weight {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (x y : Ambient d) (ε : ℝ) (hε : 0 < ε) (hy : ε ≤ dist x y) :
    ‖kernel n x y‖ ^ 2 ≤ (ε ^ (n - 1))⁻¹ * inverseDistancePow (n + 1) x y := by
  have hd : 0 < dist x y := lt_of_lt_of_le hε hy
  rw [kernel_norm_of_ne n x y (dist_pos.mp hd), inv_pow, ← pow_mul,
    show n * 2 = (n - 1) + (n + 1) by omega, pow_add, mul_inv]
  apply mul_le_mul_of_nonneg_right
  · simpa only [one_div] using! one_div_le_one_div_of_le
      (pow_pos hε (n - 1)) (pow_le_pow_left₀ hε.le hy (n - 1))
  · positivity

theorem kernel_memLp_two_on_exterior {d : ℕ} (n : ℕ) (hn : 1 ≤ n) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) :
    MemLp (kernel n x) 2 (μ.restrict {y | ε < dist x y}) := by
  have hmeas : AEStronglyMeasurable (kernel n x) (μ.restrict {y | ε < dist x y}) :=
    (kernel_measurable_right n x).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have hi := (inverseDistancePow_integrableOn_exterior n C μ hg x ε hε).const_mul
    ((ε ^ (n - 1))⁻¹)
  apply hi.mono' ((kernel_measurable_right n x).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem
    (measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable)] with y hy
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact kernel_sq_norm_le_tail_weight n hn x y ε hε hy.le

theorem truncation_integrable_of_globalGrowth {d : ℕ} (n : ℕ) (hn : 1 ≤ n) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun y => f y • kernel n x y) {y | ε < dist x y} μ := by
  apply memLp_one_iff_integrable.mp
  exact MemLp.smul (hf := kernel_memLp_two_on_exterior n hn C μ hg x ε hε) (hφ := hf.restrict _)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FiniteRieszPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-measure truncated Riesz pairings

The scalar truncated kernel is measurable and bounded away from its singularity.
Symmetrization expresses finite-measure pairings as interior double integrals,
whose integrability yields convergence as the truncation scale tends to zero.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem scalarTruncatedKernel_measurable {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ) :
    Measurable (scalarTruncatedKernel m e ε) := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  unfold scalarTruncatedKernel kernel
  apply Measurable.ite (measurableSet_lt measurable_const (continuous_fst.dist continuous_snd).measurable)
  · fun_prop
  · exact measurable_const

theorem scalarTruncatedKernel_bound {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ)
    (hε : 0 < ε) (q : Ambient d × Ambient d) :
    |scalarTruncatedKernel m e ε q| ≤ ‖e‖ * (ε ^ m)⁻¹ := by
  unfold scalarTruncatedKernel
  split_ifs with h
  · have hi : |inner ℝ e (kernel m q.1 q.2)| ≤ ‖e‖ * ‖kernel m q.1 q.2‖ := by
      simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) e (kernel m q.1 q.2)
    apply hi.trans
    exact mul_le_mul_of_nonneg_left (kernel_norm_le_truncation m q.1 q.2 ε hε h.le) (norm_nonneg e)
  · simp only [abs_zero]
    positivity

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

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactRieszPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compactly supported Lipschitz Riesz pairings

Growth bounds control the exterior pairing of a compactly supported Lipschitz test.
Finite ball restrictions then connect truncated pairings to the renormalized
pairing through the outer-radius limit.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem rieszFarIntegrand_integrable_of_compact_lipschitz {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    Integrable (rieszFarIntegrand m e φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))) := by
  let ν := μ.restrict (ball a R)
  let w := affineNormalHeight e a 0
  have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  have hw : LipschitzWith ‖e‖₊ w := affineNormalHeight_lipschitz e a 0
  have hwL2 := lipschitz_height_memLp_on_ball m C μ hg w ‖e‖₊ hw a R hR
  have hφL2 := lipschitz_height_memLp_on_ball m C μ hg φ L hφ a R hR
  have hφI := hφL2.integrable (by norm_num)
  have hφw : Integrable (fun x => φ x * w x) ν := memLp_one_iff_integrable.mp (MeasureTheory.MemLp.mul (hφ := hφL2) (hf := hwL2))
  obtain ⟨hweighted, hZ⟩ := weighted_height_closed_tail_bound m C μ hg w ‖e‖₊ hw a R hR
  have hN := (renormalized_far_pairing_integrable_and_bound m C μ ν hg w φ
    hw.continuous.measurable hφ.continuous.measurable hφI hφw a H R hH hR hHR
    (Filter.Eventually.of_forall hsupport) hweighted _ hZ).1
  have hwa : w a = 0 := by simp only [w, affineNormalHeight, sub_self, inner_zero_right]
  have heq : rieszFarIntegrand m e φ a = renormalizedNormalIntegrand m w φ a := by
    funext q
    rw [rieszFarIntegrand_eq_normal_sub_correction m e w φ (affineNormalHeight_difference e a 0),
      hwa, mul_zero, zero_mul, sub_zero]
  rw [heq]
  exact hN

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LocalizedRieszPairingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localized scalar Riesz pairing bounds

Lipschitz cancellation bounds the interior integrand by a weakly singular kernel.
The exterior estimate uses compact support and the normal height to control its
tail, giving quantitative bounds for the localized scalar pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem rieszInteriorIntegrand_weak_kernel_bound {d : ℕ} (p : ℕ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (x y : Ambient d) :
    |rieszInteriorIntegrand (p + 1) e φ (x, y)| ≤
      (‖e‖ * (L : ℝ)) * inverseDistancePow p x y := by
  by_cases hxy : x = y
  · subst y
    simp only [rieszInteriorIntegrand, sub_self, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) L.coe_nonneg)
      (inverseDistancePow_nonneg _ _ _)
  have hd : dist x y ≠ 0 := (dist_pos.mpr hxy).ne'
  have he : |inner ℝ e (kernel (p + 1) x y)| ≤
      ‖e‖ * (dist x y ^ (p + 1))⁻¹ := by
    simpa only [Real.norm_eq_abs, kernel_norm_of_ne _ _ _ hxy] using!
      norm_inner_le_norm (𝕜 := ℝ) e (kernel (p + 1) x y)
  have hl : |φ x - φ y| ≤ (L : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using! hφ.dist_le_mul x y
  calc
    _ = |inner ℝ e (kernel (p + 1) x y)| * |φ x - φ y| := by
      rw [rieszInteriorIntegrand, abs_mul]
    _ ≤ (‖e‖ * (dist x y ^ (p + 1))⁻¹) * ((L : ℝ) * dist x y) :=
      mul_le_mul he hl (abs_nonneg _) (by positivity)
    _ = _ := by
      unfold inverseDistancePow
      rw [pow_succ]
      field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedRieszInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem cappedRieszInterior_continuous {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (e : Ambient d) (φ : Ambient d → ℝ) (hφ : Continuous φ) :
    Continuous (cappedRieszInterior m ε e φ) := by
  have hc := (cappedInverseDistancePow_lipschitz (X := Ambient d) m ε hε).continuous
  unfold cappedRieszInterior
  fun_prop

theorem distance_mul_cappedInverseDistancePow_bound {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) (q : X × X) :
    dist q.1 q.2 * cappedInverseDistancePow (m + 1) ε q ≤ (ε ^ m)⁻¹ := by
  have hmax : 0 < max ε (dist q.1 q.2) := hε.trans_le (le_max_left _ _)
  calc
    _ ≤ max ε (dist q.1 q.2) * cappedInverseDistancePow (m + 1) ε q :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (cappedInverseDistancePow_nonneg _ _ _)
    _ = ((max ε (dist q.1 q.2)) ^ m)⁻¹ := by
      unfold cappedInverseDistancePow
      rw [pow_succ]
      field_simp
    _ ≤ _ := inv_anti₀ (pow_pos hε m) (pow_le_pow_left₀ hε.le (le_max_left _ _) m)

theorem cappedRieszInterior_bound {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (e : Ambient d) (φ : Ambient d → ℝ) (B : ℝ≥0)
    (hB : ∀ x, |φ x| ≤ (B : ℝ)) (q : Ambient d × Ambient d) :
    |cappedRieszInterior m ε e φ q| ≤ (2 * (B : ℝ) * ‖e‖) * (ε ^ m)⁻¹ := by
  have hi : |inner ℝ e (q.1 - q.2)| ≤ ‖e‖ * dist q.1 q.2 := by
    simpa only [Real.norm_eq_abs, dist_eq_norm] using!
      norm_inner_le_norm (𝕜 := ℝ) e (q.1 - q.2)
  have hd : |φ q.1 - φ q.2| ≤ 2 * (B : ℝ) := by
    have ht := abs_sub_le (φ q.1) 0 (φ q.2)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    linarith [hB q.1, hB q.2]
  calc
    _ = |inner ℝ e (q.1 - q.2)| * |φ q.1 - φ q.2| *
        cappedInverseDistancePow (m + 1) ε q := by
      rw [cappedRieszInterior, abs_mul, abs_mul,
        abs_of_nonneg (cappedInverseDistancePow_nonneg _ _ _)]
    _ ≤ (‖e‖ * dist q.1 q.2) * (2 * (B : ℝ)) *
        cappedInverseDistancePow (m + 1) ε q :=
      mul_le_mul_of_nonneg_right (mul_le_mul hi hd (abs_nonneg _) (by positivity))
        (cappedInverseDistancePow_nonneg _ _ _)
    _ = (2 * (B : ℝ) * ‖e‖) *
        (dist q.1 q.2 * cappedInverseDistancePow (m + 1) ε q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (distance_mul_cappedInverseDistancePow_bound m ε hε q) (by positivity)

theorem cappedRieszInterior_eq_affine_bilinear {d : ℕ} (m : ℕ) (ε : ℝ)
    (e : Ambient d) (φ : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    cappedRieszInterior m ε e φ q =
      (affineNormalHeight e 0 0 q.1 - affineNormalHeight e 0 0 q.2) *
        cappedTestKernel m ε φ q := by
  rw [affineNormalHeight_difference]
  unfold cappedRieszInterior cappedTestKernel
  ring

theorem rieszInterior_cap_error_pointwise {d : ℕ} (p : ℕ) (ε : ℝ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (q : Ambient d × Ambient d) :
    |rieszInteriorIntegrand (p + 1) e φ q - cappedRieszInterior (p + 1) ε e φ q| ≤
      (‖e‖ * (L : ℝ)) * nearPairWeight p ε q := by
  have hb := capped_bilinear_error_pointwise (p + 1) ε (affineNormalHeight e 0 0) φ q
  rw [← cappedRieszInterior_eq_affine_bilinear] at hb
  have heq := rieszInteriorIntegrand_eq_fractionalBilinear (p + 1) e
    (affineNormalHeight e 0 0) φ (affineNormalHeight_difference e 0 0)
  simp only [← heq] at hb
  apply hb.trans
  by_cases hq : q ∈ nearPairSet ε
  · rw [indicator_of_mem hq, nearPairWeight, indicator_of_mem hq]
    exact rieszInteriorIntegrand_weak_kernel_bound p e φ L hφ q.1 q.2
  · rw [indicator_of_notMem hq, nearPairWeight, indicator_of_notMem hq, mul_zero]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedRieszKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Capped Riesz kernels

Capping the radial singularity gives a continuous bounded vector kernel agreeing
with the Riesz kernel away from the cap. The scalar difference from hard truncation
is controlled by a symmetric weight supported on close pairs.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem cappedRieszKernel_norm_bound {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (q : Ambient d × Ambient d) : ‖cappedRieszKernel m ε q‖ ≤ (ε ^ m)⁻¹ := by
  rw [cappedRieszKernel, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (cappedInverseDistancePow_nonneg _ _ _), ← dist_eq_norm, mul_comm]
  exact distance_mul_cappedInverseDistancePow_bound m ε hε q

theorem scalarCappedRieszKernel_continuous {d : ℕ} (m : ℕ) (e : Ambient d)
    (ε : ℝ) (hε : 0 < ε) : Continuous (scalarCappedRieszKernel m e ε) :=
  continuous_const.inner (cappedRieszKernel_continuous m ε hε)

theorem scalarCappedRieszKernel_bound {d : ℕ} (m : ℕ) (e : Ambient d)
    (ε : ℝ) (hε : 0 < ε) (q : Ambient d × Ambient d) :
    |scalarCappedRieszKernel m e ε q| ≤ ‖e‖ * (ε ^ m)⁻¹ := by
  have hi : |inner ℝ e (cappedRieszKernel m ε q)| ≤ ‖e‖ * ‖cappedRieszKernel m ε q‖ := by
    simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) e (cappedRieszKernel m ε q)
  exact hi.trans (mul_le_mul_of_nonneg_left (cappedRieszKernel_norm_bound m ε hε q) (norm_nonneg e))

theorem closedNearCapWeight_measurable {d : ℕ} (m : ℕ) (ε : ℝ) :
    Measurable (closedNearCapWeight (d := d) m ε) :=
  measurable_const.indicator (nearPairSet_measurable ε)

theorem closedNearCapWeight_nonneg {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (q : Ambient d × Ambient d) : 0 ≤ closedNearCapWeight m ε q :=
  indicator_nonneg (fun _ _ => inv_nonneg.mpr (pow_nonneg hε.le m)) q

theorem closedNearCapWeight_symm {d : ℕ} (m : ℕ) (ε : ℝ) (x y : Ambient d) :
    closedNearCapWeight m ε (y, x) = closedNearCapWeight m ε (x, y) := by
  simp only [closedNearCapWeight, indicator_apply, nearPairSet, mem_ofPred_eq, mem_closedBall]
  simp only [dist_comm x y]

theorem scalarCappedRieszKernel_hard_error {d : ℕ} (m : ℕ) (e : Ambient d)
    (ε : ℝ) (hε : 0 < ε) (q : Ambient d × Ambient d) :
    |scalarCappedRieszKernel m e ε q - scalarTruncatedKernel m e ε q| ≤
      ‖e‖ * closedNearCapWeight m ε q := by
  by_cases hq : ε < dist q.1 q.2
  · have hnot : q ∉ nearPairSet ε := by
      simpa only [nearPairSet, mem_ofPred_eq, mem_closedBall, dist_comm q.2 q.1, not_le] using! hq
    rw [scalarCappedRieszKernel, cappedRieszKernel_eq_kernel m ε q hq.le,
      scalarTruncatedKernel, ite_eq_left hq, sub_self, abs_zero,
      closedNearCapWeight, indicator_of_notMem hnot, mul_zero]
  · have hyes : q ∈ nearPairSet ε := by
      simpa only [nearPairSet, mem_ofPred_eq, mem_closedBall, dist_comm q.2 q.1] using! le_of_not_gt hq
    rw [scalarTruncatedKernel, ite_eq_right hq, sub_zero, closedNearCapWeight, indicator_of_mem hyes]
    exact scalarCappedRieszKernel_bound m e ε hε q

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_CapErrorRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cap-error row bounds

The closed near-cap weight is constant on a closed ball and vanishes outside it.
Upper growth bounds give integrability of each row and a scale-independent integral bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped ENNReal

theorem closedNearCapWeight_section {d : ℕ} (m : ℕ) (ε : ℝ) (x : Ambient d) :
    (fun y => closedNearCapWeight m ε (x, y)) =
      (closedBall x ε).indicator (fun _ => (ε ^ m)⁻¹) := by
  funext y
  classical
  by_cases hy : y ∈ closedBall x ε
  · simp only [closedNearCapWeight, indicator_of_mem (show (x, y) ∈ nearPairSet ε from hy),
      indicator_of_mem hy]
  · simp only [closedNearCapWeight, indicator_of_notMem (show (x, y) ∉ nearPairSet ε from hy),
      indicator_of_notMem hy]

theorem closedNearCapWeight_row_integrable_and_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (ε : ℝ) (hε : 0 < ε) (x : Ambient d) :
    Integrable (fun y => closedNearCapWeight m ε (x, y)) μ ∧
      (∫ y, closedNearCapWeight m ε (x, y) ∂μ) ≤ C * 2 ^ m := by
  have hball : μ (closedBall x ε) ≤ ENNReal.ofReal (C * (2 * ε) ^ m) :=
    (measure_mono (closedBall_subset_ball (by linarith : ε < 2 * ε))).trans
      (hg.2 x (2 * ε) (by positivity))
  let : IsFiniteMeasure (μ.restrict (closedBall x ε)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hball.trans_lt ENNReal.ofReal_lt_top⟩
  have hreal : μ.real (closedBall x ε) ≤ C * (2 * ε) ^ m :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (pow_nonneg (by positivity) _)) hball
  rw [closedNearCapWeight_section]
  refine ⟨(integrable_indicator_iff measurableSet_closedBall).mpr (integrable_const _), ?_⟩
  rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul]
  calc
    μ.real (closedBall x ε) * (ε ^ m)⁻¹ ≤ (C * (2 * ε) ^ m) * (ε ^ m)⁻¹ :=
      mul_le_mul_of_nonneg_right hreal (by positivity)
    _ = C * 2 ^ m := by
      rw [mul_pow]
      have hne : ε ^ m ≠ 0 := pow_ne_zero _ hε.ne'
      field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_VectorL2PairingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A vector-valued L² norm estimate controls each scalar pairing against a fixed direction.
The proof combines pointwise inner-product bounds with the L² Cauchy–Schwarz inequality.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

theorem toLp_norm_eq_sqrt_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  rw [← toLp_norm_sq_eq_integral μ f hf, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem scalar_L2_pairing_of_vector_norm_bound {X : Type*} [MeasurableSpace X] {d : ℕ}
    (μ : Measure X) (f g : X → ℝ) (F : X → Ambient d)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hF : MemLp F 2 μ)
    (D : ℝ≥0) (hN : eLpNorm F 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) (e : Ambient d) :
    Integrable (fun x => g x * inner ℝ e (F x)) μ ∧
      |∫ x, g x * inner ℝ e (F x) ∂μ| ≤
        (‖e‖ * (D : ℝ)) * Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  let u := fun x => inner ℝ e (F x)
  have hpoint : ∀ᵐ x ∂μ, ‖u x‖ ≤ ‖e‖ * ‖F x‖ :=
    Filter.Eventually.of_forall fun x => norm_inner_le_norm (𝕜 := ℝ) e (F x)
  have hum : AEStronglyMeasurable u μ :=
    aestronglyMeasurable_const.inner hF.aestronglyMeasurable
  have hu : MemLp u 2 μ := hF.of_le_mul hum hpoint
  have hNu : eLpNorm u 2 μ ≤
      ENNReal.ofReal ‖e‖ * ((D : ℝ≥0∞) * eLpNorm f 2 μ) :=
    (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpoint 2).trans
      (mul_le_mul_right hN (ENNReal.ofReal ‖e‖))
  have hfin : ENNReal.ofReal ‖e‖ * ((D : ℝ≥0∞) * eLpNorm f 2 μ) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hf.eLpNorm_ne_top)
  have hnorm : ‖hu.toLp u‖ ≤ ‖e‖ * ((D : ℝ) * ‖hf.toLp f‖) := by
    simpa only [Lp.norm_toLp, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg e),
      ENNReal.coe_toReal] using! ENNReal.toReal_mono hfin hNu
  refine ⟨memLp_one_iff_integrable.mp (MeasureTheory.MemLp.mul (hφ := hg) (hf := hu)), ?_⟩
  rw [← toLp_inner_eq_integral μ g u hg hu]
  have hi : |inner ℝ (hg.toLp g) (hu.toLp u)| ≤ ‖hg.toLp g‖ * ‖hu.toLp u‖ := by
    simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) (hg.toLp g) (hu.toLp u)
  calc
    _ ≤ ‖hg.toLp g‖ * (‖e‖ * ((D : ℝ) * ‖hf.toLp f‖)) :=
      hi.trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
    _ = _ := by
      rw [toLp_norm_eq_sqrt_integral μ g hg, toLp_norm_eq_sqrt_integral μ f hf]
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_HardBilinearPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bilinear pairings for hard truncations

Integrability of bounded-kernel products permits the product-space bilinear form
to be rewritten as a pairing with the hard-truncated Riesz transform. This
identification connects kernel integrals with the vector-valued L² estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal ENNReal

theorem bounded_kernel_bilinear_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (k : X × X → ℝ) (hk : Measurable k)
    (B : ℝ) (hB : ∀ q, |k q| ≤ B)
    (f g : X → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun q : X × X => f q.1 * g q.2 * k q) (μ.prod μ) := by
  apply ((hf.abs.mul_prod hg.abs).mul_const B).mono'
    (((hfm.comp measurable_fst).mul (hgm.comp measurable_snd)).mul hk).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun q => by
    simp only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB q) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem truncated_inner_eq_weighted_scalar_integral {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth m C μ)
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ) (x : Ambient d) :
    inner ℝ e (truncated m μ ε f x) =
      ∫ y, f y * scalarTruncatedKernel m e ε (x, y) ∂μ := by
  have hi := truncation_integrable_of_globalGrowth m hm C μ hgrowth f hf x ε hε
  have hs : MeasurableSet {y : Ambient d | ε < dist x y} :=
    measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  unfold truncated
  rw [← integral_inner (𝕜 := ℝ) hi e, ← integral_indicator hs]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  by_cases hy : ε < dist x y
  · rw [indicator_of_mem (show y ∈ {y : Ambient d | ε < dist x y} from hy)]
    simp only [scalarTruncatedKernel, ite_eq_left hy, real_inner_smul_right]
  · rw [indicator_of_notMem (show y ∉ {y : Ambient d | ε < dist x y} from hy)]
    simp only [scalarTruncatedKernel, ite_eq_right hy, mul_zero]

theorem hard_bilinear_eq_truncated_pairing {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hgrowth : GlobalUpperGrowth m C μ)
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 μ) (hf1 : Integrable f μ) (hg1 : Integrable g μ) :
    (∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarTruncatedKernel m e ε q ∂μ.prod μ) =
      ∫ x, g x * inner ℝ e (truncated m μ ε f x) ∂μ := by
  have hI := bounded_kernel_bilinear_integrable μ (scalarTruncatedKernel m e ε)
    (scalarTruncatedKernel_measurable m e ε) (‖e‖ * (ε ^ m)⁻¹)
    (scalarTruncatedKernel_bound m e ε hε) g f hgm hfm hg1 hf1
  rw [integral_prod _ hI]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [mul_assoc]
  rw [integral_const_mul, ← truncated_inner_eq_weighted_scalar_integral m hm C μ hgrowth e ε hε f hf x]

theorem hard_bilinear_bound_of_native_L2 {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hgrowth : GlobalUpperGrowth m C μ)
    (D : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (e : Ambient d)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hf1 : Integrable f μ) (hg1 : Integrable g μ)
    (hTf : MemLp (truncated m μ ε f) 2 μ)
    (hN : eLpNorm (truncated m μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) :
    |∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarTruncatedKernel m e ε q ∂μ.prod μ| ≤
      (‖e‖ * (D : ℝ)) * Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  rw [hard_bilinear_eq_truncated_pairing m hm C μ hgrowth e ε hε f g hfm hgm hf hf1 hg1]
  exact (scalar_L2_pairing_of_vector_norm_bound μ f g (truncated m μ ε f) hf hg hTf D hN e).2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_CappedTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter
open scoped BoundedContinuousFunction

theorem scalarCappedTransform_integrable_and_bound {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f : Ambient d → ℝ) (hfm : Measurable f) (hf : Integrable f μ) (x : Ambient d) :
    Integrable (fun y => f y * scalarCappedRieszKernel m e ε (x, y)) μ ∧
      |scalarCappedTransform m μ e ε f x| ≤ (∫ y, |f y| ∂μ) * (‖e‖ * (ε ^ m)⁻¹) := by
  have hm : Measurable (fun y => f y * scalarCappedRieszKernel m e ε (x, y)) :=
    hfm.mul ((scalarCappedRieszKernel_continuous m e ε hε).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hb (y : Ambient d) : |f y * scalarCappedRieszKernel m e ε (x, y)| ≤
      |f y| * (‖e‖ * (ε ^ m)⁻¹) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (scalarCappedRieszKernel_bound m e ε hε (x, y)) (abs_nonneg _)
  have hI : Integrable (fun y => f y * scalarCappedRieszKernel m e ε (x, y)) μ := by
    apply (hf.abs.mul_const (‖e‖ * (ε ^ m)⁻¹)).mono' hm.aestronglyMeasurable
    exact Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using! hb y
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ y, |f y * scalarCappedRieszKernel m e ε (x, y)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ y, |f y| * (‖e‖ * (ε ^ m)⁻¹) ∂μ :=
      integral_mono hI.abs (hf.abs.mul_const (‖e‖ * (ε ^ m)⁻¹)) hb
    _ = _ := integral_mul_const _ _

theorem scalarCappedTransform_continuous {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f : Ambient d → ℝ) (hfm : Measurable f) (hf : Integrable f μ) :
    Continuous (scalarCappedTransform m μ e ε f) := by
  apply continuous_of_dominated (bound := fun y => |f y| * (‖e‖ * (ε ^ m)⁻¹))
  · intro x
    exact (scalarCappedTransform_integrable_and_bound m μ e ε hε f hfm hf x).1.aestronglyMeasurable
  · intro x
    apply Eventually.of_forall
    intro y
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (scalarCappedRieszKernel_bound m e ε hε (x, y)) (abs_nonneg _)
  · exact hf.abs.mul_const _
  · exact Eventually.of_forall fun y => continuous_const.mul
      ((scalarCappedRieszKernel_continuous m e ε hε).comp (continuous_id.prodMk continuous_const))

theorem exists_boundedContinuous_scalarCappedTransform {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f : Ambient d → ℝ) (hfm : Measurable f) (hf : Integrable f μ) :
    ∃ T : Ambient d →ᵇ ℝ, ∀ x, T x = scalarCappedTransform m μ e ε f x := by
  let B := (∫ y, |f y| ∂μ) * (‖e‖ * (ε ^ m)⁻¹)
  let T : Ambient d →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨scalarCappedTransform m μ e ε f, scalarCappedTransform_continuous m μ e ε hε f hfm hf⟩
    (2 * B) (by
      intro x y
      change dist (scalarCappedTransform m μ e ε f x) (scalarCappedTransform m μ e ε f y) ≤ 2 * B
      rw [Real.dist_eq]
      have hx := (scalarCappedTransform_integrable_and_bound m μ e ε hε f hfm hf x).2
      have hy := (scalarCappedTransform_integrable_and_bound m μ e ε hε f hfm hf y).2
      have ht := abs_sub_le (scalarCappedTransform m μ e ε f x) 0 (scalarCappedTransform m μ e ε f y)
      simp only [sub_zero, zero_sub, abs_neg] at ht
      dsimp only [B]
      linarith)
  exact ⟨T, fun _ => rfl⟩

theorem capped_bilinear_eq_scalarCappedTransform {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q ∂μ.prod μ) =
      ∫ x, g x * scalarCappedTransform m μ e ε f x ∂μ := by
  have hI := bounded_kernel_bilinear_integrable μ (scalarCappedRieszKernel m e ε)
    (scalarCappedRieszKernel_continuous m e ε hε).measurable (‖e‖ * (ε ^ m)⁻¹)
    (scalarCappedRieszKernel_bound m e ε hε) g f hgm hfm hg hf
  rw [integral_prod _ hI]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  simp only [mul_assoc, integral_const_mul]
  rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_CappedTransformL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction

theorem scalarCappedTransform_memLp_bound_of_bilinear {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f : Ambient d →ᵇ ℝ) (B : ℝ≥0)
    (hB : ∀ g : Ambient d →ᵇ ℝ,
      |∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q ∂μ.prod μ| ≤
        (B : ℝ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (∫ x, f x ^ 2 ∂μ)) :
    MemLp (scalarCappedTransform m μ e ε f) 2 μ ∧
      eLpNorm (scalarCappedTransform m μ e ε f) 2 μ ≤ (B : ℝ≥0∞) * eLpNorm f 2 μ := by
  have hf : MemLp f 2 μ :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖ (Eventually.of_forall f.norm_coe_le_norm)
  have hf1 := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  obtain ⟨T, hT⟩ := exists_boundedContinuous_scalarCappedTransform m μ e ε hε
    f f.continuous.measurable hf1
  have hTm : MemLp T 2 μ :=
    MemLp.of_bound T.continuous.aestronglyMeasurable ‖T‖ (Eventually.of_forall T.norm_coe_le_norm)
  have heq : scalarCappedTransform m μ e ε f = T := funext fun x => (hT x).symm
  rw [heq]
  have hpair : (∫ q : Ambient d × Ambient d, T q.1 * f q.2 * scalarCappedRieszKernel m e ε q
      ∂μ.prod μ) = ∫ x, T x ^ 2 ∂μ := by
    rw [capped_bilinear_eq_scalarCappedTransform m μ e ε hε f T
      f.continuous.measurable T.continuous.measurable hf1 (hTm.integrable (by norm_num)), heq]
    simp only [pow_two]
  have hI0 : 0 ≤ ∫ x, T x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg (T x)
  have hb := hB T
  rw [hpair, abs_of_nonneg hI0] at hb
  have hsqrt : Real.sqrt (∫ x, T x ^ 2 ∂μ) ≤ (B : ℝ) * Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
    by_cases hz : Real.sqrt (∫ x, T x ^ 2 ∂μ) = 0
    · rw [hz]
      positivity
    have hp : 0 < Real.sqrt (∫ x, T x ^ 2 ∂μ) :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    by_contra hn
    have hpos := mul_pos
      (sub_pos.mpr (lt_of_not_ge hn)) hp
    nlinarith [Real.sq_sqrt hI0]
  have hnorm : ‖hTm.toLp T‖ ≤ (B : ℝ) * ‖hf.toLp f‖ := by
    simpa only [toLp_norm_eq_sqrt_integral] using! hsqrt
  refine ⟨hTm, ?_⟩
  have he := ENNReal.ofReal_le_ofReal hnorm
  simpa only [Lp.norm_toLp, ENNReal.ofReal_mul B.coe_nonneg, ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_toReal hTm.eLpNorm_ne_top, ENNReal.ofReal_toReal hf.eLpNorm_ne_top] using! he

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FarRieszTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The scalar far Riesz transform

Subtracting the kernel at the localization center gives an integrable far-field
kernel under global upper growth. Quantitative decay bounds yield measurability
and local `L²` control of its scalar integral on the inner ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal

theorem scalar_far_kernel_bound {d : ℕ} (m : ℕ) (e a x y : Ambient d)
    (R : ℝ) (hR : 0 < R) (hx : 2 * dist x a ≤ R) (hy : R ≤ dist a y) :
    |inner ℝ e (kernel m x y - kernel m a y)| ≤
      ((2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * dist x a)) *
        inverseDistancePow (m + 1) a y := by
  let w := affineNormalHeight e a 0
  have hw : LipschitzWith ‖e‖₊ w := affineNormalHeight_lipschitz e a 0
  have hwa : w a = 0 := by simp only [w, affineNormalHeight, sub_self, inner_zero_right]
  have hwx : |w x| ≤ ‖e‖ * dist x a := by
    simpa only [Real.dist_eq, hwa, sub_zero, coe_nnnorm] using! hw.dist_le_mul x a
  have hcancel := cancelled_height_far_bound m w ‖e‖₊ hw a x y R hR hx hy
  simp only [hwa, abs_zero, zero_div, add_zero, coe_nnnorm] at hcancel
  have hk := inverseDistancePow_far_le (m + 1) a x y (hR.trans_le hy) (hx.trans hy)
  have heq : inner ℝ e (kernel m x y - kernel m a y) =
      w x * inverseDistancePow (m + 1) x y -
        w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y) := by
    rw [inner_sub_right, kernel_inner_normal_difference m e w (affineNormalHeight_difference e a 0),
      kernel_inner_normal_difference m e w (affineNormalHeight_difference e a 0), hwa]
    ring
  rw [heq]
  calc
    _ ≤ |w x * inverseDistancePow (m + 1) x y| +
        |w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using!
        abs_sub_le (w x * inverseDistancePow (m + 1) x y) 0
          (w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y))
    _ ≤ (‖e‖ * dist x a) * (2 ^ (m + 1) * inverseDistancePow (m + 1) a y) +
        (‖e‖ * (m + 1 : ℝ) * 2 ^ (m + 2) * dist x a) * inverseDistancePow (m + 1) a y := by
      apply add_le_add _ hcancel
      rw [abs_mul, abs_of_nonneg (inverseDistancePow_nonneg _ _ _)]
      exact mul_le_mul hwx hk (inverseDistancePow_nonneg _ _ _) (by positivity)
    _ = _ := by ring

theorem scalarFarRieszTransform_measurable {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (e a : Ambient d) (R : ℝ) :
    Measurable (scalarFarRieszTransform m μ e a R) := by
  have hm : Measurable (fun q : Ambient d × Ambient d =>
      inner ℝ e (kernel m q.1 q.2 - kernel m a q.2)) := by
    have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
    have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
    have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
    unfold kernel
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem scalarFarRieszTransform_integrable_and_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (e a x : Ambient d) (R : ℝ) (hR : 0 < R) (hx : 2 * dist x a ≤ R) :
    IntegrableOn (fun y => inner ℝ e (kernel m x y - kernel m a y)) (closedExterior a R) μ ∧
      |scalarFarRieszTransform m μ e a R x| ≤
        ((2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * dist x a)) *
          (2 * (C * 2 ^ m / R)) := by
  let B := (2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * dist x a)
  have hB : 0 ≤ B := by dsimp only [B] <;> positivity
  obtain ⟨hk, hbound⟩ := inverseDistancePow_closedExterior_integrable_and_bound m C μ hg a R hR
  have hm : Measurable (fun y => inner ℝ e (kernel m x y - kernel m a y)) := by
    have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
    have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
    have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
    unfold kernel
    fun_prop
  have hi : IntegrableOn (fun y => inner ℝ e (kernel m x y - kernel m a y)) (closedExterior a R) μ := by
    apply (hk.const_mul B).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
    simpa only [Real.norm_eq_abs] using! scalar_far_kernel_bound m e a x y R hR hx hy
  refine ⟨hi, ?_⟩
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ y in closedExterior a R, B * inverseDistancePow (m + 1) a y ∂μ := by
      apply integral_mono_ae hi.abs (hk.const_mul B)
      filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
      exact scalar_far_kernel_bound m e a x y R hR hx hy
    _ = B * ∫ y in closedExterior a R, inverseDistancePow (m + 1) a y ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound hB

theorem scalarFarRieszTransform_memLp_inner_ball {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e a : Ambient d) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R) :
    MemLp (scalarFarRieszTransform m μ e a R) 2 (μ.restrict (ball a H)) := by
  let := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a H hH
  let B := ((2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * H)) *
    (2 * (C * 2 ^ m / R))
  apply MemLp.of_bound (scalarFarRieszTransform_measurable m μ e a R).aestronglyMeasurable B
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  rw [Real.norm_eq_abs]
  have hxH : dist x a ≤ H := hx.le
  have hC := hg.1
  apply (scalarFarRieszTransform_integrable_and_bound m C μ hg e a x R hR (by linarith)).2.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxH (norm_nonneg _)) (by positivity))
    (by positivity)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_IsometricRieszPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isometric transport of Riesz pairings

Linear isometries intertwine the Riesz kernel and preserve its scalar interior
and far-field integrands. Pulling back balls and closed exteriors then transports
the corresponding scalar pairing to the lower-dimensional ambient space.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem kernel_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (x y : Ambient n) :
    kernel m (L x) (L y) = L (kernel m x y) := by
  simp only [kernel, ← map_sub, L.norm_map, map_smul]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_IsometricLocalTransforms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local Riesz transforms under linear isometries

Linear isometries commute with restriction to localization balls and preserve the
scalar capped kernels and far transforms. These identities transfer local transform
calculations between intrinsic plane coordinates and the ambient Euclidean space.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem linearIsometry_restrict_ball {n d : ℕ}
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n)) (a : Ambient n) (R : ℝ) :
    (μ.map L).restrict (ball (L a) R) = (μ.restrict (ball a R)).map L := by
  have hpre : L ⁻¹' ball (L a) R = ball a R := by
    ext x
    simp only [mem_preimage, mem_ball, L.dist_map]
  rw [Measure.restrict_map L.continuous.measurable measurableSet_ball, hpre]

theorem scalarCappedRieszKernel_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (e : Ambient n) (ε : ℝ) (x y : Ambient n) :
    scalarCappedRieszKernel m (L e) ε (L x, L y) = scalarCappedRieszKernel m e ε (x, y) := by
  have heq : cappedRieszKernel m ε (L x, L y) = L (cappedRieszKernel m ε (x, y)) := by
    simp only [cappedRieszKernel, cappedInverseDistancePow, L.dist_map, map_smul, map_sub]
  rw [scalarCappedRieszKernel, heq, L.inner_map_map]
  rfl

theorem scalarCappedTransform_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n))
    (e : Ambient n) (ε : ℝ) (f : Ambient d → ℝ) (x : Ambient n) :
    scalarCappedTransform m (μ.map L) (L e) ε f (L x) =
      scalarCappedTransform m μ e ε (fun y => f (L y)) x := by
  unfold scalarCappedTransform
  rw [L.isometry.isClosedEmbedding.measurableEmbedding.integral_map]
  simp only [scalarCappedRieszKernel_linearIsometry]

theorem scalarCappedTransform_ball_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n))
    (e a : Ambient n) (R ε : ℝ) (x : Ambient n) :
    scalarCappedTransform m ((μ.map L).restrict (ball (L a) R)) (L e) ε (fun _ => 1) (L x) =
      scalarCappedTransform m (μ.restrict (ball a R)) e ε (fun _ => 1) x := by
  rw [linearIsometry_restrict_ball, scalarCappedTransform_linearIsometry]

theorem scalarFarRieszTransform_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n))
    (e a : Ambient n) (R : ℝ) (x : Ambient n) :
    scalarFarRieszTransform m (μ.map L) (L e) (L a) R (L x) =
      scalarFarRieszTransform m μ e a R x := by
  have hext : L ⁻¹' closedExterior (L a) R = closedExterior a R := by
    ext y
    simp only [mem_preimage, closedExterior, mem_ofPred_eq, L.dist_map]
  unfold scalarFarRieszTransform
  rw [Measure.restrict_map L.continuous.measurable (closedExterior_measurable (L a) R),
    hext, L.isometry.isClosedEmbedding.measurableEmbedding.integral_map]
  simp only [kernel_linearIsometry, ← map_sub, L.inner_map_map]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RestrictedTruncationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal ENNReal

theorem truncated_restriction_eq_indicator_function {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (ε : ℝ) (f : Ambient d → ℝ) :
    truncated m (μ.restrict s) ε f = truncated m μ ε (s.indicator f) := by
  classical
  funext x
  have ht : MeasurableSet {y : Ambient d | ε < dist x y} :=
    measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  have heq : (fun y => s.indicator f y • kernel m x y) =
      s.indicator (fun y => f y • kernel m x y) := by
    funext y
    by_cases hy : y ∈ s
    · simp only [indicator_of_mem hy]
    · simp only [indicator_of_notMem hy, zero_smul]
  unfold truncated
  rw [heq, integral_indicator hs, Measure.restrict_restrict ht,
    Measure.restrict_restrict hs, inter_comm]

theorem native_truncation_bound_restrict {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (D : ℝ≥0)
    (hB : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated m μ ε f) 2 μ ∧
        eLpNorm (truncated m μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (s : Set (Ambient d)) (hs : MeasurableSet s) :
    ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ.restrict s) →
      MemLp (truncated m (μ.restrict s) ε f) 2 (μ.restrict s) ∧
        eLpNorm (truncated m (μ.restrict s) ε f) 2 (μ.restrict s) ≤
          (D : ℝ≥0∞) * eLpNorm f 2 (μ.restrict s) := by
  intro ε hε f hf
  have hi : MemLp (s.indicator f) 2 μ := (memLp_indicator_iff_restrict hs).mpr hf
  obtain ⟨hT, hN⟩ := hB ε hε (s.indicator f) hi
  rw [truncated_restriction_eq_indicator_function m μ s hs ε f]
  refine ⟨hT.restrict s, ?_⟩
  calc
    _ ≤ eLpNorm (truncated m μ ε (s.indicator f)) 2 μ :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ (D : ℝ≥0∞) * eLpNorm (s.indicator f) 2 μ := hN
    _ = _ := by rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_WeakRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weak convergence on continuity sets

Weak convergence of finite measures controls the masses of sets with null boundary.
Weighting by bounded continuous nonnegative functions transfers this control to restricted
integrals, providing continuity-set versions of the weak convergence estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem finiteMeasure_continuitySet_mass_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d))
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) :
    Tendsto (fun j => (μ j : Measure (Ambient d)).real s) atTop
      (𝓝 ((ν : Measure (Ambient d)).real s)) := by
  by_cases hν : ν = 0
  · subst ν
    have ht : Tendsto (fun j => (μ j : Measure (Ambient d)).real univ) atTop (𝓝 0) := by
      simpa using! NNReal.continuous_coe.continuousAt.tendsto.comp hweak.mass
    simpa using! squeeze_zero (fun _ => measureReal_nonneg)
      (fun j => measureReal_mono (μ := (μ j : Measure (Ambient d))) (subset_univ s)) ht
  · exact finiteMeasure_cell_mass_tendsto μ ν hweak hν s hboundary

theorem weightedFiniteMeasure_integral {d : ℕ} (μ : FiniteMeasure (Ambient d))
    (f : Ambient d →ᵇ ℝ≥0) (g : Ambient d → ℝ) :
    (∫ x, g x ∂(weightedFiniteMeasure μ f : Measure (Ambient d))) =
      ∫ x, (f x : ℝ) * g x ∂(μ : Measure (Ambient d)) := by
  exact integral_withDensity_eq_integral_smul (μ := (μ : Measure (Ambient d)))
    f.continuous.measurable g

theorem weightedFiniteMeasure_real_set {d : ℕ} (μ : FiniteMeasure (Ambient d))
    (f : Ambient d →ᵇ ℝ≥0) (s : Set (Ambient d)) (hs : MeasurableSet s) :
    (weightedFiniteMeasure μ f : Measure (Ambient d)).real s =
      ∫ x in s, (f x : ℝ) ∂(μ : Measure (Ambient d)) := by
  change ((μ : Measure (Ambient d)).withDensity (fun x => (f x : ℝ≥0∞))).real s = _
  rw [Measure.real, withDensity_apply _ hs]
  exact f.toReal_lintegral_coe_eq_integral ((μ : Measure (Ambient d)).restrict s)

theorem weightedFiniteMeasure_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (f : Ambient d →ᵇ ℝ≥0) :
    Tendsto (fun j => weightedFiniteMeasure (μ j) f) atTop (𝓝 (weightedFiniteMeasure ν f)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  simp only [weightedFiniteMeasure_integral]
  let f₀ : Ambient d →ᵇ ℝ := BoundedContinuousFunction.comp ((↑) : ℝ≥0 → ℝ)
    NNReal.isometry_coe.lipschitz f
  exact FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (f₀ * g)

theorem weak_setIntegral_nnreal_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) (f : Ambient d →ᵇ ℝ≥0) :
    Tendsto (fun j => ∫ x in s, (f x : ℝ) ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x in s, (f x : ℝ) ∂(ν : Measure (Ambient d)))) := by
  have hb : (weightedFiniteMeasure ν f : Measure (Ambient d)) (frontier s) = 0 :=
    withDensity_absolutelyContinuous _ _ hboundary
  have h := finiteMeasure_continuitySet_mass_tendsto (fun j => weightedFiniteMeasure (μ j) f)
    (weightedFiniteMeasure ν f) (weightedFiniteMeasure_tendsto μ ν hweak f) s hb
  simpa only [weightedFiniteMeasure_real_set _ f s hs] using! h

theorem weak_setIntegral_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) (f : Ambient d →ᵇ ℝ) :
    Tendsto (fun j => ∫ x in s, f x ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x in s, f x ∂(ν : Measure (Ambient d)))) := by
  have hp := weak_setIntegral_nnreal_tendsto μ ν hweak s hs hboundary f.nnrealPart
  have hn := weak_setIntegral_nnreal_tendsto μ ν hweak s hs hboundary (-f).nnrealPart
  simpa only [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub] using! hp.sub hn

theorem restrictedFiniteMeasure_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) :
    Tendsto (fun j => restrictedFiniteMeasure (μ j) s) atTop (𝓝 (restrictedFiniteMeasure ν s)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  exact fun f => weak_setIntegral_tendsto μ ν hweak s hs hboundary f

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactWeakConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction CompactlySupported

theorem compactWeightedFiniteMeasure_integral {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ≥0)) (g : Ambient d → ℝ) :
    (∫ x, g x ∂(compactWeightedFiniteMeasure μ f : Measure (Ambient d))) =
      ∫ x, (f x : ℝ) * g x ∂μ := by
  exact integral_withDensity_eq_integral_smul f.continuous.measurable g

theorem compactWeightedFiniteMeasure_tendsto {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (f : C_c(Ambient d, ℝ≥0)) :
    Tendsto (fun j => compactWeightedFiniteMeasure (μ j) f) atTop
      (𝓝 (compactWeightedFiniteMeasure ν f)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  let test : C_c(Ambient d, ℝ) :=
    ⟨⟨fun x => f.toReal x * g x, f.toReal.continuous.mul g.continuous⟩,
      f.toReal.hasCompactSupport.mul_right⟩
  have ht := hlocal test
  change Tendsto (fun j => ∫ x, f.toReal x * g x ∂μ j) atTop
    (𝓝 (∫ x, f.toReal x * g x ∂ν)) at ht
  simpa only [compactWeightedFiniteMeasure_integral,
    CompactlySupportedContinuousMap.toReal_apply] using! ht

theorem exists_compact_nonneg_cutoff {d : ℕ} (s : Set (Ambient d)) (hs : IsCompact s) :
    ∃ f : C_c(Ambient d, ℝ≥0), (∀ x ∈ s, f x = 1) ∧ ∀ x, f x ≤ 1 := by
  obtain ⟨g, hgs, _, hgc, hg⟩ :=
    exists_continuous_one_zero_of_isCompact hs isClosed_empty (disjoint_empty s)
  let g₀ : C_c(Ambient d, ℝ) := ⟨g, hgc⟩
  refine ⟨g₀.nnrealPart, ?_, ?_⟩
  · intro x hx
    change Real.toNNReal (g x) = 1
    rw [show g x = 1 from hgs hx]
    simp
  · intro x
    change Real.toNNReal (g x) ≤ 1
    simpa using! Real.toNNReal_le_toNNReal (hg x).2

theorem compactWeightedFiniteMeasure_restrict {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ≥0))
    (s : Set (Ambient d)) (hs : MeasurableSet s) (hf : ∀ x ∈ s, f x = 1) :
    (compactWeightedFiniteMeasure μ f : Measure (Ambient d)).restrict s = μ.restrict s := by
  change (μ.withDensity (fun x => (f x : ℝ≥0∞))).restrict s = _
  rw [restrict_withDensity hs]
  calc
    _ = (μ.restrict s).withDensity 1 := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem hs] with x hx
      simp only [hf x hx, ENNReal.coe_one, Pi.one_apply]
    _ = _ := withDensity_one

theorem compactTestConvergence_restrict_tendsto {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (s : Set (Ambient d))
    (hs : MeasurableSet s) (hc : IsCompact (closure s))
    (hboundary : ν (frontier s) = 0) :
    Tendsto (fun j => relativelyCompactFiniteMeasure (μ j) s hc) atTop
      (𝓝 (relativelyCompactFiniteMeasure ν s hc)) := by
  obtain ⟨f, hf, _⟩ := exists_compact_nonneg_cutoff (closure s) hc
  have hf' : ∀ x ∈ s, f x = 1 := fun x hx => hf x (subset_closure hx)
  have hb : (compactWeightedFiniteMeasure ν f : Measure (Ambient d)) (frontier s) = 0 :=
    withDensity_absolutelyContinuous _ _ hboundary
  have h := restrictedFiniteMeasure_tendsto (fun j => compactWeightedFiniteMeasure (μ j) f)
    (compactWeightedFiniteMeasure ν f) (compactWeightedFiniteMeasure_tendsto μ ν hlocal f) s hs hb
  have heq : ∀ (ρ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ρ],
      restrictedFiniteMeasure (compactWeightedFiniteMeasure ρ f) s =
        relativelyCompactFiniteMeasure ρ s hc := by
    intro ρ _
    apply Subtype.ext
    exact compactWeightedFiniteMeasure_restrict ρ f s hs hf'
  simpa only [heq] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_SchurBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bilinear Schur estimates

A nonnegative symmetric kernel with uniformly bounded row integrals defines an
integrable bilinear pairing on square-integrable functions. Factoring the kernel
through its square root reduces the quantitative bound to Cauchy–Schwarz on the
product measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Function Set

variable {X : Type*} [MeasurableSpace X]

theorem schur_bilinear_integrable_and_sq_bound
    (μ : Measure X) [IsFiniteMeasure μ] (k : X × X → ℝ)
    (hk : Measurable k) (hk0 : ∀ q, 0 ≤ k q) (hsymm : ∀ x y, k (y, x) = k (x, y))
    (hrow : ∀ x, Integrable (fun y => k (x, y)) μ)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, (∫ y, k (x, y) ∂μ) ≤ B)
    (f g : X → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun q : X × X => f q.1 * g q.2 * k q) (μ.prod μ) ∧
      (∫ q : X × X, f q.1 * g q.2 * k q ∂μ.prod μ) ^ 2 ≤
        B ^ 2 * (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  obtain ⟨hif, hbf⟩ := row_weighted_square_integrable_and_bound μ k hk hk0 hrow B hbound f hfm hf
  obtain ⟨hig, hbg⟩ := row_weighted_square_integrable_and_bound μ k hk hk0 hrow B hbound g hgm hg
  have hswap (q : X × X) : k q.swap = k q := hsymm q.1 q.2
  have hig' : Integrable (fun q : X × X => g q.2 ^ 2 * k q) (μ.prod μ) := by
    simpa only [Function.comp_def, Prod.fst_swap, hswap] using! hig.swap
  have hbg' : (∫ q : X × X, g q.2 ^ 2 * k q ∂μ.prod μ) ≤ B * (∫ x, g x ^ 2 ∂μ) := by
    have heq := integral_prod_swap (μ := μ) (ν := μ) (fun q : X × X => g q.1 ^ 2 * k q)
    simp only [Prod.fst_swap, hswap] at heq
    exact heq.trans_le hbg
  let F : X × X → ℝ := fun q => f q.1 * Real.sqrt (k q)
  let G : X × X → ℝ := fun q => g q.2 * Real.sqrt (k q)
  have hFsq (q : X × X) : F q ^ 2 = f q.1 ^ 2 * k q := by
    dsimp only [F]
    rw [mul_pow, Real.sq_sqrt (hk0 q)]
  have hGsq (q : X × X) : G q ^ 2 = g q.2 ^ 2 * k q := by
    dsimp only [G]
    rw [mul_pow, Real.sq_sqrt (hk0 q)]
  have hF : MemLp F 2 (μ.prod μ) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop : AEStronglyMeasurable F (μ.prod μ))).mpr
    simpa only [hFsq] using! hif
  have hG : MemLp G 2 (μ.prod μ) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop : AEStronglyMeasurable G (μ.prod μ))).mpr
    simpa only [hGsq] using! hig'
  have hprod : (fun q : X × X => F q * G q) = fun q => f q.1 * g q.2 * k q := by
    funext q
    change (f q.1 * Real.sqrt (k q)) * (g q.2 * Real.sqrt (k q)) = _
    calc
      _ = f q.1 * g q.2 * (Real.sqrt (k q)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (hk0 q)]
  have hI : Integrable (fun q => F q * G q) (μ.prod μ) :=
    memLp_one_iff_integrable.mp (MeasureTheory.MemLp.mul (hφ := hF) (hf := hG))
  refine ⟨hprod ▸ hI, ?_⟩
  have hcs := integral_mul_cauchy_schwarz_sq (μ.prod μ) F G hF hG
  rw [hprod] at hcs
  simp only [hFsq, hGsq] at hcs
  calc
    _ ≤ (∫ q : X × X, f q.1 ^ 2 * k q ∂μ.prod μ) *
        (∫ q : X × X, g q.2 ^ 2 * k q ∂μ.prod μ) := hcs
    _ ≤ (B * (∫ x, f x ^ 2 ∂μ)) * (B * (∫ x, g x ^ 2 ∂μ)) :=
      mul_le_mul hbf hbg' (integral_nonneg fun q => mul_nonneg (sq_nonneg _) (hk0 q))
        (mul_nonneg hB (integral_nonneg fun x => sq_nonneg (f x)))
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CapErrorBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem scalar_cap_error_bilinear_integrable_and_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hgrowth : GlobalUpperGrowth m C μ)
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun q : Ambient d × Ambient d => f q.1 * g q.2 *
      (scalarCappedRieszKernel m e ε q - scalarTruncatedKernel m e ε q)) (μ.prod μ) ∧
    |∫ q : Ambient d × Ambient d, f q.1 * g q.2 *
      (scalarCappedRieszKernel m e ε q - scalarTruncatedKernel m e ε q) ∂μ.prod μ| ≤
      (‖e‖ * (C * 2 ^ m)) * Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  let k := closedNearCapWeight (d := d) m ε
  let W := fun q : Ambient d × Ambient d => |f q.1| * |g q.2| * k q
  let E := fun q : Ambient d × Ambient d => f q.1 * g q.2 *
    (scalarCappedRieszKernel m e ε q - scalarTruncatedKernel m e ε q)
  have hC : 0 ≤ C * 2 ^ m := mul_nonneg hgrowth.1 (by positivity)
  obtain ⟨hW, hWsq⟩ := schur_bilinear_integrable_and_sq_bound μ k
    (closedNearCapWeight_measurable m ε) (closedNearCapWeight_nonneg m ε hε)
    (closedNearCapWeight_symm m ε)
    (fun x => (closedNearCapWeight_row_integrable_and_bound m C μ hgrowth ε hε x).1)
    (C * 2 ^ m) hC
    (fun x => (closedNearCapWeight_row_integrable_and_bound m C μ hgrowth ε hε x).2)
    (fun x => |f x|) (fun x => |g x|) hfm.abs hgm.abs hf.abs hg.abs
  simp only [sq_abs] at hWsq
  have hW0 (q : Ambient d × Ambient d) : 0 ≤ W q :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (closedNearCapWeight_nonneg m ε hε q)
  have hpoint (q : Ambient d × Ambient d) : |E q| ≤ ‖e‖ * W q := by
    dsimp only [E, W]
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (|f q.1| * |g q.2|) * (‖e‖ * k q) :=
        mul_le_mul_of_nonneg_left (scalarCappedRieszKernel_hard_error m e ε hε q)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = _ := by ring
  have hEm : Measurable E :=
    ((hfm.comp measurable_fst).mul (hgm.comp measurable_snd)).mul
      ((scalarCappedRieszKernel_continuous m e ε hε).measurable.sub
        (scalarTruncatedKernel_measurable m e ε))
  have hE : Integrable E (μ.prod μ) := by
    apply (hW.const_mul ‖e‖).mono' hEm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun q => by
      simpa only [Real.norm_eq_abs] using! hpoint q
  have habs : |∫ q, E q ∂μ.prod μ| ≤ ‖e‖ * (∫ q, W q ∂μ.prod μ) := by
    calc
      _ ≤ ∫ q, |E q| ∂μ.prod μ := abs_integral_le_integral_abs
      _ ≤ ∫ q, ‖e‖ * W q ∂μ.prod μ := integral_mono hE.abs (hW.const_mul ‖e‖) hpoint
      _ = _ := integral_const_mul _ _
  refine ⟨hE, ?_⟩
  have hF0 : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg (f x)
  have hG0 : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg (g x)
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  calc
    _ ≤ (‖e‖ * (∫ q, W q ∂μ.prod μ)) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (integral_nonneg hW0))).mpr habs
    _ ≤ ‖e‖ ^ 2 * ((C * 2 ^ m) ^ 2 * (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ)) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hWsq (sq_nonneg _)
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt hF0, Real.sq_sqrt hG0]
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedBilinearL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

theorem capped_bilinear_bound_of_native_L2 {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hgrowth : GlobalUpperGrowth m C μ)
    (D : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (e : Ambient d)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hTf : MemLp (truncated m μ ε f) 2 μ)
    (hN : eLpNorm (truncated m μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) :
    |∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q ∂μ.prod μ| ≤
      (‖e‖ * ((D : ℝ) + C * 2 ^ m)) *
        Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  have hf1 := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hg1 := hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcap := bounded_kernel_bilinear_integrable μ (scalarCappedRieszKernel m e ε)
    (scalarCappedRieszKernel_continuous m e ε hε).measurable (‖e‖ * (ε ^ m)⁻¹)
    (scalarCappedRieszKernel_bound m e ε hε) g f hgm hfm hg1 hf1
  have hhard := bounded_kernel_bilinear_integrable μ (scalarTruncatedKernel m e ε)
    (scalarTruncatedKernel_measurable m e ε) (‖e‖ * (ε ^ m)⁻¹)
    (scalarTruncatedKernel_bound m e ε hε) g f hgm hfm hg1 hf1
  have hb := hard_bilinear_bound_of_native_L2 m hm C μ hgrowth D ε hε e
    f g hfm hgm hf hg hf1 hg1 hTf hN
  have he := (scalar_cap_error_bilinear_integrable_and_bound m C μ hgrowth e ε hε
    g f hgm hfm hg hf).2
  have hdiff : (∫ q : Ambient d × Ambient d, g q.1 * f q.2 *
      (scalarCappedRieszKernel m e ε q - scalarTruncatedKernel m e ε q) ∂μ.prod μ) =
      (∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q ∂μ.prod μ) -
      (∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarTruncatedKernel m e ε q ∂μ.prod μ) := by
    simp only [mul_sub]
    exact integral_sub hcap hhard
  rw [hdiff] at he
  let P := ∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q ∂μ.prod μ
  let H := ∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarTruncatedKernel m e ε q ∂μ.prod μ
  have ht : |P| ≤ |H| + |P - H| := by
    have h := abs_add_le H (P - H)
    rw [show H + (P - H) = P by ring] at h
    exact h
  calc
    _ ≤ |H| + |P - H| := ht
    _ ≤ (‖e‖ * (D : ℝ)) * Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (∫ x, f x ^ 2 ∂μ) +
        (‖e‖ * (C * 2 ^ m)) * Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (∫ x, f x ^ 2 ∂μ) :=
      add_le_add hb he
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_FiniteWeakProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem finiteMeasure_smul_product {d k : ℕ}
    (μ : FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient k)) (c b : ℝ≥0) :
    (c • μ).prod (b • ν) = (c * b) • μ.prod ν := by
  apply Subtype.ext
  change (c • (μ : Measure (Ambient d))).prod (b • (ν : Measure (Ambient k))) =
    (c * b) • (μ : Measure (Ambient d)).prod (ν : Measure (Ambient k))
  simp only [← Measure.coe_nnreal_smul, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, ENNReal.coe_mul, mul_comm]

theorem finiteMeasure_product_normalization {d k : ℕ}
    (μ : FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient k)) :
    μ.prod ν = (μ.mass * ν.mass) • (μ.normalize.prod ν.normalize).toFiniteMeasure := by
  calc
    _ = (μ.mass • μ.normalize.toFiniteMeasure).prod
        (ν.mass • ν.normalize.toFiniteMeasure) :=
      congrArg₂ FiniteMeasure.prod μ.self_eq_mass_smul_normalize ν.self_eq_mass_smul_normalize
    _ = _ := finiteMeasure_smul_product μ.normalize.toFiniteMeasure ν.normalize.toFiniteMeasure
      μ.mass ν.mass

theorem finiteMeasure_product_tendsto_nonzero {d k : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : ℕ → FiniteMeasure (Ambient k))
    (μ₀ : FiniteMeasure (Ambient d)) (ν₀ : FiniteMeasure (Ambient k))
    (hμ : Tendsto μ atTop (𝓝 μ₀)) (hν : Tendsto ν atTop (𝓝 ν₀))
    (hμ₀ : μ₀ ≠ 0) (hν₀ : ν₀ ≠ 0) :
    Tendsto (fun j => (μ j).prod (ν j)) atTop (𝓝 (μ₀.prod ν₀)) := by
  have hP := FiniteMeasure.tendsto_normalize_of_tendsto hμ hμ₀
  have hQ := FiniteMeasure.tendsto_normalize_of_tendsto hν hν₀
  have hPQ : Tendsto (fun j => (μ j).normalize.prod (ν j).normalize) atTop
      (𝓝 (μ₀.normalize.prod ν₀.normalize)) :=
    (ProbabilityMeasure.continuous_prod.tendsto (μ₀.normalize, ν₀.normalize)).comp (hP.prodMk_nhds hQ)
  have hF := (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto
    (μ₀.normalize.prod ν₀.normalize)).comp hPQ
  have hm := hμ.mass.mul hν.mass
  have ht := hm.smul hF
  simpa only [Function.comp_apply, ← finiteMeasure_product_normalization] using! ht

theorem finiteMeasure_bounded_product_integral_tendsto {d k : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : ℕ → FiniteMeasure (Ambient k))
    (μ₀ : FiniteMeasure (Ambient d)) (ν₀ : FiniteMeasure (Ambient k))
    (hμ : Tendsto μ atTop (𝓝 μ₀)) (hν : Tendsto ν atTop (𝓝 ν₀))
    (hμ₀ : μ₀ ≠ 0) (hν₀ : ν₀ ≠ 0) (F : Ambient d × Ambient k →ᵇ ℝ) :
    Tendsto (fun j => ∫ q, F q ∂(μ j : Measure (Ambient d)).prod (ν j : Measure (Ambient k)))
      atTop (𝓝 (∫ q, F q ∂(μ₀ : Measure (Ambient d)).prod (ν₀ : Measure (Ambient k)))) :=
  FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
    (finiteMeasure_product_tendsto_nonzero μ ν μ₀ ν₀ hμ hν hμ₀ hν₀) F

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_WeakCappedL2Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem capped_bilinear_integral_tendsto {d : ℕ} (m : ℕ)
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (hν : ν ≠ 0)
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε) (f g : Ambient d →ᵇ ℝ) :
    Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      g q.1 * f q.2 * scalarCappedRieszKernel m e ε q
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q
        ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))) := by
  let B := ‖e‖ * (ε ^ m)⁻¹
  let K : Ambient d × Ambient d →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨scalarCappedRieszKernel m e ε, scalarCappedRieszKernel_continuous m e ε hε⟩ (2 * B) (by
      intro q z
      change dist (scalarCappedRieszKernel m e ε q) (scalarCappedRieszKernel m e ε z) ≤ 2 * B
      rw [Real.dist_eq]
      have ht := abs_sub_le (scalarCappedRieszKernel m e ε q) 0 (scalarCappedRieszKernel m e ε z)
      simp only [sub_zero, zero_sub, abs_neg] at ht
      have hq := scalarCappedRieszKernel_bound m e ε hε q
      have hz := scalarCappedRieszKernel_bound m e ε hε z
      dsimp only [B]
      linarith)
  let F : Ambient d × Ambient d →ᵇ ℝ :=
    (g.compContinuous ⟨Prod.fst, continuous_fst⟩ * f.compContinuous ⟨Prod.snd, continuous_snd⟩) * K
  exact finiteMeasure_bounded_product_integral_tendsto μ μ ν ν hweak hweak hν hν F

theorem weak_capped_bilinear_bound_of_native_L2 {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (hν : ν ≠ 0)
    (hgrowth : ∀ j, GlobalUpperGrowth m C (μ j : Measure (Ambient d)))
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j : Measure (Ambient d)) →
      MemLp (truncated m (μ j : Measure (Ambient d)) ε f) 2 (μ j : Measure (Ambient d)) ∧
        eLpNorm (truncated m (μ j : Measure (Ambient d)) ε f) 2 (μ j : Measure (Ambient d)) ≤
          (D : ℝ≥0∞) * eLpNorm f 2 (μ j : Measure (Ambient d)))
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε) (f g : Ambient d →ᵇ ℝ) :
    |∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q
      ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d))| ≤
      (‖e‖ * ((D : ℝ) + C * 2 ^ m)) * Real.sqrt (∫ x, g x ^ 2 ∂(ν : Measure (Ambient d))) *
        Real.sqrt (∫ x, f x ^ 2 ∂(ν : Measure (Ambient d))) := by
  have hpair := capped_bilinear_integral_tendsto m μ ν hweak hν e ε hε f g
  have hf : Tendsto (fun j => ∫ x, f x ^ 2 ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x, f x ^ 2 ∂(ν : Measure (Ambient d)))) := by
    simpa only [BoundedContinuousFunction.mul_apply, ← pow_two] using!
      FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (f * f)
  have hg : Tendsto (fun j => ∫ x, g x ^ 2 ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x, g x ^ 2 ∂(ν : Measure (Ambient d)))) := by
    simpa only [BoundedContinuousFunction.mul_apply, ← pow_two] using!
      FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (g * g)
  have hnorms := (hg.sqrt.const_mul (‖e‖ * ((D : ℝ) + C * 2 ^ m))).mul hf.sqrt
  apply le_of_tendsto_of_tendsto hpair.abs hnorms
  apply Filter.Eventually.of_forall
  intro j
  have hf₂ : MemLp f 2 (μ j : Measure (Ambient d)) :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖ (Filter.Eventually.of_forall f.norm_coe_le_norm)
  have hg₂ : MemLp g 2 (μ j : Measure (Ambient d)) :=
    MemLp.of_bound g.continuous.aestronglyMeasurable ‖g‖ (Filter.Eventually.of_forall g.norm_coe_le_norm)
  obtain ⟨hT, hN⟩ := hB j ε hε f hf₂
  exact capped_bilinear_bound_of_native_L2 m hm C (μ j : Measure (Ambient d)) (hgrowth j)
    D ε hε e f g f.continuous.measurable g.continuous.measurable hf₂ hg₂ hT hN

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactLimitCappedL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem compact_limit_capped_bilinear_L2_bound {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth m C (μ j)) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j) →
      MemLp (truncated m (μ j) ε f) 2 (μ j) ∧
        eLpNorm (truncated m (μ j) ε f) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm f 2 (μ j))
    (a : Ambient d) (R : ℝ)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0)
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε) (f g : Ambient d →ᵇ ℝ) :
    |∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q
      ∂(ν.restrict (ball a R)).prod (ν.restrict (ball a R))| ≤
      (‖e‖ * ((D : ℝ) + C * 2 ^ m)) * Real.sqrt (∫ x in ball a R, g x ^ 2 ∂ν) *
        Real.sqrt (∫ x in ball a R, f x ^ 2 ∂ν) := by
  have hcompact : IsCompact (closure (ball a R)) :=
    (isCompact_closedBall a R).of_isClosed_subset isClosed_closure
      (closure_minimal ball_subset_closedBall isClosed_closedBall)
  let μ' := fun j => relativelyCompactFiniteMeasure (μ j) (ball a R) hcompact
  let ν' := relativelyCompactFiniteMeasure ν (ball a R) hcompact
  have hweak' : Tendsto μ' atTop (𝓝 ν') :=
    compactTestConvergence_restrict_tendsto μ ν hweak (ball a R) measurableSet_ball hcompact hboundary
  have hν' : ν' ≠ 0 := by
    intro hz
    have heq := congrArg (fun ρ : FiniteMeasure (Ambient d) => (ρ : Measure (Ambient d)) univ) hz
    apply hmass
    change (ν.restrict (ball a R)) univ = (0 : Measure (Ambient d)) univ at heq
    simpa only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using! heq
  exact weak_capped_bilinear_bound_of_native_L2 m hm C μ' ν' hweak' hν'
    (fun j => globalGrowth_restrict m C (μ j) (hgrowth j) (ball a R)) D
    (fun j => native_truncation_bound_restrict m (μ j) D (hB j) (ball a R) measurableSet_ball)
    e ε hε f g

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactLimitCappedTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Capped transforms under compact-test limits

Bilinear bounds inherited by a weak limit yield scalar capped-transform L² bounds
on ball restrictions, with constants controlled by upper growth and truncation bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem compact_limit_scalarCappedTransform_L2_bound {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth m C (μ j)) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j) →
      MemLp (truncated m (μ j) ε f) 2 (μ j) ∧
        eLpNorm (truncated m (μ j) ε f) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm f 2 (μ j))
    (a : Ambient d) (R : ℝ)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0)
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε) (f : Ambient d →ᵇ ℝ) :
    MemLp (scalarCappedTransform m (ν.restrict (ball a R)) e ε f) 2 (ν.restrict (ball a R)) ∧
      eLpNorm (scalarCappedTransform m (ν.restrict (ball a R)) e ε f) 2 (ν.restrict (ball a R)) ≤
        (Real.toNNReal (‖e‖ * ((D : ℝ) + C * 2 ^ m)) : ℝ≥0∞) * eLpNorm f 2 (ν.restrict (ball a R)) := by
  have hcompact : IsCompact (closure (ball a R)) :=
    (isCompact_closedBall a R).of_isClosed_subset isClosed_closure
      (closure_minimal ball_subset_closedBall isClosed_closedBall)
  let := relativelyCompact_restrict_finite ν (ball a R) hcompact
  have hnonneg : 0 ≤ ‖e‖ * ((D : ℝ) + C * 2 ^ m) :=
    mul_nonneg (norm_nonneg _) (add_nonneg D.coe_nonneg (mul_nonneg (hgrowth 0).1 (by positivity)))
  apply scalarCappedTransform_memLp_bound_of_bilinear m (ν.restrict (ball a R)) e ε hε f
    (Real.toNNReal (‖e‖ * ((D : ℝ) + C * 2 ^ m)))
  intro g
  rw [Real.coe_toNNReal _ hnonneg]
  exact compact_limit_capped_bilinear_L2_bound m hm C μ ν hgrowth hweak D hB
    a R hboundary hmass e ε hε f g

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_WeakL2Subsequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weak subsequences of bounded L² sequences

A bounded sequence in a separable Hilbert space admits a weakly convergent
subsequence whose limit obeys the same norm bound. For real L² functions,
the Hilbert-space pairings become integrals against arbitrary L² tests.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem bounded_hilbert_sequence_weak_subsequence {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (B : ℝ) (hB : ∀ j, ‖u j‖ ≤ B) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ v : H, ‖v‖ ≤ B ∧
      ∀ w : H, Tendsto (fun j => inner ℝ (u (ρ j)) w) atTop (𝓝 (inner ℝ v w)) := by
  let F : ℕ → WeakDual ℝ H := fun j =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (u j))
  have hin : ∀ j, F j ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ H) B := by
    intro j
    rw [mem_preimage, mem_closedBall, dist_zero_right]
    change ‖InnerProductSpace.toDual ℝ H (u j)‖ ≤ B
    rw [(InnerProductSpace.toDual ℝ H).norm_map]
    exact hB j
  obtain ⟨T, hT, ρ, hρ, hlim⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) B) hin
  let v := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual T)
  refine ⟨ρ, hρ, v, ?_, ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual T)‖ ≤ B
    rw [(InnerProductSpace.toDual ℝ H).symm.norm_map]
    rw [mem_preimage, mem_closedBall, dist_zero_right] at hT
    exact hT
  · intro w
    have h := ((WeakDual.eval_continuous w).tendsto T).comp hlim
    change Tendsto (fun j => inner ℝ (u (ρ j)) w) atTop (𝓝 (T w)) at h
    simpa only [v, InnerProductSpace.toDual_symm_apply] using! h

theorem bounded_L2_sequence_weak_subsequence {d : ℕ} (μ : Measure (Ambient d)) [SFinite μ]
    (f : ℕ → Ambient d → ℝ) (hf : ∀ j, MemLp (f j) 2 μ)
    (B : ℝ) (hB : ∀ j, ‖(hf j).toLp (f j)‖ ≤ B) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ v : Lp ℝ 2 μ, ‖v‖ ≤ B ∧
      ∀ g : Ambient d → ℝ, MemLp g 2 μ →
        Tendsto (fun j => ∫ x, f (ρ j) x * g x ∂μ) atTop (𝓝 (∫ x, v x * g x ∂μ)) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  obtain ⟨ρ, hρ, v, hv, hlim⟩ := bounded_hilbert_sequence_weak_subsequence
    (fun j => (hf j).toLp (f j)) B hB
  refine ⟨ρ, hρ, v, hv, ?_⟩
  intro g hg
  have hright : inner ℝ v (hg.toLp g) = ∫ x, v x * g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx, real_scalar_inner_mul]
  simpa only [toLp_inner_eq_integral, hright] using! hlim (hg.toLp g)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_LocalWeakCappedTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local weak limits of capped transforms

Uniform L² bounds yield weakly convergent subsequences of scalar capped transforms
at dyadic truncation scales, both for finite measures and for finite ball restrictions.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem exists_scalarCappedTransform_weak_subsequence {d : ℕ} (m : ℕ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (e : Ambient d) (A : ℝ≥0)
    (hB : ∀ ε : ℝ, 0 < ε →
      MemLp (scalarCappedTransform m ν e ε (fun _ => 1)) 2 ν ∧
        eLpNorm (scalarCappedTransform m ν e ε (fun _ => 1)) 2 ν ≤
          (A : ℝ≥0∞) * eLpNorm (fun _ : Ambient d => (1 : ℝ)) 2 ν) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      Tendsto (fun j => (1 / 2 : ℝ) ^ (ρ j)) atTop (𝓝 0) ∧
      ∃ v : Lp ℝ 2 ν, ‖v‖ ≤ (A : ℝ) * Real.sqrt (ν.real univ) ∧
        ∀ g : Ambient d → ℝ, MemLp g 2 ν →
          Tendsto (fun j => ∫ x, scalarCappedTransform m ν e ((1 / 2 : ℝ) ^ (ρ j))
            (fun _ => 1) x * g x ∂ν) atTop (𝓝 (∫ x, v x * g x ∂ν)) := by
  let F := fun j : ℕ => scalarCappedTransform m ν e ((1 / 2 : ℝ) ^ j) (fun _ => 1)
  have hF : ∀ j, MemLp (F j) 2 ν := fun j => (hB _ (by positivity)).1
  have hconst : MemLp (fun _ : Ambient d => (1 : ℝ)) 2 ν := memLp_const 1
  have hc := toLp_norm_eq_sqrt_integral ν (fun _ : Ambient d => (1 : ℝ)) hconst
  simp only [Lp.norm_toLp, one_pow, integral_const, smul_eq_mul, mul_one] at hc
  have hnorm (j : ℕ) : ‖(hF j).toLp (F j)‖ ≤ (A : ℝ) * Real.sqrt (ν.real univ) := by
    have hfin : (A : ℝ≥0∞) * eLpNorm (fun _ : Ambient d => (1 : ℝ)) 2 ν ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top hconst.eLpNorm_ne_top
    have h := ENNReal.toReal_mono hfin (hB ((1 / 2 : ℝ) ^ j) (by positivity)).2
    simpa only [Lp.norm_toLp, ENNReal.toReal_mul, ENNReal.coe_toReal, hc] using! h
  obtain ⟨ρ, hρ, v, hv, hlim⟩ := bounded_L2_sequence_weak_subsequence ν F hF
    ((A : ℝ) * Real.sqrt (ν.real univ)) hnorm
  refine ⟨ρ, hρ, ?_, v, hv, hlim⟩
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp hρ.tendsto_atTop

theorem exists_local_weak_transform_of_source_L2 {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth m C (μ j)) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j) →
      MemLp (truncated m (μ j) ε f) 2 (μ j) ∧
        eLpNorm (truncated m (μ j) ε f) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm f 2 (μ j))
    (a : Ambient d) (R : ℝ)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0) (e : Ambient d) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      Tendsto (fun j => (1 / 2 : ℝ) ^ (ρ j)) atTop (𝓝 0) ∧
      ∃ v : Lp ℝ 2 (ν.restrict (ball a R)),
        ‖v‖ ≤ (Real.toNNReal (‖e‖ * ((D : ℝ) + C * 2 ^ m)) : ℝ) *
          Real.sqrt (ν.real (ball a R)) ∧
        ∀ g : Ambient d → ℝ, MemLp g 2 (ν.restrict (ball a R)) →
          Tendsto (fun j => ∫ x in ball a R,
            scalarCappedTransform m (ν.restrict (ball a R)) e ((1 / 2 : ℝ) ^ (ρ j))
              (fun _ => 1) x * g x ∂ν) atTop (𝓝 (∫ x in ball a R, v x * g x ∂ν)) := by
  have hcompact : IsCompact (closure (ball a R)) :=
    (isCompact_closedBall a R).of_isClosed_subset isClosed_closure
      (closure_minimal ball_subset_closedBall isClosed_closedBall)
  let := relativelyCompact_restrict_finite ν (ball a R) hcompact
  have h := exists_scalarCappedTransform_weak_subsequence m (ν.restrict (ball a R)) e
    (Real.toNNReal (‖e‖ * ((D : ℝ) + C * 2 ^ m))) (fun ε hε =>
      compact_limit_scalarCappedTransform_L2_bound m hm C μ ν hgrowth hweak D hB
        a R hboundary hmass e ε hε (BoundedContinuousFunction.const (Ambient d) 1))
  simpa only [Measure.real, Measure.restrict_apply_univ] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedPairingSymmetrization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Function

theorem scalarCappedRieszKernel_swap {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ)
    (q : Ambient d × Ambient d) :
    scalarCappedRieszKernel m e ε q.swap = -scalarCappedRieszKernel m e ε q := by
  have hcap : cappedInverseDistancePow (m + 1) ε q.swap = cappedInverseDistancePow (m + 1) ε q := by
    simp only [cappedInverseDistancePow, Prod.fst_swap, Prod.snd_swap, dist_comm q.2 q.1]
  unfold scalarCappedRieszKernel cappedRieszKernel
  rw [hcap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [← neg_sub q.1 q.2, smul_neg, inner_neg_right]

theorem cappedRieszInterior_eq_scalar_cap {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ)
    (φ : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    cappedRieszInterior m ε e φ q = scalarCappedRieszKernel m e ε q * (φ q.1 - φ q.2) := by
  unfold cappedRieszInterior scalarCappedRieszKernel cappedRieszKernel
  rw [real_inner_smul_right]
  ring

theorem finite_capped_pairing_symmetrization {d : ℕ} (m : ℕ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (φ : Ambient d → ℝ) (hφm : Measurable φ) (hφ : Integrable φ ν) :
    (∫ x, scalarCappedTransform m ν e ε (fun _ => 1) x * φ x ∂ν) =
      (1 / 2 : ℝ) * (∫ q, cappedRieszInterior m ε e φ q ∂ν.prod ν) := by
  let F := fun q : Ambient d × Ambient d => φ q.1 * scalarCappedRieszKernel m e ε q
  have hF : Integrable F (ν.prod ν) := by
    simpa only [mul_one] using! bounded_kernel_bilinear_integrable ν (scalarCappedRieszKernel m e ε)
      (scalarCappedRieszKernel_continuous m e ε hε).measurable (‖e‖ * (ε ^ m)⁻¹)
      (scalarCappedRieszKernel_bound m e ε hε) φ (fun _ => 1) hφm measurable_const hφ (integrable_const 1)
  have heq : cappedRieszInterior m ε e φ = fun q => F q + F q.swap := by
    funext q
    rw [cappedRieszInterior_eq_scalar_cap]
    dsimp only [F]
    rw [scalarCappedRieszKernel_swap]
    dsimp only [Prod.swap]
    ring
  have hsum : (∫ q, cappedRieszInterior m ε e φ q ∂ν.prod ν) = 2 * (∫ q, F q ∂ν.prod ν) := by
    rw [heq]
    change (∫ q, F q + (F ∘ Prod.swap) q ∂ν.prod ν) = 2 * (∫ q, F q ∂ν.prod ν)
    rw [integral_add hF hF.swap]
    simp only [Function.comp_def, integral_prod_swap]
    ring
  have hpair : (∫ q, F q ∂ν.prod ν) =
      ∫ x, scalarCappedTransform m ν e ε (fun _ => 1) x * φ x ∂ν := by
    have h := capped_bilinear_eq_scalarCappedTransform m ν e ε hε (fun _ => 1) φ
      measurable_const hφm (integrable_const 1) hφ
    simpa only [mul_one, mul_comm (φ _) (scalarCappedTransform m ν e ε (fun _ => 1) _)] using! h
  rw [hsum, hpair]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RieszInteriorCapError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrable errors for capped interior Riesz kernels

The capped interior integrand is integrable for finite measures and bounded
continuous tests. For Lipschitz tests, a near-diagonal weight dominates its
difference from the original integrand, giving integrability of the latter
and quantitative control of the capping error.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal

theorem cappedRieszInterior_integrable {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ]
    (e : Ambient d) (φ : Ambient d → ℝ) (hφ : Continuous φ)
    (B : ℝ≥0) (hB : ∀ x, |φ x| ≤ (B : ℝ)) :
    Integrable (cappedRieszInterior m ε e φ) (μ.prod μ) := by
  apply Integrable.of_bound
    (cappedRieszInterior_continuous m ε hε e φ hφ).measurable.aestronglyMeasurable
    ((2 * (B : ℝ) * ‖e‖) * (ε ^ m)⁻¹)
  exact Eventually.of_forall fun q => by
    simpa only [Real.norm_eq_abs] using! cappedRieszInterior_bound m ε hε e φ B hB q

theorem rieszInterior_integrable_and_cap_error {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L B : ℝ≥0)
    (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    Integrable (rieszInteriorIntegrand (p + 1) e φ) (μ.prod μ) ∧
      |(∫ q, rieszInteriorIntegrand (p + 1) e φ q ∂μ.prod μ) -
        ∫ q, cappedRieszInterior (p + 1) ε e φ q ∂μ.prod μ| ≤
          (‖e‖ * (L : ℝ)) * (μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * ε))) := by
  let F := rieszInteriorIntegrand (p + 1) e φ
  let G := cappedRieszInterior (p + 1) ε e φ
  have hG : Integrable G (μ.prod μ) :=
    cappedRieszInterior_integrable (p + 1) ε hε μ e φ hφ.continuous B hB
  have hFm : Measurable F := by
    have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
    have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
    have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
    have hφm := hφ.continuous.measurable
    dsimp only [F]
    unfold rieszInteriorIntegrand kernel
    fun_prop
  have hdom := (nearPairWeight_integrable p C μ hg ε hε).const_mul (‖e‖ * (L : ℝ))
  have herr : Integrable (fun q => F q - G q) (μ.prod μ) := by
    apply hdom.mono' (hFm.aestronglyMeasurable.sub hG.aestronglyMeasurable)
    exact Eventually.of_forall fun q => by
      simpa only [Real.norm_eq_abs] using! rieszInterior_cap_error_pointwise p ε e φ L hφ q
  have hF : Integrable F (μ.prod μ) := by
    have heq : F = fun q => (F q - G q) + G q := by funext q; ring
    rw [heq]
    exact herr.add hG
  refine ⟨hF, ?_⟩
  change |(∫ q, F q ∂μ.prod μ) - ∫ q, G q ∂μ.prod μ| ≤ _
  rw [← integral_sub hF hG]
  calc
    _ ≤ ∫ q, |F q - G q| ∂μ.prod μ := abs_integral_le_integral_abs
    _ ≤ ∫ q, (‖e‖ * (L : ℝ)) * nearPairWeight p ε q ∂μ.prod μ :=
      integral_mono_ae herr.abs hdom
        (Eventually.of_forall fun q => rieszInterior_cap_error_pointwise p ε e φ L hφ q)
    _ = (‖e‖ * (L : ℝ)) * ∫ q, nearPairWeight p ε q ∂μ.prod μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (nearPairWeight_integral_bound p C μ hg ε hε)
      (mul_nonneg (norm_nonneg _) L.coe_nonneg)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_WeakTransformInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal

theorem finite_capped_interior_tendsto {d : ℕ} (p : ℕ) (C : ℝ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (hg : GlobalUpperGrowth (p + 1) C ν)
    (e : Ambient d) (φ : Ambient d → ℝ) (L B : ℝ≥0)
    (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ))
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => ∫ q, cappedRieszInterior (p + 1) (ε j) e φ q ∂ν.prod ν) atTop
      (𝓝 (∫ q, rieszInteriorIntegrand (p + 1) e φ q ∂ν.prod ν)) := by
  let A := (‖e‖ * (L : ℝ)) * (ν.real Set.univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p)))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_)
    (show Tendsto (fun j => A * ε j) atTop (𝓝 0) by
      simpa only [mul_zero] using! hεlim.const_mul A)
  rw [Real.norm_eq_abs, abs_sub_comm]
  have h := (rieszInterior_integrable_and_cap_error p C ν hg e φ L B hφ hB (ε j) (hε j)).2
  calc
    _ ≤ (‖e‖ * (L : ℝ)) * (ν.real Set.univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * ε j))) := h
    _ = _ := by dsimp only [A] <;> ring

theorem weak_transform_represents_interior {d : ℕ} (p : ℕ) (C : ℝ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (hg : GlobalUpperGrowth (p + 1) C ν)
    (e : Ambient d) (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (v : Lp ℝ 2 ν)
    (hweak : ∀ g : Ambient d → ℝ, MemLp g 2 ν →
      Tendsto (fun j => ∫ x, scalarCappedTransform (p + 1) ν e (ε j) (fun _ => 1) x * g x ∂ν)
        atTop (𝓝 (∫ x, v x * g x ∂ν)))
    (φ : Ambient d → ℝ) (L B : ℝ≥0) (hφ : LipschitzWith L φ)
    (hB : ∀ x, |φ x| ≤ (B : ℝ)) :
    (∫ x, v x * φ x ∂ν) = (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e φ q ∂ν.prod ν) := by
  have hφ₂ : MemLp φ 2 ν :=
    MemLp.of_bound hφ.continuous.aestronglyMeasurable B (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using! hB x)
  have hφ₁ := hφ₂.integrable (by norm_num)
  have heq (j : ℕ) := finite_capped_pairing_symmetrization (p + 1) ν e (ε j) (hε j)
    φ hφ.continuous.measurable hφ₁
  have hlim : Tendsto (fun j => ∫ x, scalarCappedTransform (p + 1) ν e (ε j) (fun _ => 1) x * φ x ∂ν)
      atTop (𝓝 ((1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e φ q ∂ν.prod ν))) := by
    simp only [heq]
    exact (finite_capped_interior_tendsto p C ν hg e φ L B hφ hB ε hε hεlim).const_mul (1 / 2 : ℝ)
  exact tendsto_nhds_unique (hweak φ hφ₂) hlim

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_LocalInteriorRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local L² representatives of interior pairings

Weak limits of capped transforms on ball restrictions represent the interior Riesz
pairing. The resulting representative retains the quantitative L² bound inherited
from the approximating measures.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_local_L2_interior_representative {d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
    (hgν : GlobalUpperGrowth (p + 1) G ν) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε f) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε f) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm f 2 (μ j))
    (a : Ambient d) (R : ℝ)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0) (e : Ambient d) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      Tendsto (fun j => (1 / 2 : ℝ) ^ (ρ j)) atTop (𝓝 0) ∧
      ∃ v : Lp ℝ 2 (ν.restrict (ball a R)),
        ‖v‖ ≤ (Real.toNNReal (‖e‖ * ((D : ℝ) + C * 2 ^ (p + 1))) : ℝ) *
          Real.sqrt (ν.real (ball a R)) ∧
        (∀ g : Ambient d → ℝ, MemLp g 2 (ν.restrict (ball a R)) →
          Tendsto (fun j => ∫ x in ball a R,
            scalarCappedTransform (p + 1) (ν.restrict (ball a R)) e ((1 / 2 : ℝ) ^ (ρ j))
              (fun _ => 1) x * g x ∂ν) atTop (𝓝 (∫ x in ball a R, v x * g x ∂ν))) ∧
        ∀ (φ : Ambient d → ℝ) (L B : ℝ≥0), LipschitzWith L φ →
          (∀ x, |φ x| ≤ (B : ℝ)) →
          (∫ x in ball a R, v x * φ x ∂ν) = (1 / 2 : ℝ) *
            (∫ q, rieszInteriorIntegrand (p + 1) e φ q
              ∂(ν.restrict (ball a R)).prod (ν.restrict (ball a R))) := by
  have hcompact : IsCompact (closure (ball a R)) :=
    (isCompact_closedBall a R).of_isClosed_subset isClosed_closure
      (closure_minimal ball_subset_closedBall isClosed_closedBall)
  let := relativelyCompact_restrict_finite ν (ball a R) hcompact
  obtain ⟨ρ, hρ, hεlim, v, hv, hlim⟩ := exists_local_weak_transform_of_source_L2
    (p + 1) (by omega) C μ ν hgrowth hweak D hB a R hboundary hmass e
  refine ⟨ρ, hρ, hεlim, v, hv, hlim, ?_⟩
  intro φ L B hφ hBφ
  exact weak_transform_represents_interior p G (ν.restrict (ball a R))
    (globalGrowth_restrict (p + 1) G ν hgν (ball a R)) e
    (fun j => (1 / 2 : ℝ) ^ (ρ j)) (fun _ => by positivity) hεlim v hlim φ L B hφ hBφ

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_LocalTestConstancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter Function
open scoped NNReal ContDiff

theorem integrable_mul_compact_test_of_integrableOn {d : ℕ}
    (μ : Measure (Ambient d)) (U : Set (Ambient d))
    (f g : Ambient d → ℝ) (hf : IntegrableOn f U μ)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : support g ⊆ U) :
    Integrable (fun x => f x * g x) μ := by
  obtain ⟨B, hB⟩ := hgc.exists_bound_of_continuous hg
  have hi : IntegrableOn (fun x => f x * g x) U μ :=
    hf.mul_bdd hg.aestronglyMeasurable (Eventually.of_forall hB)
  apply hi.integrable_of_forall_notMem_eq_zero
  intro x hx
  have hz : g x = 0 := by
    by_contra hn
    exact hx (hgs hn)
  rw [hz, mul_zero]

theorem local_mean_zero_test_annihilator_constant {d : ℕ}
    (μ : Measure (Ambient d)) (U : Set (Ambient d)) (hU : IsOpen U)
    [IsFiniteMeasure (μ.restrict U)]
    (f : Ambient d → ℝ) (hf : IntegrableOn f U μ)
    (η : Ambient d → ℝ) (Kη : ℝ≥0) (hη : LipschitzWith Kη η)
    (hηc : HasCompactSupport η) (hηs : support η ⊆ U) (hηmean : (∫ x, η x ∂μ) = 1)
    (hzero : ∀ (φ : Ambient d → ℝ) (K : ℝ≥0), LipschitzWith K φ →
      HasCompactSupport φ → support φ ⊆ U → (∫ x, φ x ∂μ) = 0 →
        (∫ x, f x * φ x ∂μ) = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂μ, x ∈ U → f x = c := by
  have hηI : Integrable η μ := by
    simpa only [one_mul] using! integrable_mul_compact_test_of_integrableOn μ U
      (fun _ => 1) η (integrable_const 1) hη.continuous hηc hηs
  have hfη := integrable_mul_compact_test_of_integrableOn μ U f η hf hη.continuous hηc hηs
  let c := ∫ x, f x * η x ∂μ
  refine ⟨c, ?_⟩
  have hfc : LocallyIntegrableOn (fun x => f x - c) U μ :=
    (hf.sub (integrable_const c)).locallyIntegrableOn
  have ha := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfc ?_
  · filter_upwards [ha] with x hx hxU
    exact sub_eq_zero.mp (hx hxU)
  intro g hgsmooth hgc hgs
  have hgsU : support g ⊆ U := subset_trans (subset_tsupport g) hgs
  have hgI : Integrable g μ := by
    simpa only [one_mul] using! integrable_mul_compact_test_of_integrableOn μ U
      (fun _ => 1) g (integrable_const 1) hgsmooth.continuous hgc hgsU
  have hfg := integrable_mul_compact_test_of_integrableOn μ U f g hf hgsmooth.continuous hgc hgsU
  obtain ⟨Kg, hKg⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hgsmooth (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let M := ∫ x, g x ∂μ
  let φ := fun x => g x - M * η x
  have hφ : LipschitzWith (Kg + ‖M‖₊ * Kη) φ := hKg.sub (lipschitz_const_mul_real hη M)
  have hφc : HasCompactSupport φ := hgc.sub hηc.mul_left
  have hφs : support φ ⊆ U := by
    intro x hx
    by_contra hn
    have hg0 : g x = 0 := by
      by_contra hz
      exact hn (hgsU hz)
    have hη0 : η x = 0 := by
      by_contra hz
      exact hn (hηs hz)
    exact hx (by simp only [φ, hg0, hη0, mul_zero, sub_zero])
  have hφmean : (∫ x, φ x ∂μ) = 0 := by
    change (∫ x, g x - M * η x ∂μ) = 0
    rw [integral_sub hgI (hηI.const_mul M), integral_const_mul, hηmean, mul_one]
    exact sub_self _
  have hz := hzero φ _ hφ hφc hφs hφmean
  have heq : (fun x => f x * φ x) = fun x => f x * g x - M * (f x * η x) := by
    funext x
    dsimp only [φ]
    ring
  rw [heq, integral_sub hfg (hfη.const_mul M), integral_const_mul] at hz
  have hfgmean : (∫ x, f x * g x ∂μ) = M * c := sub_eq_zero.mp hz
  change (∫ x, g x * (f x - c) ∂μ) = 0
  calc
    _ = ∫ x, f x * g x - c * g x ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = (∫ x, f x * g x ∂μ) - c * ∫ x, g x ∂μ := by
      rw [integral_sub hfg (hgI.const_mul c), integral_const_mul]
    _ = 0 := by rw [hfgmean]; dsimp only [M] <;> ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_DensityCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

theorem bounded_div_density_memLp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f g : α → ℝ)
    (hf : Measurable f) (hg : Measurable g) (c B : ℝ) (hc : 0 < c)
    (hlower : ∀ x, c ≤ f x) (hbound : ∀ x, |g x| ≤ B) :
    MemLp (fun x => g x / f x) 2 μ := by
  apply MemLp.of_bound (hg.div hf).aestronglyMeasurable (B / c)
  apply Eventually.of_forall
  intro x
  rw [Pi.div_apply, Real.norm_eq_abs, abs_div, abs_of_pos (hc.trans_le (hlower x))]
  exact (div_le_div_of_nonneg_left (abs_nonneg _) hc (hlower x)).trans
    (div_le_div_of_nonneg_right (hbound x) hc.le)

theorem integral_mul_div_density {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 < f x)
    (F g : α → ℝ) :
    (∫ x, F x * (g x / f x) ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) =
      ∫ x, F x * g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [ENNReal.toReal_ofReal (hpos x).le, smul_eq_mul]
  field_simp [(hpos x).ne']

theorem setIntegral_mul_div_density {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 < f x)
    (U : Set α) (hU : MeasurableSet U) (F g : α → ℝ) :
    (∫ x in U, F x * (g x / f x) ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) =
      ∫ x in U, F x * g x ∂μ := by
  rw [restrict_withDensity hU]
  exact integral_mul_div_density (μ.restrict U) f hf hpos F g

theorem positive_density_absolutelyContinuous {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 < f x) :
    μ ≪ μ.withDensity (fun x => ENNReal.ofReal (f x)) :=
  withDensity_absolutelyContinuous' hf.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (hpos x)).ne')

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_DensityRieszTransforms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter

theorem scalarCappedTransform_withDensity {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 < f x)
    (U : Set (Ambient d)) (hU : MeasurableSet U) (e : Ambient d) (ε : ℝ) (x : Ambient d) :
    scalarCappedTransform m ((μ.withDensity (fun y => ENNReal.ofReal (f y))).restrict U)
      e ε (fun _ => 1) x = scalarCappedTransform m (μ.restrict U) e ε f x := by
  unfold scalarCappedTransform
  rw [restrict_withDensity hU, integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [ENNReal.toReal_ofReal (hpos y).le, smul_eq_mul, one_mul]

theorem scalarFarRieszTransform_withDensity {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 < f x)
    (e a : Ambient d) (R : ℝ) (x : Ambient d) :
    scalarFarRieszTransform m (μ.withDensity (fun y => ENNReal.ofReal (f y))) e a R x =
      ∫ y in closedExterior a R, f y * inner ℝ e (kernel m x y - kernel m a y) ∂μ := by
  unfold scalarFarRieszTransform
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ (closedExterior_measurable a R)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [ENNReal.toReal_ofReal (hpos y).le, smul_eq_mul]

theorem scalarFarRieszTransform_mul_test_integrable {d : ℕ} (m : ℕ) (C : ℝ)
    (ρ : Measure (Ambient d)) [SFinite ρ] (hgrowth : GlobalUpperGrowth m C ρ)
    (σ : Measure (Ambient d)) (e a : Ambient d) (H R : ℝ)
    (hR : 0 < R) (hHR : 2 * H ≤ R)
    (g : Ambient d → ℝ) (hg : Measurable g) (hgI : Integrable g σ)
    (hsupport : ∀ x, g x ≠ 0 → dist x a ≤ H) :
    Integrable (fun x => scalarFarRieszTransform m ρ e a R x * g x) σ := by
  let B := ((2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * H)) *
    (2 * (C * 2 ^ m / R))
  have hC := hgrowth.1
  apply (hgI.abs.const_mul B).mono'
    ((scalarFarRieszTransform_measurable m ρ e a R).mul hg).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  by_cases hz : g x = 0
  · simp only [Pi.mul_apply, hz, mul_zero, norm_zero, abs_zero, le_refl]
  have hx := hsupport x hz
  have hF : |scalarFarRieszTransform m ρ e a R x| ≤ B := by
    apply (scalarFarRieszTransform_integrable_and_bound m C ρ hgrowth e a x R hR (by linarith)).2.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (norm_nonneg _)) (by positivity))
      (by positivity)
  rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hF (abs_nonneg _)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_DensityWeakPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem weak_L2_pairings_cancel_density {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Measurable f)
    (U : Set α) (hU : MeasurableSet U)
    [IsFiniteMeasure ((μ.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)]
    (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
    (T : ℕ → α → ℝ) (v : α → ℝ)
    (hweak : ∀ g : α → ℝ, MemLp g 2 ((μ.withDensity (fun x => ENNReal.ofReal (f x))).restrict U) →
      Tendsto (fun j => ∫ x in U, T j x * g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) atTop
        (𝓝 (∫ x in U, v x * g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x)))))
    (g : α → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ x, |g x| ≤ B) :
    Tendsto (fun j => ∫ x in U, T j x * g x ∂μ) atTop (𝓝 (∫ x in U, v x * g x ∂μ)) := by
  have hpos : ∀ x, 0 < f x := fun x => hc.trans_le (hlower x)
  have hdiv := bounded_div_density_memLp
    ((μ.withDensity (fun x => ENNReal.ofReal (f x))).restrict U) f g hf hg c B hc hlower hB
  have h := hweak (fun x => g x / f x) hdiv
  simpa only [setIntegral_mul_div_density μ f hf hpos U hU] using! h

theorem weak_L2_pairings_cancel_density_add_correction {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Measurable f)
    (U : Set α) (hU : MeasurableSet U)
    [IsFiniteMeasure ((μ.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)]
    (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
    (T : ℕ → α → ℝ) (v : α → ℝ)
    (hweak : ∀ g : α → ℝ, MemLp g 2 ((μ.withDensity (fun x => ENNReal.ofReal (f x))).restrict U) →
      Tendsto (fun j => ∫ x in U, T j x * g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) atTop
        (𝓝 (∫ x in U, v x * g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x)))))
    (F : α → ℝ) (V : Set α) (b : ℝ)
    (hconstant : ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (f x)), x ∈ V → v x + F x = b)
    (g : α → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ x, |g x| ≤ B)
    (hgs : ∀ x, g x ≠ 0 → x ∈ V) (hgI : IntegrableOn g U μ)
    (hFI : IntegrableOn (fun x => F x * g x) U μ) :
    Tendsto (fun j => (∫ x in U, T j x * g x ∂μ) + ∫ x in U, F x * g x ∂μ)
      atTop (𝓝 (b * ∫ x in U, g x ∂μ)) := by
  have hlim := weak_L2_pairings_cancel_density μ f hf U hU c hc hlower T v hweak g hg B hB
  have hbase : ∀ᵐ x ∂μ, x ∈ V → v x + F x = b :=
    (positive_density_absolutelyContinuous μ f hf (fun x => hc.trans_le (hlower x))).ae_le hconstant
  have heq : (fun x => v x * g x) =ᵐ[μ.restrict U] (fun x => b * g x - F x * g x) := by
    filter_upwards [ae_restrict_of_ae hbase] with x hx
    by_cases hz : g x = 0
    · simp only [hz, mul_zero, sub_zero]
    · rw [← hx (hgs x hz)]
      ring
  have hvalue : (∫ x in U, v x * g x ∂μ) + (∫ x in U, F x * g x ∂μ) =
      b * ∫ x in U, g x ∂μ := by
    rw [integral_congr_ae heq, integral_sub (hgI.const_mul b) hFI, integral_const_mul]
    ring
  simpa only [hvalue] using! hlim.add_const (∫ x in U, F x * g x ∂μ)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_UnweightedCappedEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing density weights from capped equations

A positive lower bound on a measurable density allows weak pairings for its
weighted measure to be rewritten against volume. The capped local transform
and the integrable far-field correction then converge together to the constant
pairing on compactly supported tests.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem unweighted_capped_pairing_tendsto_constant {n : ℕ} (m : ℕ) (G : ℝ)
    (f : Ambient n → ℝ) (hf : Measurable f) (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
    (hgrowth : GlobalUpperGrowth m G ((volume : Measure (Ambient n)).withDensity
      (fun x => ENNReal.ofReal (f x))))
    (e a : Ambient n) (H R b : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (ε : ℕ → ℝ) (v : Ambient n → ℝ)
    (hweak : ∀ g : Ambient n → ℝ,
      MemLp g 2 (((volume : Measure (Ambient n)).withDensity (fun x => ENNReal.ofReal (f x))).restrict (ball a R)) →
      Tendsto (fun j => ∫ x in ball a R,
        scalarCappedTransform m
          (((volume : Measure (Ambient n)).withDensity (fun y => ENNReal.ofReal (f y))).restrict (ball a R))
          e (ε j) (fun _ => 1) x * g x
            ∂(volume : Measure (Ambient n)).withDensity (fun y => ENNReal.ofReal (f y))) atTop
        (𝓝 (∫ x in ball a R, v x * g x
          ∂(volume : Measure (Ambient n)).withDensity (fun y => ENNReal.ofReal (f y)))))
    (hconstant : ∀ᵐ x ∂(volume : Measure (Ambient n)).withDensity (fun y => ENNReal.ofReal (f y)),
      x ∈ ball a H → v x + scalarFarRieszTransform m
        ((volume : Measure (Ambient n)).withDensity (fun y => ENNReal.ofReal (f y))) e a R x = b)
    (g : Ambient n → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ x, |g x| ≤ B)
    (hgI : Integrable g volume) (hgs : ∀ x, g x ≠ 0 → x ∈ ball a H) :
    Tendsto (fun j =>
      (∫ x, scalarCappedTransform m (volume.restrict (ball a R)) e (ε j) f x * g x) +
        ∫ x, (∫ y in closedExterior a R, f y * inner ℝ e (kernel m x y - kernel m a y)) * g x)
      atTop (𝓝 (b * ∫ x, g x)) := by
  let ρ : Measure (Ambient n) := volume.withDensity (fun x => ENNReal.ofReal (f x))
  let := finiteMeasure_restrict_ball_of_globalGrowth m G ρ hgrowth a R hR
  have hpos : ∀ x, 0 < f x := fun x => hc.trans_le (hlower x)
  have hFI := scalarFarRieszTransform_mul_test_integrable m G ρ hgrowth volume e a H R
    hR hHR g hg hgI (fun x hx => (hgs x hx).le)
  have h := weak_L2_pairings_cancel_density_add_correction volume f hf (ball a R)
    measurableSet_ball c hc hlower
    (fun j => scalarCappedTransform m (ρ.restrict (ball a R)) e (ε j) (fun _ => 1)) v hweak
    (scalarFarRieszTransform m ρ e a R) (ball a H) b hconstant g hg B hB hgs hgI.restrict hFI.restrict
  have hgzero : ∀ x ∉ ball a R, g x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hgs x hn).trans (by linarith : H < R))
  have hlocal (F : Ambient n → ℝ) : (∫ x in ball a R, F x * g x) = ∫ x, F x * g x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hgzero x hx, mul_zero]
  have hmean : (∫ x in ball a R, g x) = ∫ x, g x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hgzero
  simpa only [ρ, scalarCappedTransform_withDensity m volume f hf hpos (ball a R) measurableSet_ball,
    scalarFarRieszTransform_withDensity m volume f hf hpos, hlocal, hmean] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_IsometricWeakTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology Function

theorem linearIsometry_ball_integral {n d : ℕ}
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n))
    (a : Ambient n) (R : ℝ) (F : Ambient d → ℝ) :
    (∫ x in ball (L a) R, F x ∂μ.map L) = ∫ x in ball a R, F (L x) ∂μ := by
  rw [linearIsometry_restrict_ball, L.isometry.isClosedEmbedding.measurableEmbedding.integral_map]

theorem linearIsometry_local_weak_L2_pairings {n d : ℕ}
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n))
    (a : Ambient n) (R : ℝ) (T : ℕ → Ambient d → ℝ) (v : Ambient d → ℝ)
    (hv : MemLp v 2 ((μ.map L).restrict (ball (L a) R)))
    (hweak : ∀ g : Ambient d → ℝ, MemLp g 2 ((μ.map L).restrict (ball (L a) R)) →
      Tendsto (fun j => ∫ x in ball (L a) R, T j x * g x ∂μ.map L) atTop
        (𝓝 (∫ x in ball (L a) R, v x * g x ∂μ.map L))) :
    MemLp (fun x => v (L x)) 2 (μ.restrict (ball a R)) ∧
      ∀ g : Ambient n → ℝ, MemLp g 2 (μ.restrict (ball a R)) →
        Tendsto (fun j => ∫ x in ball a R, T j (L x) * g x ∂μ) atTop
          (𝓝 (∫ x in ball a R, v (L x) * g x ∂μ)) := by
  have hmap := linearIsometry_restrict_ball L μ a R
  have hv' : MemLp v 2 ((μ.restrict (ball a R)).map L) := by rwa [← hmap]
  refine ⟨?_, ?_⟩
  · exact L.isometry.isClosedEmbedding.measurableEmbedding.memLp_map_measure_iff.mp hv'
  intro g hg
  let Φ := fun x : Ambient d => g (L.toContinuousLinearMap.adjoint x)
  have hleft (x : Ambient n) : L.toContinuousLinearMap.adjoint (L x) = x :=
    DFunLike.congr_fun L.adjoint_comp_self x
  have hcomp : Φ ∘ L = g := by
    funext x
    simp only [Φ, Function.comp_apply, hleft]
  have hΦ : MemLp Φ 2 ((μ.map L).restrict (ball (L a) R)) := by
    rw [hmap, L.isometry.isClosedEmbedding.measurableEmbedding.memLp_map_measure_iff, hcomp]
    exact hg
  have hpair (F : Ambient d → ℝ) : (∫ x in ball (L a) R, F x * Φ x ∂μ.map L) =
      ∫ x in ball a R, F (L x) * g x ∂μ := by
    rw [linearIsometry_ball_integral]
    simp only [Φ, hleft]
  simpa only [hpair] using! hweak Φ hΦ

theorem local_capped_weak_L2_pairings_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n))
    (e a : Ambient n) (R : ℝ) (ε : ℕ → ℝ) (v : Ambient d → ℝ)
    (hv : MemLp v 2 ((μ.map L).restrict (ball (L a) R)))
    (hweak : ∀ g : Ambient d → ℝ, MemLp g 2 ((μ.map L).restrict (ball (L a) R)) →
      Tendsto (fun j => ∫ x in ball (L a) R,
        scalarCappedTransform m ((μ.map L).restrict (ball (L a) R)) (L e) (ε j) (fun _ => 1) x * g x
          ∂μ.map L) atTop (𝓝 (∫ x in ball (L a) R, v x * g x ∂μ.map L))) :
    MemLp (fun x => v (L x)) 2 (μ.restrict (ball a R)) ∧
      ∀ g : Ambient n → ℝ, MemLp g 2 (μ.restrict (ball a R)) →
        Tendsto (fun j => ∫ x in ball a R,
          scalarCappedTransform m (μ.restrict (ball a R)) e (ε j) (fun _ => 1) x * g x ∂μ) atTop
          (𝓝 (∫ x in ball a R, v (L x) * g x ∂μ)) := by
  have h := linearIsometry_local_weak_L2_pairings L μ a R
    (fun j => scalarCappedTransform m ((μ.map L).restrict (ball (L a) R)) (L e) (ε j) (fun _ => 1))
    v hv hweak
  simpa only [scalarCappedTransform_ball_linearIsometry] using! h

theorem local_transform_constancy_linearIsometry {n d : ℕ} (m : ℕ)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (μ : Measure (Ambient n))
    (e a : Ambient n) (H R b : ℝ) (v : Ambient d → ℝ)
    (hconstant : ∀ᵐ x ∂μ.map L, x ∈ ball (L a) H →
      v x + scalarFarRieszTransform m (μ.map L) (L e) (L a) R x = b) :
    ∀ᵐ x ∂μ, x ∈ ball a H → v (L x) + scalarFarRieszTransform m μ e a R x = b := by
  have h := ae_of_ae_map L.continuous.measurable.aemeasurable hconstant
  simpa only [mem_ball, L.dist_map, scalarFarRieszTransform_linearIsometry] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LocalRenormalizedRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local representatives of renormalized Riesz pairings

The far-field pairing is represented by the scalar far Riesz transform. Adding
this transform to a local interior representative gives the renormalized pairing
on supported Lipschitz tests and preserves local L² integrability.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem far_pairing_eq_scalarFarRieszTransform {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    IntegrableOn (fun x => scalarFarRieszTransform m μ e a R x * φ x) (ball a R) μ ∧
      (∫ q, rieszFarIntegrand m e φ a q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))) =
        ∫ x in ball a R, scalarFarRieszTransform m μ e a R x * φ x ∂μ := by
  have hi := rieszFarIntegrand_integrable_of_compact_lipschitz m C μ hg e φ L hφ
    a H R hH hR hHR hsupport
  have heq (x : Ambient d) : (∫ y in closedExterior a R, rieszFarIntegrand m e φ a (x, y) ∂μ) =
      scalarFarRieszTransform m μ e a R x * φ x := by
    simp only [rieszFarIntegrand, integral_const_mul, scalarFarRieszTransform, mul_comm]
  refine ⟨?_, ?_⟩
  · simpa only [heq] using! hi.integral_prod_left
  · rw [integral_prod _ hi]
    simp only [heq]

theorem local_renormalized_pairing_representation {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (e a : Ambient d) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (v : Lp ℝ 2 (μ.restrict (ball a R)))
    (hv : ∀ (φ : Ambient d → ℝ) (L B : ℝ≥0), LipschitzWith L φ →
      (∀ x, |φ x| ≤ (B : ℝ)) → (∫ x in ball a R, v x * φ x ∂μ) =
        (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e φ q
          ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R)))) :
    MemLp (fun x => v x + scalarFarRieszTransform (p + 1) μ e a R x) 2 (μ.restrict (ball a H)) ∧
      ∀ (φ : Ambient d → ℝ) (L B : ℝ≥0), LipschitzWith L φ →
        (∀ x, |φ x| ≤ (B : ℝ)) → (∀ x, φ x ≠ 0 → dist x a ≤ H) →
        rieszScalarPairing (p + 1) μ a R e φ =
          ∫ x, (v x + scalarFarRieszTransform (p + 1) μ e a R x) * φ x ∂μ := by
  have hsubset : ball a H ⊆ ball a R := ball_subset_ball (by linarith)
  have hvH : MemLp (fun x => v x) 2 (μ.restrict (ball a H)) :=
    MemLp.mono_measure (Measure.restrict_mono_set μ hsubset) (Lp.memLp v)
  refine ⟨hvH.add (scalarFarRieszTransform_memLp_inner_ball (p + 1) C μ hg e a H R hH hR hHR), ?_⟩
  intro φ L B hφ hB hs
  let := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
  have hφ₂ : MemLp φ 2 (μ.restrict (ball a R)) :=
    MemLp.of_bound hφ.continuous.aestronglyMeasurable B
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hB x)
  have hiv : IntegrableOn (fun x => v x * φ x) (ball a R) μ :=
    memLp_one_iff_integrable.mp (MeasureTheory.MemLp.mul (hφ := (Lp.memLp v)) (hf := hφ₂))
  obtain ⟨hif, hfar⟩ := far_pairing_eq_scalarFarRieszTransform (p + 1) C μ hg e φ L hφ
    a H R hH.le hR hHR hs
  calc
    _ = (∫ x in ball a R, v x * φ x ∂μ) +
        ∫ x in ball a R, scalarFarRieszTransform (p + 1) μ e a R x * φ x ∂μ := by
      unfold rieszScalarPairing
      dsimp only
      rw [← hv φ L B hφ hB, hfar]
    _ = ∫ x in ball a R, (v x + scalarFarRieszTransform (p + 1) μ e a R x) * φ x ∂μ := by
      rw [← integral_add hiv hif]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : φ x = 0 := by
        by_contra hn
        exact hx ((hs x hn).trans_lt (by linarith : H < R))
      rw [hz, mul_zero]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ScaledBallBumps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Scaled ball bumps give compactly supported Lipschitz cutoffs. A lower ball-mass bound
allows normalization to integral one with an explicit scale-dependent Lipschitz bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem scaledBallBump_bounds {d : ℕ} (a : Ambient d) (r : ℝ) (x : Ambient d) :
    0 ≤ scaledBallBump a r x ∧ scaledBallBump a r x ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem scaledBallBump_lipschitz {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    LipschitzWith (Real.toNNReal r⁻¹) (scaledBallBump a r) := by
  have h : LipschitzWith (Real.toNNReal r⁻¹)
      (fun x : Ambient d => r⁻¹ * dist x a) := by
    have heq : ‖r⁻¹‖₊ = Real.toNNReal r⁻¹ := by
      apply NNReal.coe_injective
      simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
        Real.coe_toNNReal r⁻¹ (inv_nonneg.mpr hr.le)]
    simpa only [mul_one, heq] using! lipschitz_const_mul_real (LipschitzWith.dist_left a) r⁻¹
  have hsub : LipschitzWith (Real.toNNReal r⁻¹)
      (fun x : Ambient d => 2 - r⁻¹ * dist x a) := by
    simpa only [zero_add] using! (LipschitzWith.const (2 : ℝ)).sub h
  exact (hsub.const_min 1).const_max 0

theorem scaledBallBump_eq_one {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (x : Ambient d) (hx : dist x a ≤ r) : scaledBallBump a r x = 1 := by
  have hb : r⁻¹ * dist x a ≤ 1 := by
    calc
      _ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hr.le)
      _ = 1 := inv_mul_cancel₀ hr.ne'
  simp only [scaledBallBump, min_eq_left (by linarith : (1 : ℝ) ≤ 2 - r⁻¹ * dist x a),
    max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem scaledBallBump_support_bound {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (x : Ambient d) (hx : scaledBallBump a r x ≠ 0) : dist x a ≤ 2 * r := by
  by_contra hn
  have hdist : 2 * r < dist x a := lt_of_not_ge hn
  have hb : 2 < r⁻¹ * dist x a := by
    calc
      (2 : ℝ) = r⁻¹ * (2 * r) := by field_simp
      _ < _ := mul_lt_mul_of_pos_left hdist (inv_pos.mpr hr)
  exact hx (max_eq_left ((min_le_right _ _).trans (by linarith : 2 - r⁻¹ * dist x a ≤ 0)))

theorem scaledBallBump_hasCompactSupport {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (scaledBallBump a r) := by
  apply HasCompactSupport.intro (isCompact_closedBall a (2 * r))
  intro x hx
  by_contra hn
  exact hx (scaledBallBump_support_bound a r hr x hn)

theorem scaledBallBump_integral_lower {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    μ.real (ball a r) ≤ ∫ x, scaledBallBump a r x ∂μ := by
  have hi := (scaledBallBump_lipschitz a r hr).continuous.integrable_of_hasCompactSupport
    (μ := μ) (scaledBallBump_hasCompactSupport a r hr)
  have hs : (∫ x in ball a r, scaledBallBump a r x ∂μ) = μ.real (ball a r) := by
    calc
      _ = ∫ _x in ball a r, (1 : ℝ) ∂μ := by
        apply setIntegral_congr_fun measurableSet_ball
        intro x hx
        exact scaledBallBump_eq_one a r hr x hx.le
      _ = _ := by simp only [setIntegral_const, smul_eq_mul, mul_one]
  rw [← hs]
  exact setIntegral_le_integral hi (Eventually.of_forall fun x => (scaledBallBump_bounds a r x).1)

theorem exists_normalized_ball_bump {d : ℕ} (n : ℕ) (C c : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ) (hc : 0 < c)
    (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (hmass : ENNReal.ofReal (c * r ^ n) ≤ μ (ball a r)) :
    ∃ (φ : Ambient d → ℝ) (L : ℝ≥0),
      HasCompactSupport φ ∧ LipschitzWith L φ ∧
      (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≠ 0 → dist x a ≤ 2 * r) ∧
      (∫ x, φ x ∂μ) = 1 ∧ (L : ℝ) ≤ (c * r ^ (n + 1))⁻¹ := by
  let := hg.finite_on_compacts
  let b := scaledBallBump a r
  let M := ∫ x, b x ∂μ
  have hfinite : μ (ball a r) ≠ ∞ :=
    ((hg.2 a r hr).trans_lt ENNReal.ofReal_lt_top).ne
  have hl : c * r ^ n ≤ M := by
    have ht := ENNReal.toReal_mono hfinite hmass
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    exact ht.trans (scaledBallBump_integral_lower μ a r hr)
  have hM : 0 < M := (mul_pos hc (pow_pos hr n)).trans_le hl
  let φ := fun x => M⁻¹ * b x
  let L : ℝ≥0 := ‖M⁻¹‖₊ * Real.toNNReal r⁻¹
  refine ⟨φ, L, (scaledBallBump_hasCompactSupport a r hr).mul_left,
    lipschitz_const_mul_real (scaledBallBump_lipschitz a r hr) M⁻¹, ?_, ?_, ?_, ?_⟩
  · intro x
    exact mul_nonneg (inv_nonneg.mpr hM.le) (scaledBallBump_bounds a r x).1
  · intro x hx
    apply scaledBallBump_support_bound a r hr x
    intro hb
    exact hx (by simp only [φ, b, hb, mul_zero])
  · change (∫ x, M⁻¹ * b x ∂μ) = 1
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hM.ne'
  · change ((‖M⁻¹‖₊ : ℝ) * (Real.toNNReal r⁻¹ : ℝ)) ≤ _
    rw [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM),
      Real.coe_toNNReal r⁻¹ (inv_nonneg.mpr hr.le)]
    calc
      _ ≤ (c * r ^ n)⁻¹ * r⁻¹ := mul_le_mul_of_nonneg_right
        (by simpa only [one_div] using! one_div_le_one_div_of_le (by positivity : 0 < c * r ^ n) hl)
        (inv_nonneg.mpr hr.le)
      _ = _ := by rw [pow_succ, ← mul_assoc, mul_inv_rev]; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_LocalReflectionlessTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local constancy from reflectionlessness

A renormalized local transform annihilates mean-zero Lipschitz tests under
reflectionlessness. A normalized ball bump and local L² integrability then identify
the transform with a constant almost everywhere on the inner ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal

theorem local_transform_constant_of_reflectionless {d : ℕ} (p : ℕ) (C c : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ) (hc : 0 < c)
    (e a : Ambient d) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hmass : ENNReal.ofReal (c * (H / 4) ^ (p + 1)) ≤ μ (ball a (H / 4)))
    (v : Lp ℝ 2 (μ.restrict (ball a R)))
    (hv : ∀ (φ : Ambient d → ℝ) (L B : ℝ≥0), LipschitzWith L φ →
      (∀ x, |φ x| ≤ (B : ℝ)) → (∫ x in ball a R, v x * φ x ∂μ) =
        (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e φ q
          ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))))
    (hreflect : ScalarReflectionlessAt (p + 1) μ a) :
    ∃ b : ℝ, ∀ᵐ x ∂μ, x ∈ ball a H →
      v x + scalarFarRieszTransform (p + 1) μ e a R x = b := by
  let := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a H hH
  obtain ⟨hL2, hpair⟩ := local_renormalized_pairing_representation p C μ hg e a H R hH hR hHR v hv
  obtain ⟨η, Kη, hηc, hη, _, hηs, hηmean, _⟩ :=
    exists_normalized_ball_bump (p + 1) C c μ hg hc a (H / 4) (by positivity) hmass
  have hηU : support η ⊆ ball a H := by
    intro x hx
    exact (hηs x hx).trans_lt (by linarith : 2 * (H / 4) < H)
  apply local_mean_zero_test_annihilator_constant μ (ball a H) isOpen_ball
    (fun x => v x + scalarFarRieszTransform (p + 1) μ e a R x)
    (hL2.integrable (by norm_num)) η Kη hη hηc hηU hηmean
  intro φ K hφ hφc hφs hφmean
  obtain ⟨B, hB⟩ := hφc.exists_bound_of_continuous hφ.continuous
  have hb : ∀ x, |φ x| ≤ (Real.toNNReal B : ℝ) := by
    intro x
    have hb' : |φ x| ≤ B := by simpa only [Real.norm_eq_abs] using! hB x
    exact hb'.trans (Real.le_coe_toNNReal B)
  have hs : ∀ x, φ x ≠ 0 → dist x a ≤ H := fun x hx => (hφs hx).le
  rw [← hpair φ K (Real.toNNReal B) hφ hb hs]
  exact hreflect e φ K H R hφ hH.le hR hHR hs hφmean

theorem exists_local_constant_transform_of_source_L2 {d : ℕ} (p : ℕ) (C G c : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
    (hgν : GlobalUpperGrowth (p + 1) G ν) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε f) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε f) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm f 2 (μ j))
    (e a : Ambient d) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hboundary : ν (frontier (ball a R)) = 0) (hmass : ν (ball a R) ≠ 0)
    (hc : 0 < c) (hlower : ENNReal.ofReal (c * (H / 4) ^ (p + 1)) ≤ ν (ball a (H / 4)))
    (hreflect : ScalarReflectionlessAt (p + 1) ν a) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      Tendsto (fun j => (1 / 2 : ℝ) ^ (ρ j)) atTop (𝓝 0) ∧
      ∃ v : Lp ℝ 2 (ν.restrict (ball a R)),
        ‖v‖ ≤ (Real.toNNReal (‖e‖ * ((D : ℝ) + C * 2 ^ (p + 1))) : ℝ) *
          Real.sqrt (ν.real (ball a R)) ∧
        (∀ g : Ambient d → ℝ, MemLp g 2 (ν.restrict (ball a R)) →
          Tendsto (fun j => ∫ x in ball a R,
            scalarCappedTransform (p + 1) (ν.restrict (ball a R)) e ((1 / 2 : ℝ) ^ (ρ j))
              (fun _ => 1) x * g x ∂ν) atTop (𝓝 (∫ x in ball a R, v x * g x ∂ν))) ∧
        ∃ b : ℝ, ∀ᵐ x ∂ν, x ∈ ball a H →
          v x + scalarFarRieszTransform (p + 1) ν e a R x = b := by
  obtain ⟨ρ, hρ, hεlim, v, hv, hlim, hrep⟩ := exists_local_L2_interior_representative
    p C G μ ν hgrowth hgν hweak D hB a R hboundary hmass e
  exact ⟨ρ, hρ, hεlim, v, hv, hlim,
    local_transform_constant_of_reflectionless p G c ν hgν hc e a H R hH hR hHR hlower v hrep hreflect⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SourcePlanarUnweightedEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_source_planar_unweighted_capped_equation_oai {d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
    (hgν : GlobalUpperGrowth (p + 1) G ν) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε f) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε f) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm f 2 (μ j))
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (f : Ambient (p + 1) → ℝ)
    (hf : Measurable f) (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
    (hdensity : ((volume : Measure (Ambient (p + 1))).withDensity
      (fun x => ENNReal.ofReal (f x))).map L = ν)
    (e a : Ambient (p + 1)) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hboundary : ν (frontier (ball (L a) R)) = 0) (hmass : ν (ball (L a) R) ≠ 0)
    (cMass : ℝ) (hcMass : 0 < cMass)
    (hlowerMass : ENNReal.ofReal (cMass * (H / 4) ^ (p + 1)) ≤ ν (ball (L a) (H / 4)))
    (hreflect : ScalarReflectionlessAt (p + 1) ν (L a)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      Tendsto (fun j => (1 / 2 : ℝ) ^ (s j)) atTop (𝓝 0) ∧
      ∃ b : ℝ, ∀ (g : Ambient (p + 1) → ℝ), Measurable g →
        ∀ B : ℝ, (∀ x, |g x| ≤ B) → Integrable g volume →
          (∀ x, g x ≠ 0 → x ∈ ball a H) →
          Tendsto (fun j =>
            (∫ x, scalarCappedTransform (p + 1) (volume.restrict (ball a R))
              e ((1 / 2 : ℝ) ^ (s j)) f x * g x) +
            ∫ x, (∫ y in closedExterior a R, f y *
              inner ℝ e (kernel (p + 1) x y - kernel (p + 1) a y)) * g x)
            atTop (𝓝 (b * ∫ x, g x)) := by
  subst ν
  let ρ : Measure (Ambient (p + 1)) := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have hgρ : GlobalUpperGrowth (p + 1) G ρ := by
    refine ⟨hgν.1, ?_⟩
    intro x r hr
    have hpre : L ⁻¹' ball (L x) r = ball x r := by
      ext y
      simp only [mem_preimage, mem_ball, L.dist_map]
    have h := hgν.2 (L x) r hr
    rw [Measure.map_apply L.continuous.measurable measurableSet_ball, hpre] at h
    exact h
  obtain ⟨s, hs, hεlim, v, _, hlim, b, hconstant⟩ :=
    exists_local_constant_transform_of_source_L2 p C G cMass μ (ρ.map L)
      hgrowth hgν hweak D hB (L e) (L a) H R hH hR hHR hboundary hmass hcMass hlowerMass hreflect
  obtain ⟨_, hlimIntrinsic⟩ := local_capped_weak_L2_pairings_linearIsometry (p + 1) L ρ e a R
    (fun j => (1 / 2 : ℝ) ^ (s j)) v (Lp.memLp v) hlim
  have hconstantIntrinsic := local_transform_constancy_linearIsometry (p + 1) L ρ e a H R b v hconstant
  refine ⟨s, hs, hεlim, b, ?_⟩
  intro g hg B hBg hgI hgs
  exact unweighted_capped_pairing_tendsto_constant (p + 1) G f hf c hc hlower hgρ e a H R b
    hH hR hHR (fun j => (1 / 2 : ℝ) ^ (s j)) (fun x => v (L x))
    hlimIntrinsic hconstantIntrinsic g hg B hBg hgI hgs

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.exists_source_planar_unweighted_capped_equation_oai := @OAI.RieszRectifiability.exists_source_planar_unweighted_capped_equation_oai
