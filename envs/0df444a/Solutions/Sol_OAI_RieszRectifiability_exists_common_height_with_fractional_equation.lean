-- Prove2me | solution 1 for OAI.RieszRectifiability.exists_common_height_with_fractional_equation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:23.957626+00:00
-- url     : https://prove2.me/submissions/3fd28649-4a6b-4415-a829-5f6e5cb86bde

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000
import Theorems.Thm_OAI_RieszRectifiability_exists_global_height_with_local_singular_limits
import Theorems.Thm_OAI_RieszRectifiability_schwartz_fractional_equation_of_real_pairing

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_MeasureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

theorem kernel_antisymm {d : ℕ} (n : ℕ) (x y : Ambient d) :
    kernel n y x = -kernel n x y := by
  rw [kernel, kernel, norm_sub_rev, ← neg_sub x y, smul_neg]

end

end RieszRectifiability

end OAI
end

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

theorem openProjectionBox_isOpen {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (I : Box ι) (π : X → ι → ℝ) (hπ : Continuous π) : IsOpen (openProjectionBox I π) :=
  (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).preimage hπ

theorem coordinatePlaneMeasure_upper_growth {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (he : Measurable e) (Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e) :
    GlobalUpperGrowth (Fintype.card ι) ((2 * (Q : ℝ)) ^ Fintype.card ι)
      (coordinatePlaneMeasure e) := by
  refine ⟨by positivity, ?_⟩
  intro x r hr
  rw [coordinatePlaneMeasure, Measure.map_apply he measurableSet_ball]
  calc
    volume (e ⁻¹' ball x r) ≤ volume (closedBall (π x) ((Q : ℝ) * r)) := by
      apply measure_mono
      intro u hu
      apply mem_closedBall.mpr
      have hu' : dist (e u) x < r := hu
      calc
        dist u (π x) = dist (π (e u)) (π x) := by rw [hleft u]
        _ ≤ (Q : ℝ) * dist (e u) x := hπ.dist_le_mul _ _
        _ ≤ (Q : ℝ) * r := mul_le_mul_of_nonneg_left hu'.le Q.coe_nonneg
    _ = ENNReal.ofReal ((2 * ((Q : ℝ) * r)) ^ Fintype.card ι) :=
      Real.volume_pi_closedBall (π x) (mul_nonneg Q.coe_nonneg hr.le)
    _ = ENNReal.ofReal ((2 * (Q : ℝ)) ^ Fintype.card ι * r ^ Fintype.card ι) := by
      congr 1
      rw [← mul_assoc, mul_pow]

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BoundedPlaneBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem mem_exhaustionBox_Ioo_of_norm_lt {ι : Type*} [Fintype ι]
    (H : ℕ) (u : ι → ℝ) (hu : ‖u‖ < (H : ℝ) + 1) : u ∈ Box.Ioo (exhaustionBox ι H) := by
  intro i _
  change -((H : ℝ) + 1) < u i ∧ u i < (H : ℝ) + 1
  apply abs_lt.mp
  exact (show |u i| ≤ ‖u‖ by simpa only [Real.norm_eq_abs] using! norm_le_pi_norm u i).trans_lt hu

theorem boundedProjectionRegion_isOpen {ι : Type*} [Fintype ι] {d : ℕ}
    (π : Ambient d → ι → ℝ) (hπ : Continuous π) (a : Ambient d) (K : ℝ≥0) (H : ℕ) :
    IsOpen (boundedProjectionRegion π a K H) :=
  (openProjectionBox_isOpen (exhaustionBox ι H) π hπ).inter isOpen_ball

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_MeanZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem meanCorrection_integrable (μ : Measure X) (φ η : X → ℝ)
    (hφ : Integrable φ μ) (hη : Integrable η μ) :
    Integrable (meanCorrection μ φ η) μ :=
  hφ.sub (hη.const_mul _)

theorem meanCorrection_integral_zero (μ : Measure X) (φ η : X → ℝ)
    (hφ : Integrable φ μ) (hη : Integrable η μ) (hne : (∫ x, η x ∂μ) ≠ 0) :
    (∫ x, meanCorrection μ φ η x ∂μ) = 0 := by
  change (∫ x, φ x - ((∫ y, φ y ∂μ) / (∫ y, η y ∂μ)) * η x ∂μ) = 0
  rw [integral_sub hφ (hη.const_mul _), integral_const_mul,
    div_mul_cancel₀ _ hne, sub_self]

theorem meanCorrection_coefficient_tendsto_zero
    (μ : ℕ → Measure X) (φ η : X → ℝ) (b : ℝ) (hb : b ≠ 0)
    (hφ : Tendsto (fun j => ∫ x, φ x ∂μ j) atTop (𝓝 0))
    (hη : Tendsto (fun j => ∫ x, η x ∂μ j) atTop (𝓝 b)) :
    Tendsto (fun j => (∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)) atTop (𝓝 0) := by
  simpa only [zero_div] using! hφ.div hη hb

end

end RieszRectifiability

end OAI
end

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

theorem ball_restriction_mass_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    (μ.restrict (ball a R)).real univ ≤ C * R ^ m := by
  simpa only [Measure.real, Measure.restrict_apply_univ] using!
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (by positivity)) (hg.2 a R hR)

theorem ball_restriction_pair_diameter {d : ℕ}
    (μ : Measure (Ambient d)) (a : Ambient d) (R : ℝ)
    [SFinite (μ.restrict (ball a R))] :
    ∀ᵐ q ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R)), dist q.1 q.2 ≤ 2 * R := by
  have hs : ∀ᵐ x ∂μ.restrict (ball a R), x ∈ ball a R := ae_restrict_mem measurableSet_ball
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs,
    Measure.quasiMeasurePreserving_snd.ae hs] with q hx hy
  change dist q.1 a < R at hx
  change dist q.2 a < R at hy
  have ht := dist_triangle q.1 a q.2
  rw [dist_comm a q.2] at ht
  linarith

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_EnergyFromTruncations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ENNReal

theorem nonnegative_integrable_of_exhaustion {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    (s : ℕ → Set X) (hs : ∀ k, MeasurableSet (s k)) (hmono : Monotone s)
    (hcover : Function.support f ⊆ ⋃ k, s k)
    (hI : ∀ k, IntegrableOn f (s k) μ) (B : ℝ)
    (hB : ∀ k, (∫ x in s k, f x ∂μ) ≤ B) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ B := by
  have hnn : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall hpos
  have hfull : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
      ∫⁻ x in ⋃ k, s k, ENNReal.ofReal (f x) ∂μ := by
    rw [← lintegral_indicator (MeasurableSet.iUnion hs)]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ ⋃ k, s k
    · rw [indicator_of_mem hx]
    · have hfx : f x = 0 := by
        by_contra h
        exact hx (hcover h)
      rw [indicator_of_notMem hx, hfx, ENNReal.ofReal_zero]
  have hbound : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal B := by
    rw [hfull, setLIntegral_iUnion_of_directed _ hmono.directed_le]
    apply iSup_le
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hI k) (Filter.Eventually.of_forall hpos)]
    exact ENNReal.ofReal_le_ofReal (hB k)
  have hfin : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ∞ :=
    (hbound.trans_lt ENNReal.ofReal_lt_top).ne
  have hint : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hnn).mp hfin
  refine ⟨hint, ?_⟩
  have hB0 : 0 ≤ B := (integral_nonneg hpos).trans (hB 0)
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hB0 hbound

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ShellHeightL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# First-moment bounds on dyadic shells

Cauchy–Schwarz bounds an absolute first moment by the mass and second moment of
a finite measure. Applying this estimate to dyadic annuli combines upper growth
with shellwise second-moment decay to control the corresponding height integral.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem integral_abs_sq_le_mass_second_moment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (w : X → ℝ) (hw : MemLp w 2 ν) :
    (∫ x, |w x| ∂ν) ^ 2 ≤ ν.real univ * (∫ x, w x ^ 2 ∂ν) := by
  have h := integral_mul_cauchy_schwarz_sq ν (fun x => ‖w x‖) (fun _ => (1 : ℝ))
    hw.norm (memLp_const 1)
  simpa only [mul_one, one_mul, one_pow, integral_const, smul_eq_mul, Real.norm_eq_abs,
    sq_abs, mul_comm] using! h

theorem integral_abs_le_of_mass_second_moment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (w : X → ℝ) (hw : MemLp w 2 ν)
    (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hmass : ν.real univ ≤ M) (hsecond : (∫ x, w x ^ 2 ∂ν) ≤ M * A ^ 2) :
    (∫ x, |w x| ∂ν) ≤ M * A := by
  have hsq : (∫ x, |w x| ∂ν) ^ 2 ≤ (M * A) ^ 2 := by
    calc
      _ ≤ ν.real univ * (∫ x, w x ^ 2 ∂ν) := integral_abs_sq_le_mass_second_moment ν w hw
      _ ≤ M * (M * A ^ 2) := mul_le_mul hmass hsecond
        (integral_nonneg fun x => sq_nonneg _) hM
      _ = _ := by ring
  exact (sq_le_sq₀ (integral_nonneg fun x => abs_nonneg _) (mul_nonneg hM hA)).mp hsq

theorem shell_height_l1_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (w : Ambient d → ℝ) (hw : MemLp w 2 (μ.restrict (dyadicAnnulus a R k)))
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (hsecond : (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    (∫ y in dyadicAnnulus a R k, |w y| ∂μ) ≤
      B * δ * (R * 2 ^ k) ^ (m + 1) * b ^ k := by
  let ν := μ.restrict (dyadicAnnulus a R k)
  have : IsFiniteMeasure ν := ⟨by
    simpa only [ν, Measure.restrict_apply_univ] using! dyadicAnnulus_measure_lt_top m C μ hg a R hR k⟩
  have hB : 0 ≤ B := (mul_nonneg hg.1 (by positivity)).trans hCB
  have hmass : ν.real univ ≤ B * (R * 2 ^ k) ^ m := by
    have hmass' : μ.real (dyadicAnnulus a R k) ≤ C * (R * 2 ^ (k + 1)) ^ m :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (by positivity))
        ((measure_mono (dyadicAnnulus_subset_ball a R k)).trans (hg.2 a _ (by positivity)))
    have heq : C * (R * (2 : ℝ) ^ (k + 1)) ^ m = (C * 2 ^ m) * (R * 2 ^ k) ^ m := by
      rw [pow_succ, show R * ((2 : ℝ) ^ k * 2) = (R * 2 ^ k) * 2 by ring, mul_pow]
      ring
    change (μ.restrict (dyadicAnnulus a R k)).real univ ≤ _
    simpa only [Measure.real, Measure.restrict_apply_univ] using!
      hmass'.trans (heq ▸ mul_le_mul_of_nonneg_right hCB (by positivity))
  have h := integral_abs_le_of_mass_second_moment ν w hw
    (B * (R * 2 ^ k) ^ m) (δ * (R * 2 ^ k) * b ^ k) (by positivity) (by positivity) hmass hsecond
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  rw [pow_succ]
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

variable [MeasurableSpace X]

theorem meanCorrection_lipschitz (μ : Measure X) {φ η : X → ℝ}
    {Kφ Kη : ℝ≥0} (hφ : LipschitzWith Kφ φ) (hη : LipschitzWith Kη η) :
    LipschitzWith (Kφ + ‖(∫ y, φ y ∂μ) / (∫ y, η y ∂μ)‖₊ * Kη)
      (meanCorrection μ φ η) :=
  hφ.sub (lipschitz_const_mul_real hη _)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LocalLipschitzEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local Lipschitz control of fractional energy

Almost-everywhere Lipschitz difference bounds and bounded pair distances give
integrability of fractional pair energies under global upper growth. Their weighted
differences lie in L², yielding integrability of the associated bilinear pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem fractionalEnergy_bound_of_difference_bound {d : ℕ} (p : ℕ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (x y : Ambient d)
    (h : |w x - w y| ≤ (K : ℝ) * dist x y) :
    fractionalPairEnergy (p + 1) w x y ≤ (K : ℝ) ^ 2 * inverseDistancePow p x y := by
  by_cases hxy : x = y
  · subst y
    simp only [fractionalPairEnergy, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]
    exact mul_nonneg (sq_nonneg _) (inverseDistancePow_nonneg _ _ _)
  · have hd : 0 < dist x y := dist_pos.mpr hxy
    have hsq : (w x - w y) ^ 2 ≤ (K : ℝ) ^ 2 * dist x y ^ 2 := by
      simpa only [sq_abs, mul_pow] using!
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg K.coe_nonneg dist_nonneg)).mpr h
    calc
      _ ≤ ((K : ℝ) ^ 2 * dist x y ^ 2) / dist x y ^ (p + 1 + 1) :=
        div_le_div_of_nonneg_right hsq (pow_nonneg dist_nonneg _)
      _ = _ := by
        rw [show p + 1 + 1 = p + 2 by omega, pow_add]
        unfold inverseDistancePow
        field_simp

theorem fractionalEnergy_integrable_of_ae_lipschitz {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w : Ambient d → ℝ) (hw : Measurable w) (K : ℝ≥0)
    (hK : ∀ᵐ q ∂μ.prod μ, |w q.1 - w q.2| ≤ (K : ℝ) * dist q.1 q.2)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂μ.prod μ, dist q.1 q.2 ≤ r) :
    Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) w q.1 q.2)
      (μ.prod μ) := by
  have hm : Measurable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) w q.1 q.2) := by
    unfold fractionalPairEnergy
    fun_prop
  apply ((nearPairWeight_integrable p C μ hg r hr).const_mul ((K : ℝ) ^ 2)).mono'
    hm.aestronglyMeasurable
  filter_upwards [hK, hdiam] with q hq hd
  have hmem : q ∈ nearPairSet r := by
    simpa only [nearPairSet, mem_ofPred_eq, mem_closedBall, dist_comm] using! hd
  rw [Real.norm_of_nonneg (fractionalPairEnergy_nonneg _ _ _ _), nearPairWeight,
    indicator_of_mem hmem]
  exact fractionalEnergy_bound_of_difference_bound p w K q.1 q.2 hq

theorem fractionalBilinear_integrable_of_ae_lipschitz {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w ψ : Ambient d → ℝ) (hw : Measurable w) (hψ : Measurable ψ) (K L : ℝ≥0)
    (hK : ∀ᵐ q ∂μ.prod μ, |w q.1 - w q.2| ≤ (K : ℝ) * dist q.1 q.2)
    (hL : ∀ᵐ q ∂μ.prod μ, |ψ q.1 - ψ q.2| ≤ (L : ℝ) * dist q.1 q.2)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂μ.prod μ, dist q.1 q.2 ≤ r) :
    Integrable (fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) w ψ q.1 q.2)
      (μ.prod μ) := by
  have hf := weightedDifference_memLp (p + 1) w hw (μ.prod μ)
    (fractionalEnergy_integrable_of_ae_lipschitz p C μ hg w hw K hK r hr hdiam)
  have hgtest := weightedDifference_memLp (p + 1) ψ hψ (μ.prod μ)
    (fractionalEnergy_integrable_of_ae_lipschitz p C μ hg ψ hψ L hL r hr hdiam)
  have hprod : MemLp (fun q : Ambient d × Ambient d =>
      weightedDifference (p + 1) w q.1 q.2 * weightedDifference (p + 1) ψ q.1 q.2)
      1 (μ.prod μ) := MemLp.mul' (hφ := hf) (hf := hgtest)
  simpa only [weightedDifference_mul] using! memLp_one_iff_integrable.mp hprod

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FiniteShellTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted height bounds on dyadic shells

Square-integrable height bounds on each shell control integrals weighted by
inverse powers of distance. The dyadic coefficient identity expresses these
estimates in the geometric form needed for tail bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem dyadic_weighted_height_coefficient (m k : ℕ) (B δ R b : ℝ) (hR : 0 < R) :
    ((R * 2 ^ k) ^ (m + 2))⁻¹ * (B * δ * (R * 2 ^ k) ^ (m + 1) * b ^ k) =
      (B * δ / R) * (b / 2) ^ k := by
  rw [show m + 2 = (m + 1) + 1 by omega, pow_succ, div_pow]
  field_simp

theorem shell_weighted_height_integrable_and_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (w : Ambient d → ℝ) (hw : MemLp w 2 (μ.restrict (dyadicAnnulus a R k)))
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (hsecond : (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (dyadicAnnulus a R k) μ ∧
      (∫ y in dyadicAnnulus a R k, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        (B * δ / R) * (b / 2) ^ k := by
  have : IsFiniteMeasure (μ.restrict (dyadicAnnulus a R k)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using! dyadicAnnulus_measure_lt_top m C μ hg a R hR k⟩
  have hfirst := (hw.integrable (by norm_num)).abs
  have hpoint : ∀ᵐ y ∂μ.restrict (dyadicAnnulus a R k),
      ‖inverseDistancePow (m + 2) a y‖ ≤ ((R * 2 ^ k) ^ (m + 2))⁻¹ := by
    filter_upwards [ae_restrict_mem (dyadicAnnulus_measurable a R k)] with y hy
    exact inverseDistancePow_bound_on_annulus (m + 2) a R hR k y hy
  have hi := hfirst.mul_bdd (inverseDistancePow_measurable (m + 2) a).aestronglyMeasurable hpoint
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y in dyadicAnnulus a R k, ((R * 2 ^ k) ^ (m + 2))⁻¹ * |w y| ∂μ := by
      apply integral_mono_ae hi (hfirst.const_mul _)
      filter_upwards [hpoint] with y hy
      rw [Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)] at hy
      simpa only [mul_comm] using! mul_le_mul_of_nonneg_left hy (abs_nonneg (w y))
    _ = ((R * 2 ^ k) ^ (m + 2))⁻¹ * (∫ y in dyadicAnnulus a R k, |w y| ∂μ) :=
      integral_const_mul _ _
    _ ≤ ((R * 2 ^ k) ^ (m + 2))⁻¹ * (B * δ * (R * 2 ^ k) ^ (m + 1) * b ^ k) :=
      mul_le_mul_of_nonneg_left (shell_height_l1_bound m C B μ hg hCB a R hR k w hw δ b hδ hb hsecond)
        (by positivity)
    _ = _ := dyadic_weighted_height_coefficient m k B δ R b hR

theorem finiteShellRegion_eq {d : ℕ} (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    finiteShellRegion a R N = {y | R ≤ dist a y ∧ dist a y < R * 2 ^ N} := by
  ext y
  constructor
  · intro hy
    obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp hy
    have hlow : R ≤ R * (2 : ℝ) ^ k := by
      simpa only [mul_one] using!
        mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
    have hhigh : R * (2 : ℝ) ^ (k + 1) ≤ R * 2 ^ N :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt (Finset.mem_range.mp hk))) hR.le
    exact ⟨hlow.trans hyk.1, hyk.2.trans_le hhigh⟩
  · intro hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp ((closedExterior_subset_iUnion_dyadicAnnulus a R hR) hy.1)
    have hkN : k < N := by
      by_contra h
      have hp : R * (2 : ℝ) ^ N ≤ R * 2 ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.le_of_not_gt h)) hR.le
      exact (not_lt_of_ge (hp.trans hk.1)) hy.2
    exact mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr hkN, hk⟩

theorem finite_shell_weighted_height_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (w : Ambient d → ℝ) (hw : ∀ k < N, MemLp w 2 (μ.restrict (dyadicAnnulus a R k)))
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hsecond : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (finiteShellRegion a R N) μ ∧
      (∫ y in finiteShellRegion a R N, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        (B * δ / R) / (1 - b / 2) := by
  have hB : 0 ≤ B := (mul_nonneg hg.1 (by positivity)).trans hCB
  have hI (k : ℕ) (hk : k ∈ Finset.range N) :=
    (shell_weighted_height_integrable_and_bound m C B μ hg hCB a R hR k w
      (hw k (Finset.mem_range.mp hk)) δ b hδ hb0 (hsecond k (Finset.mem_range.mp hk))).1
  have hratio : ‖b / 2‖ < 1 := by rw [Real.norm_of_nonneg (by positivity)]; linarith
  have hgeo := summable_geometric_of_norm_lt_one hratio
  constructor
  · exact integrableOn_finset_iUnion.mpr hI
  · rw [finiteShellRegion, integral_biUnion_finset (Finset.range N)
      (fun k _ => dyadicAnnulus_measurable a R k)
      (fun k _ l _ hkl => dyadicAnnulus_disjoint a R hR hkl) hI]
    calc
      _ ≤ ∑ k ∈ Finset.range N, (B * δ / R) * (b / 2) ^ k := by
        apply Finset.sum_le_sum
        intro k hk
        exact (shell_weighted_height_integrable_and_bound m C B μ hg hCB a R hR k w
          (hw k (Finset.mem_range.mp hk)) δ b hδ hb0 (hsecond k (Finset.mem_range.mp hk))).2
      _ = (B * δ / R) * ∑ k ∈ Finset.range N, (b / 2) ^ k := by rw [Finset.mul_sum]
      _ ≤ (B * δ / R) * ∑' k : ℕ, (b / 2) ^ k :=
        mul_le_mul_of_nonneg_left (hgeo.sum_le_tsum (Finset.range N) (fun k _ => by positivity))
          (by positivity)
      _ = _ := by rw [tsum_geometric_of_norm_lt_one hratio]; rfl

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

theorem lipschitz_height_memLp_on_annulus {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (k : ℕ) :
    MemLp w 2 (μ.restrict (dyadicAnnulus a R k)) := by
  have : IsFiniteMeasure (μ.restrict (dyadicAnnulus a R k)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using! dyadicAnnulus_measure_lt_top m C μ hg a R hR k⟩
  apply MemLp.of_bound hw.continuous.measurable.aestronglyMeasurable
    ((K : ℝ) * (R * 2 ^ (k + 1)) + |w a|)
  filter_upwards [ae_restrict_mem (dyadicAnnulus_measurable a R k)] with y hy
  rw [Real.norm_eq_abs]
  have hdiff : |w y - w a| ≤ (K : ℝ) * dist a y := by
    simpa only [Real.dist_eq, dist_comm y a] using! hw.dist_le_mul y a
  have habs : |w y| ≤ |w y - w a| + |w a| := by
    simpa only [sub_add_cancel] using! abs_add_le (w y - w a) (w a)
  exact habs.trans (add_le_add
    (hdiff.trans (mul_le_mul_of_nonneg_left hy.2.le K.coe_nonneg)) le_rfl)

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

theorem finiteShellRegion_union_closedExterior {d : ℕ}
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    finiteShellRegion a R N ∪ closedExterior a (R * 2 ^ N) = closedExterior a R := by
  rw [finiteShellRegion_eq a R hR N]
  have hRT : R ≤ R * (2 : ℝ) ^ N := by
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
  ext y
  change (R ≤ dist a y ∧ dist a y < R * 2 ^ N) ∨ R * 2 ^ N ≤ dist a y ↔ R ≤ dist a y
  constructor
  · rintro (h | h)
    · exact h.1
    · exact hRT.trans h
  · intro hy
    by_cases h : dist a y < R * 2 ^ N
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr (le_of_not_gt h)

theorem finiteShellRegion_disjoint_closedExterior {d : ℕ}
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    Disjoint (finiteShellRegion a R N) (closedExterior a (R * 2 ^ N)) := by
  rw [finiteShellRegion_eq a R hR N]
  exact Set.disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hy) hx.2)

theorem improved_weighted_height_tail_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hsecond : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ ∧
      (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        (B * δ / R) / (1 - b / 2) +
          ((K : ℝ) + |w a| / (R * 2 ^ N)) * (2 * (C * 2 ^ m / (R * 2 ^ N))) := by
  obtain ⟨hIfin, hbfin⟩ := finite_shell_weighted_height_bound m C B μ hg hCB a R hR N w
    (fun k _ => lipschitz_height_memLp_on_annulus m C μ hg w K hw a R hR k) δ b hδ hb0 hb2 hsecond
  obtain ⟨hItail, hbtail⟩ := weighted_height_closed_tail_bound m C μ hg w K hw a (R * 2 ^ N) (by positivity)
  rw [← finiteShellRegion_union_closedExterior a R hR N]
  refine ⟨hIfin.union hItail, ?_⟩
  rw [setIntegral_union (finiteShellRegion_disjoint_closedExterior a R hR N)
    (closedExterior_measurable a (R * 2 ^ N)) hIfin hItail]
  exact add_le_add hbfin hbtail

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

theorem riesz_far_integral_eq_normal {d : ℕ} (m : ℕ) (C : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasure ν]
    (hg : GlobalUpperGrowth m C μ) (e : Ambient d) (w φ : Ambient d → ℝ)
    (hw : ∀ x y, w x - w y = inner ℝ e (x - y))
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (hφ : Integrable φ ν) (hzero : (∫ x, φ x ∂ν) = 0)
    (hN : Integrable (renormalizedNormalIntegrand m w φ a) (ν.prod (μ.restrict (closedExterior a R)))) :
    Integrable (rieszFarIntegrand m e φ a) (ν.prod (μ.restrict (closedExterior a R))) ∧
      (∫ q, rieszFarIntegrand m e φ a q ∂ν.prod (μ.restrict (closedExterior a R))) =
        ∫ q, renormalizedNormalIntegrand m w φ a q ∂ν.prod (μ.restrict (closedExterior a R)) := by
  have hk := (inverseDistancePow_closedExterior_integrable_and_bound m C μ hg a R hR).1
  have hcorrection := (hφ.mul_const (w a)).mul_prod hk
  have heq : rieszFarIntegrand m e φ a = fun q => renormalizedNormalIntegrand m w φ a q -
      (φ q.1 * w a) * inverseDistancePow (m + 1) a q.2 := by
    funext q
    exact rieszFarIntegrand_eq_normal_sub_correction m e w φ hw a q
  rw [heq]
  refine ⟨hN.sub hcorrection, ?_⟩
  rw [integral_sub hN hcorrection, integral_prod_mul (fun x => φ x * w a) (inverseDistancePow (m + 1) a),
    integral_mul_const, hzero, zero_mul, zero_mul, sub_zero]

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

theorem rieszInteriorIntegrand_integrable_of_lipschitz {d : ℕ} (p : ℕ) (C : ℝ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (hg : GlobalUpperGrowth (p + 1) C ν)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂ν.prod ν, dist q.1 q.2 ≤ r) :
    Integrable (rieszInteriorIntegrand (p + 1) e φ) (ν.prod ν) := by
  let w := affineNormalHeight e 0 0
  have hw : LipschitzWith ‖e‖₊ w := affineNormalHeight_lipschitz e 0 0
  have hI := fractionalBilinear_integrable_of_ae_lipschitz p C ν hg w φ
    hw.continuous.measurable hφ.continuous.measurable ‖e‖₊ L
    (Filter.Eventually.of_forall fun q => by simpa only [Real.dist_eq] using! hw.dist_le_mul q.1 q.2)
    (Filter.Eventually.of_forall fun q => by simpa only [Real.dist_eq] using! hφ.dist_le_mul q.1 q.2)
    r hr hdiam
  have heq : rieszInteriorIntegrand (p + 1) e φ =
      fun q => fractionalBilinear (p + 1) w φ q.1 q.2 := by
    funext q
    exact rieszInteriorIntegrand_eq_fractionalBilinear (p + 1) e w φ
      (affineNormalHeight_difference e 0 0) q
  rw [heq]
  exact hI

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SymmetricPairingSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

theorem integral_symmetric_pair_split {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (s : Set X) (hs : MeasurableSet s)
    (F : X × X → ℝ) (hF : Integrable F (ν.prod ν))
    (hsym : ∀ q, F q.swap = F q)
    (hzero : ∀ x ∉ s, ∀ y ∉ s, F (x, y) = 0) :
    (∫ q, F q ∂ν.prod ν) =
      (∫ q, F q ∂(ν.restrict s).prod (ν.restrict s)) +
        2 * (∫ q, F q ∂(ν.restrict s).prod (ν.restrict sᶜ)) := by
  have hss : Integrable F ((ν.restrict s).prod (ν.restrict s)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have hsc : Integrable F ((ν.restrict s).prod (ν.restrict sᶜ)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have hcs : Integrable F ((ν.restrict sᶜ).prod (ν.restrict s)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have hcc : Integrable F ((ν.restrict sᶜ).prod (ν.restrict sᶜ)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have hmeasure : ν.prod ν =
      ((ν.restrict s).prod (ν.restrict s) + (ν.restrict s).prod (ν.restrict sᶜ)) +
      ((ν.restrict sᶜ).prod (ν.restrict s) + (ν.restrict sᶜ).prod (ν.restrict sᶜ)) := by
    calc
      ν.prod ν = (ν.restrict s + ν.restrict sᶜ).prod (ν.restrict s + ν.restrict sᶜ) := by
        rw [Measure.restrict_add_restrict_compl hs]
      _ = _ := by rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
  have hswap : (∫ q, F q ∂(ν.restrict sᶜ).prod (ν.restrict s)) =
      ∫ q, F q ∂(ν.restrict s).prod (ν.restrict sᶜ) := by
    simpa only [hsym] using! integral_prod_swap (μ := ν.restrict s) (ν := ν.restrict sᶜ) F
  have hcc0 : (∫ q, F q ∂(ν.restrict sᶜ).prod (ν.restrict sᶜ)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hs.compl),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hs.compl)] with q hx hy
    exact hzero q.1 hx q.2 hy
  rw [hmeasure, integral_add_measure (hss.add_measure hsc) (hcs.add_measure hcc),
    integral_add_measure hss hsc, integral_add_measure hcs hcc, hswap, hcc0]
  ring

theorem rieszInteriorIntegrand_swap {d : ℕ} (m : ℕ) (e : Ambient d)
    (φ : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    rieszInteriorIntegrand m e φ q.swap = rieszInteriorIntegrand m e φ q := by
  unfold rieszInteriorIntegrand
  dsimp only [Prod.swap]
  rw [kernel_antisymm, inner_neg_right]
  ring

theorem riesz_pairing_split {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [SFinite ν] (s : Set (Ambient d)) (hs : MeasurableSet s)
    (φ : Ambient d → ℝ) (hφzero : ∀ x ∉ s, φ x = 0)
    (hF : Integrable (rieszInteriorIntegrand m e φ) (ν.prod ν)) :
    Integrable (rieszRawCrossIntegrand m e φ) ((ν.restrict s).prod (ν.restrict sᶜ)) ∧
      (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q ∂ν.prod ν) =
        (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q ∂(ν.restrict s).prod (ν.restrict s)) +
          ∫ q, rieszRawCrossIntegrand m e φ q ∂(ν.restrict s).prod (ν.restrict sᶜ) := by
  have hcross : Integrable (rieszInteriorIntegrand m e φ) ((ν.restrict s).prod (ν.restrict sᶜ)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have heq : rieszInteriorIntegrand m e φ =ᵐ[(ν.restrict s).prod (ν.restrict sᶜ)]
      rieszRawCrossIntegrand m e φ := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hs.compl)] with q hy
    unfold rieszInteriorIntegrand rieszRawCrossIntegrand
    rw [hφzero q.2 hy, sub_zero, mul_comm]
  have hsplit := integral_symmetric_pair_split ν s hs (rieszInteriorIntegrand m e φ) hF
    (rieszInteriorIntegrand_swap m e φ) (by
      intro x hx y hy
      simp only [rieszInteriorIntegrand, hφzero x hx, hφzero y hy, sub_self, mul_zero])
  rw [integral_congr_ae heq] at hsplit
  refine ⟨(integrable_congr heq).mp hcross, ?_⟩
  linarith

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

theorem center_kernel_integrable_finite_exterior {d : ℕ} (m : ℕ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (kernel m a) (closedExterior a R) ν := by
  apply Integrable.of_bound (kernel_measurable_right m a).aestronglyMeasurable ((R ^ m)⁻¹)
  filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
  exact kernel_norm_le_truncation m a y R hR hy

theorem riesz_far_integral_eq_raw_of_mean_zero {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν η : Measure (Ambient d)) [SFinite ν] [SFinite η]
    (φ : Ambient d → ℝ) (hφ : Integrable φ ν) (hzero : (∫ x, φ x ∂ν) = 0)
    (a : Ambient d) (hk : Integrable (fun y => inner ℝ e (kernel m a y)) η)
    (hraw : Integrable (rieszRawCrossIntegrand m e φ) (ν.prod η)) :
    Integrable (rieszFarIntegrand m e φ a) (ν.prod η) ∧
      (∫ q, rieszFarIntegrand m e φ a q ∂ν.prod η) =
        ∫ q, rieszRawCrossIntegrand m e φ q ∂ν.prod η := by
  have hcorrection := hφ.mul_prod hk
  have heq : rieszFarIntegrand m e φ a = fun q => rieszRawCrossIntegrand m e φ q -
      φ q.1 * inner ℝ e (kernel m a q.2) := by
    funext q
    unfold rieszFarIntegrand rieszRawCrossIntegrand
    rw [inner_sub_right]
    ring
  rw [heq]
  refine ⟨hraw.sub hcorrection, ?_⟩
  rw [integral_sub hraw hcorrection, integral_prod_mul φ (fun y => inner ℝ e (kernel m a y)),
    hzero, zero_mul, sub_zero]

theorem finite_pairing_eq_renormalized {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (φ : Ambient d → ℝ) (hφ : Integrable φ ν) (hφzero : ∀ x ∉ ball a R, φ x = 0)
    (hzero : (∫ x in ball a R, φ x ∂ν) = 0)
    (hF : Integrable (rieszInteriorIntegrand m e φ) (ν.prod ν)) :
    Integrable (rieszFarIntegrand m e φ a)
      ((ν.restrict (ball a R)).prod (ν.restrict (closedExterior a R))) ∧
      (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q ∂ν.prod ν) =
        rieszScalarPairing m ν a R e φ := by
  obtain ⟨hraw, hsplit⟩ := riesz_pairing_split m e ν (ball a R) measurableSet_ball φ hφzero hF
  rw [← closedExterior_eq_compl_ball a R] at hraw hsplit
  have hk := Integrable.const_inner (𝕜 := ℝ) e (center_kernel_integrable_finite_exterior m ν a R hR)
  obtain ⟨hfar, heq⟩ := riesz_far_integral_eq_raw_of_mean_zero m e
    (ν.restrict (ball a R)) (ν.restrict (closedExterior a R)) φ hφ.restrict hzero a hk hraw
  refine ⟨hfar, hsplit.trans ?_⟩
  unfold rieszScalarPairing
  dsimp only
  rw [heq]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_HeightPairingRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Regional height pairings

The height pairing on a set combines the symmetric interior fractional bilinear
integral with a renormalized cross-region term. For affine normal heights and
mean-zero tests on a ball, cancellation of the far contribution identifies this
regional expression with the scalar Riesz pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

theorem fractionalBilinear_swap {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) :
    fractionalBilinear m w φ q.swap.1 q.swap.2 = fractionalBilinear m w φ q.1 q.2 := by
  unfold fractionalBilinear
  dsimp only [Prod.swap]
  rw [dist_comm q.2 q.1]
  ring

theorem height_pairing_split {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (ν : Measure (Ambient d)) [SFinite ν] (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hφzero : ∀ x ∉ s, φ x = 0)
    (hF : Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2) (ν.prod ν)) :
    Integrable (heightRawCrossIntegrand m w φ) ((ν.restrict s).prod (ν.restrict sᶜ)) ∧
      (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m w φ q.1 q.2 ∂ν.prod ν) =
        (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m w φ q.1 q.2
          ∂(ν.restrict s).prod (ν.restrict s)) +
          ∫ q, heightRawCrossIntegrand m w φ q ∂(ν.restrict s).prod (ν.restrict sᶜ) := by
  have hcross : Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2)
      ((ν.restrict s).prod (ν.restrict sᶜ)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have heq : (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2)
      =ᵐ[(ν.restrict s).prod (ν.restrict sᶜ)] heightRawCrossIntegrand m w φ := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hs.compl)] with q hy
    unfold fractionalBilinear heightRawCrossIntegrand inverseDistancePow
    rw [hφzero q.2 hy, sub_zero]
    ring
  have hsplit := integral_symmetric_pair_split ν s hs
    (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2) hF
    (fractionalBilinear_swap m w φ) (by
      intro x hx y hy
      simp only [fractionalBilinear, hφzero x hx, hφzero y hy, sub_self, mul_zero, zero_div])
  rw [integral_congr_ae heq] at hsplit
  refine ⟨(integrable_congr heq).mp hcross, ?_⟩
  linarith

theorem height_far_integral_eq_raw_of_mean_zero {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (ν η : Measure (Ambient d)) [SFinite ν] [SFinite η]
    (hφ : Integrable φ ν) (hzero : (∫ x, φ x ∂ν) = 0) (a : Ambient d)
    (hk : Integrable (fun y => w y * inverseDistancePow (m + 1) a y) η)
    (hraw : Integrable (heightRawCrossIntegrand m w φ) (ν.prod η)) :
    Integrable (renormalizedNormalIntegrand m w φ a) (ν.prod η) ∧
      (∫ q, renormalizedNormalIntegrand m w φ a q ∂ν.prod η) =
        ∫ q, heightRawCrossIntegrand m w φ q ∂ν.prod η := by
  have hcorrection := hφ.mul_prod hk
  have heq : renormalizedNormalIntegrand m w φ a = fun q => heightRawCrossIntegrand m w φ q +
      φ q.1 * (w q.2 * inverseDistancePow (m + 1) a q.2) := by
    funext q
    unfold renormalizedNormalIntegrand heightRawCrossIntegrand
    ring
  rw [heq]
  refine ⟨hraw.add hcorrection, ?_⟩
  rw [integral_add hraw hcorrection, integral_prod_mul φ
    (fun y => w y * inverseDistancePow (m + 1) a y), hzero, zero_mul, add_zero]

theorem finite_height_pairing_eq_renormalized {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (ν : Measure (Ambient d)) [SFinite ν] (a : Ambient d) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hφ : Integrable φ ν) (hφzero : ∀ x ∉ s, φ x = 0)
    (hzero : (∫ x in s, φ x ∂ν) = 0)
    (hk : IntegrableOn (fun y => w y * inverseDistancePow (m + 1) a y) sᶜ ν)
    (hF : Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2) (ν.prod ν)) :
    Integrable (renormalizedNormalIntegrand m w φ a) ((ν.restrict s).prod (ν.restrict sᶜ)) ∧
      (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m w φ q.1 q.2 ∂ν.prod ν) =
        heightPairingOn m ν a s w φ := by
  obtain ⟨hraw, hsplit⟩ := height_pairing_split m w φ ν s hs hφzero hF
  obtain ⟨hfar, heq⟩ := height_far_integral_eq_raw_of_mean_zero m w φ (ν.restrict s) (ν.restrict sᶜ)
    hφ.restrict hzero a hk hraw
  refine ⟨hfar, hsplit.trans ?_⟩
  unfold heightPairingOn
  rw [heq]

theorem heightPairingOn_height_div {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s : Set (Ambient d)) (w φ : Ambient d → ℝ) (δ : ℝ) :
    heightPairingOn m μ a s (fun x => w x / δ) φ = heightPairingOn m μ a s w φ / δ := by
  have hF : (fun q : Ambient d × Ambient d => fractionalBilinear m (fun x => w x / δ) φ q.1 q.2) =
      fun q => fractionalBilinear m w φ q.1 q.2 / δ := by
    funext q
    unfold fractionalBilinear
    ring
  have hN : renormalizedNormalIntegrand m (fun x => w x / δ) φ a =
      fun q => renormalizedNormalIntegrand m w φ a q / δ := by
    funext q
    unfold renormalizedNormalIntegrand
    ring
  unfold heightPairingOn
  rw [hF, hN, integral_div, integral_div]
  ring

theorem heightPairingOn_ball_eq_rieszScalarPairing {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e : Ambient d) (w φ : Ambient d → ℝ)
    (hw : ∀ x y, w x - w y = inner ℝ e (x - y))
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hφ : Integrable φ (μ.restrict (ball a R))) (hzero : (∫ x in ball a R, φ x ∂μ) = 0)
    (hN : Integrable (renormalizedNormalIntegrand m w φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)))) :
    heightPairingOn m μ a (ball a R) w φ = rieszScalarPairing m μ a R e φ := by
  let := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  have hext := (riesz_far_integral_eq_normal m C μ (μ.restrict (ball a R)) hg e w φ hw
    a R hR hφ hzero hN).2
  unfold heightPairingOn rieszScalarPairing
  simp_rw [rieszInteriorIntegrand_eq_fractionalBilinear m e w φ hw]
  rw [← closedExterior_eq_compl_ball a R, hext]

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_HeightTemperedDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tempered distributions associated with heights

Polynomially weighted integrability makes the positive and negative height
measures temperate. Their difference defines a tempered distribution whose action
on a Schwartz test function is integration against the signed height.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology SchwartzMap
open scoped NNReal ENNReal

theorem positivePart_sub_negativePart (r : ℝ) :
    (Real.toNNReal r : ℝ) - (Real.toNNReal (-r) : ℝ) = r := by
  rw [Real.coe_toNNReal', Real.coe_toNNReal']
  rcases le_total 0 r with hr | hr
  · rw [max_eq_left hr, max_eq_right (by linarith : -r ≤ 0), sub_zero]
  · rw [max_eq_right hr, max_eq_left (by linarith : 0 ≤ -r)]
    ring

theorem height_schwartz_integrable {d : ℕ}
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f) (q : ℕ)
    (hweight : Integrable (fun x => |f x| * polynomialDecay q x) μ)
    (g : 𝓢(Ambient d, ℂ)) : Integrable (fun x => f x • g x) μ := by
  let := positive_height_measure_temperate μ f hf q hweight
  have hnweight : Integrable (fun x => |(-f x)| * polynomialDecay q x) μ := by
    simpa only [abs_neg] using! hweight
  let := positive_height_measure_temperate μ (fun x => -f x) hf.neg q hnweight
  have hip : Integrable (fun x => (Real.toNNReal (f x) : ℝ) • g x) μ :=
    (integrable_withDensity_iff_integrable_coe_smul hf.real_toNNReal).mp
      (g.integrable (μ := positiveHeightMeasure μ f))
  have hin : Integrable (fun x => (Real.toNNReal (-f x) : ℝ) • g x) μ :=
    (integrable_withDensity_iff_integrable_coe_smul hf.neg.real_toNNReal).mp
      (g.integrable (μ := positiveHeightMeasure μ (fun x => -f x)))
  convert! hip.sub hin using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  change f x • g x = (Real.toNNReal (f x) : ℝ) • g x -
    (Real.toNNReal (-f x) : ℝ) • g x
  calc
    _ = ((Real.toNNReal (f x) : ℝ) - (Real.toNNReal (-f x) : ℝ)) • g x :=
      congrArg (fun r : ℝ => r • g x) (positivePart_sub_negativePart (f x)).symm
    _ = _ := sub_smul (Real.toNNReal (f x) : ℝ) (Real.toNNReal (-f x) : ℝ) (g x)

theorem heightTemperedDistribution_apply {d : ℕ}
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f) (q : ℕ)
    (hweight : Integrable (fun x => |f x| * polynomialDecay q x) μ)
    (g : 𝓢(Ambient d, ℂ)) : heightTemperedDistribution μ f hf q hweight g = ∫ x, f x • g x ∂μ := by
  let := positive_height_measure_temperate μ f hf q hweight
  have hnweight : Integrable (fun x => |(-f x)| * polynomialDecay q x) μ := by
    simpa only [abs_neg] using! hweight
  let := positive_height_measure_temperate μ (fun x => -f x) hf.neg q hnweight
  have hip : Integrable (fun x => (Real.toNNReal (f x) : ℝ) • g x) μ :=
    (integrable_withDensity_iff_integrable_coe_smul hf.real_toNNReal).mp
      (g.integrable (μ := positiveHeightMeasure μ f))
  have hin : Integrable (fun x => (Real.toNNReal (-f x) : ℝ) • g x) μ :=
    (integrable_withDensity_iff_integrable_coe_smul hf.neg.real_toNNReal).mp
      (g.integrable (μ := positiveHeightMeasure μ (fun x => -f x)))
  change (∫ x, g x ∂positiveHeightMeasure μ f) -
    (∫ x, g x ∂positiveHeightMeasure μ (fun x => -f x)) = ∫ x, f x • g x ∂μ
  unfold positiveHeightMeasure
  rw [integral_withDensity_eq_integral_smul hf.real_toNNReal,
    integral_withDensity_eq_integral_smul (show Measurable (fun x => Real.toNNReal (-f x)) from hf.neg.real_toNNReal)]
  simp only [NNReal.smul_def]
  refine (integral_sub hip hin).symm.trans (integral_congr_ae (Eventually.of_forall ?_))
  intro x
  calc
    _ = ((Real.toNNReal (f x) : ℝ) - (Real.toNNReal (-f x) : ℝ)) • g x :=
      (sub_smul (Real.toNNReal (f x) : ℝ) (Real.toNNReal (-f x) : ℝ) (g x)).symm
    _ = _ := congrArg (fun r : ℝ => r • g x) (positivePart_sub_negativePart (f x))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_PlaneHeightDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Function SchwartzMap

theorem coordinatePlaneMeasure_affine_eq_map {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) :
    coordinatePlaneMeasure (affinePlaneSection a L) =
      Measure.map (fun u : Ambient n => a + L u) volume := by
  change Measure.map ((fun u : Ambient n => a + L u) ∘ WithLp.toLp 2) volume = _
  rw [← (PiLp.volume_preserving_toLp (Fin n)).map_eq,
    Measure.map_map (by fun_prop) (PiLp.volume_preserving_toLp (Fin n)).measurable]

theorem polynomialDecay_affine_pullback_le {n d : ℕ} (q : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (u : Ambient n) :
    polynomialDecay q u ≤ (1 + ‖a‖) ^ q * polynomialDecay q (a + L u) := by
  have hnorm : 1 + ‖a + L u‖ ≤ (1 + ‖a‖) * (1 + ‖u‖) := by
    have h := norm_add_le a (L u)
    rw [L.norm_map] at h
    nlinarith [norm_nonneg a, norm_nonneg u, mul_nonneg (norm_nonneg a) (norm_nonneg u)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖a + L u‖) hnorm q
  rw [polynomialDecay, polynomialDecay, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + ‖a + L u‖) ^ q)).mpr
  calc
    _ ≤ ((1 + ‖u‖) ^ q)⁻¹ * ((1 + ‖a‖) * (1 + ‖u‖)) ^ q :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by rw [mul_pow]; field_simp

theorem polynomial_weight_integrable_affine_pullback {n d : ℕ} (q : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ) (hf : Measurable f)
    (hw : Integrable (fun x => |f x| * polynomialDecay q x)
      (coordinatePlaneMeasure (affinePlaneSection a L))) :
    Integrable (fun u : Ambient n => |f (a + L u)| * polynomialDecay q u) := by
  rw [coordinatePlaneMeasure_affine_eq_map] at hw
  have hI := hw.comp_measurable (show Measurable (fun u : Ambient n => a + L u) by fun_prop)
  apply (hI.const_mul ((1 + ‖a‖) ^ q)).mono'
    (((hf.comp (by fun_prop)).abs.mul (polynomialDecay_measurable q)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro u
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (polynomialDecay_nonneg q u))]
  calc
    _ ≤ |f (a + L u)| * ((1 + ‖a‖) ^ q * polynomialDecay q (a + L u)) :=
      mul_le_mul_of_nonneg_left (polynomialDecay_affine_pullback_le q a L u) (abs_nonneg _)
    _ = _ := by ring

theorem exists_intrinsic_height_distribution_from_tail {n d : ℕ} (q : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ) (hf : Measurable f)
    (R : ℝ) (hR : 0 < R)
    (hnear : IntegrableOn f (ball a R) (coordinatePlaneMeasure (affinePlaneSection a L)))
    (hfar : IntegrableOn (fun x => |f x| * inverseDistancePow q a x) (closedExterior a R)
      (coordinatePlaneMeasure (affinePlaneSection a L))) :
    ∃ T : 𝓢'(Ambient n, ℂ), ∀ g : 𝓢(Ambient n, ℂ),
      Integrable (fun u : Ambient n => f (a + L u) • g u) (volume : Measure (Ambient n)) ∧
      T g = ∫ u : Ambient n, f (a + L u) • g u ∂(volume : Measure (Ambient n)) := by
  have hw := polynomial_weight_integrable_from_height_tail q
    (coordinatePlaneMeasure (affinePlaneSection a L)) f hf a R hR hnear hfar
  let F : Ambient n → ℝ := fun u => f (a + L u)
  have hp : Integrable (fun u => |F u| * polynomialDecay q u) (volume : Measure (Ambient n)) :=
    polynomial_weight_integrable_affine_pullback q a L f hf hw
  have hm : Measurable F := hf.comp (show Measurable (fun u : Ambient n => a + L u) by fun_prop)
  refine ⟨heightTemperedDistribution (d := n) (volume : Measure (Ambient n)) F hm q hp, ?_⟩
  intro g
  exact ⟨height_schwartz_integrable (d := n) (volume : Measure (Ambient n)) F hm q hp g,
    heightTemperedDistribution_apply (d := n) (volume : Measure (Ambient n)) F hm q hp g⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_PlanePairingPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem affine_plane_pair_integral {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (A B : Set (Ambient d))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (F : Ambient d × Ambient d → ℝ) :
    (∫ q, F q ∂((coordinatePlaneMeasure (affinePlaneSection a L)).restrict A).prod
      ((coordinatePlaneMeasure (affinePlaneSection a L)).restrict B)) =
    ∫ q : Ambient n × Ambient n, F (a + L q.1, a + L q.2)
      ∂(volume.restrict ((fun u : Ambient n => a + L u) ⁻¹' A)).prod
        (volume.restrict ((fun u : Ambient n => a + L u) ⁻¹' B)) := by
  have he : Isometry (fun u : Ambient n => a + L u) := by
    apply Isometry.of_dist_eq
    intro u v
    simp only [dist_add_left, L.dist_map]
  rw [coordinatePlaneMeasure_affine_eq_map,
    Measure.restrict_map he.continuous.measurable hA,
    Measure.restrict_map he.continuous.measurable hB,
    Measure.map_prod_map _ _ he.continuous.measurable he.continuous.measurable]
  exact (he.isClosedEmbedding.measurableEmbedding.prodMap
    he.isClosedEmbedding.measurableEmbedding).integral_map F

theorem affine_plane_pair_integrable_iff {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (A B : Set (Ambient d))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (F : Ambient d × Ambient d → ℝ) :
    Integrable F (((coordinatePlaneMeasure (affinePlaneSection a L)).restrict A).prod
      ((coordinatePlaneMeasure (affinePlaneSection a L)).restrict B)) ↔
    Integrable (fun q : Ambient n × Ambient n => F (a + L q.1, a + L q.2))
      ((volume.restrict ((fun u : Ambient n => a + L u) ⁻¹' A)).prod
        (volume.restrict ((fun u : Ambient n => a + L u) ⁻¹' B))) := by
  have he : Isometry (fun u : Ambient n => a + L u) := by
    apply Isometry.of_dist_eq
    intro u v
    simp only [dist_add_left, L.dist_map]
  rw [coordinatePlaneMeasure_affine_eq_map,
    Measure.restrict_map he.continuous.measurable hA,
    Measure.restrict_map he.continuous.measurable hB,
    Measure.map_prod_map _ _ he.continuous.measurable he.continuous.measurable]
  exact (he.isClosedEmbedding.measurableEmbedding.prodMap
    he.isClosedEmbedding.measurableEmbedding).integrable_map_iff

theorem fractionalBilinear_affine_pullback {n d : ℕ} (m : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f φ : Ambient d → ℝ) (u v : Ambient n) :
    fractionalBilinear m f φ (a + L u) (a + L v) =
      fractionalBilinear m (fun x => f (a + L x)) (fun x => φ (a + L x)) u v := by
  simp only [fractionalBilinear, dist_add_left, L.dist_map]

theorem renormalizedNormalIntegrand_affine_pullback {n d : ℕ} (m : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f φ : Ambient d → ℝ) (q : Ambient n × Ambient n) :
    renormalizedNormalIntegrand m f φ a (a + L q.1, a + L q.2) =
      renormalizedNormalIntegrand m (fun x => f (a + L x)) (fun x => φ (a + L x)) 0 q := by
  have ha : dist a (a + L q.2) = dist (0 : Ambient n) q.2 := by
    simpa only [map_zero, add_zero] using!
      (show dist (a + L 0) (a + L q.2) = dist (0 : Ambient n) q.2 from by
        rw [dist_add_left, L.dist_map])
  simp only [renormalizedNormalIntegrand, inverseDistancePow, dist_add_left, L.dist_map, ha]

theorem heightPairingOn_affine_pullback {n d : ℕ} (m : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f φ : Ambient d → ℝ) (R : ℝ) :
    heightPairingOn m (coordinatePlaneMeasure (affinePlaneSection a L)) a (ball a R) f φ =
      heightPairingOn m volume (0 : Ambient n) (ball 0 R)
        (fun u => f (a + L u)) (fun u => φ (a + L u)) := by
  have hpre : (fun u : Ambient n => a + L u) ⁻¹' ball a R = ball 0 R := by
    ext u
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero, L.norm_map]
  unfold heightPairingOn
  rw [affine_plane_pair_integral a L (ball a R) (ball a R) measurableSet_ball measurableSet_ball,
    affine_plane_pair_integral a L (ball a R) (ball a R)ᶜ measurableSet_ball measurableSet_ball.compl]
  simp only [preimage_compl, hpre, fractionalBilinear_affine_pullback,
    renormalizedNormalIntegrand_affine_pullback]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BoundedRegionTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem radialUnitCutoff_bounds {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d) :
    0 ≤ radialUnitCutoff a R x ∧ radialUnitCutoff a R x ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem radialUnitCutoff_eq_one {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d)
    (hx : dist x a ≤ R) : radialUnitCutoff a R x = 1 := by
  have h : (1 : ℝ) ≤ R + 1 - dist x a := by linarith
  simp only [radialUnitCutoff, min_eq_left h, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem radialUnitCutoff_support_bound {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d)
    (hx : radialUnitCutoff a R x ≠ 0) : dist x a ≤ R + 1 := by
  by_contra h
  have hneg : R + 1 - dist x a < 0 := by linarith
  have hmin : min 1 (R + 1 - dist x a) ≤ 0 := (min_le_right _ _).trans hneg.le
  exact hx (max_eq_left hmin)

theorem radialUnitCutoff_lipschitz {d : ℕ} (a : Ambient d) (R : ℝ) :
    LipschitzWith 1 (radialUnitCutoff a R) := by
  have h : LipschitzWith 1 (fun x : Ambient d => R + 1 - dist x a) := by
    simpa using! (LipschitzWith.const (R + 1)).sub (LipschitzWith.dist_left a)
  exact (h.const_min 1).const_max 0

theorem radialUnitCutoff_hasCompactSupport {d : ℕ} (a : Ambient d) (R : ℝ) :
    HasCompactSupport (radialUnitCutoff a R) := by
  apply HasCompactSupport.intro (isCompact_closedBall a (R + 1))
  intro x hx
  by_contra h
  exact hx (radialUnitCutoff_support_bound a R x h)

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

theorem schwartz_directional_derivative_integral_zero {d : ℕ}
    (g : 𝓢(Ambient d, ℝ)) (v : Ambient d) :
    (∫ x, ∂_{v} g x) = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : Ambient d => (1 : ℝ)) (g := (g : Ambient d → ℝ)) (v := v)
    (by simp) (by simpa only [one_mul] using! (∂_{v} g).integrable)
    (by simpa only [one_mul] using! g.integrable)
    (fun _ _ => differentiableAt_const _) (fun _ _ => g.differentiableAt)
  simpa only [one_mul, fderiv_const_apply, zero_apply, zero_mul,
    integral_zero, neg_zero, ← lineDerivOp_apply_eq_fderiv] using! h

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

theorem compact_smooth_directional_test_admissible {d : ℕ}
    (g : Ambient d → ℝ) (hc : HasCompactSupport g) (hg : ContDiff ℝ ∞ g)
    (v : Ambient d) :
    ∃ L B : ℝ≥0,
      HasCompactSupport (fun x => fderiv ℝ g x v) ∧
      LipschitzWith L (fun x => fderiv ℝ g x v) ∧
      (∀ x, |fderiv ℝ g x v| ≤ (B : ℝ)) ∧
      Integrable (fun x => fderiv ℝ g x v) ∧
      (∫ x, fderiv ℝ g x v) = 0 := by
  let G := hc.toSchwartzMap hg
  obtain ⟨L, B, hL, hB⟩ := schwartz_real_bounded_lipschitz (∂_{v} G)
  exact ⟨L, B, hc.fderiv_apply ℝ v, hL, hB, (∂_{v} G).integrable,
    schwartz_directional_derivative_integral_zero G v⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_PlaneTestExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact ambient extensions of plane tests

An adjoint coordinate projection extends a test function from an affine plane.
A radial cutoff makes the extension compactly supported while retaining its
values on the plane and explicit uniform and Lipschitz bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Function SchwartzMap
open scoped NNReal ContDiff

theorem exists_compact_ambient_plane_test {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (g : Ambient n → ℝ)
    (hc : HasCompactSupport g) (K B : ℝ≥0) (hg : LipschitzWith K g)
    (hB : ∀ u, |g u| ≤ (B : ℝ)) :
    ∃ (φ : Ambient d → ℝ) (J : ℝ≥0),
      HasCompactSupport φ ∧ LipschitzWith J φ ∧ (∀ x, |φ x| ≤ (B : ℝ)) ∧
      (∀ u, φ (a + L u) = g u) ∧
      Integrable φ (coordinatePlaneMeasure (affinePlaneSection a L)) ∧
      (∫ x, φ x ∂coordinatePlaneMeasure (affinePlaneSection a L)) = ∫ u, g u := by
  obtain ⟨R, _, hR⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : Ambient n)
  let π : Ambient d → Ambient n := fun x => L.toContinuousLinearMap.adjoint (x - a)
  have hπ : LipschitzWith ‖L.toContinuousLinearMap.adjoint‖₊ π := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using!
      L.toContinuousLinearMap.adjoint.lipschitz.dist_le_mul (x - a) (y - a)
  have hleft : ∀ u, π (a + L u) = u := by
    intro u
    change L.toContinuousLinearMap.adjoint ((a + L u) - a) = u
    rw [add_sub_cancel_left]
    exact DFunLike.congr_fun L.adjoint_comp_self u
  let χ := radialUnitCutoff a R
  let φ : Ambient d → ℝ := fun x => χ x * g (π x)
  have hχ : LipschitzWith 1 χ := radialUnitCutoff_lipschitz a R
  have hχB : ∀ x, |χ x| ≤ (1 : ℝ≥0) := by
    intro x
    rw [abs_of_nonneg (radialUnitCutoff_bounds a R x).1]
    exact (radialUnitCutoff_bounds a R x).2
  have hφ : LipschitzWith (1 * (K * ‖L.toContinuousLinearMap.adjoint‖₊) + 1 * B) φ :=
    lipschitz_bounded_product_real hχ (hg.comp hπ) hχB (fun x => hB (π x))
  have hext : ∀ u, φ (a + L u) = g u := by
    intro u
    change χ (a + L u) * g (π (a + L u)) = g u
    rw [hleft]
    by_cases hu : g u = 0
    · rw [hu, mul_zero]
    have hnorm : ‖u‖ ≤ R := by
      simpa only [mem_closedBall, dist_zero_right] using! hR (subset_tsupport g hu)
    have hχone : χ (a + L u) = 1 := by
      apply radialUnitCutoff_eq_one
      simpa only [dist_eq_norm, add_sub_cancel_left, L.norm_map] using! hnorm
    rw [hχone, one_mul]
  refine ⟨φ, _, (radialUnitCutoff_hasCompactSupport a R).mul_right, hφ, ?_, hext, ?_, ?_⟩
  · intro x
    calc
      |φ x| = |χ x| * |g (π x)| := abs_mul _ _
      _ ≤ 1 * (B : ℝ) := mul_le_mul (hχB x) (hB (π x)) (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  · rw [coordinatePlaneMeasure_affine_eq_map]
    apply (integrable_map_measure (μ := (volume : Measure (Ambient n))) hφ.continuous.aestronglyMeasurable
      (show AEMeasurable (fun u : Ambient n => a + L u) volume from (by fun_prop))).mpr
    have hIg : Integrable g (volume : Measure (Ambient n)) :=
      hg.continuous.integrable_of_hasCompactSupport hc
    simpa only [Function.comp_def, hext] using! hIg
  · rw [coordinatePlaneMeasure_affine_eq_map,
      integral_map (show AEMeasurable (fun u : Ambient n => a + L u) volume from (by fun_prop))
        hφ.continuous.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall hext)

theorem exists_compact_ambient_directional_test {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (g : Ambient n → ℝ)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ ∞ g) (v : Ambient n) :
    ∃ (φ : Ambient d → ℝ) (J B : ℝ≥0),
      HasCompactSupport φ ∧ LipschitzWith J φ ∧ (∀ x, |φ x| ≤ (B : ℝ)) ∧
      (∀ u, φ (a + L u) = fderiv ℝ g u v) ∧
      Integrable φ (coordinatePlaneMeasure (affinePlaneSection a L)) ∧
      (∫ x, φ x ∂coordinatePlaneMeasure (affinePlaneSection a L)) = 0 := by
  obtain ⟨K, B, hcompact, hLip, hbound, _, hzero⟩ :=
    compact_smooth_directional_test_admissible g hc hg v
  obtain ⟨φ, J, hcφ, hφ, hBφ, hext, hI, hmean⟩ :=
    exists_compact_ambient_plane_test a L (fun u => fderiv ℝ g u v) hcompact K B hLip hbound
  exact ⟨φ, J, B, hcφ, hφ, hBφ, hext, hI, hmean.trans hzero⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_IntrinsicDirectionalEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set SchwartzMap
open scoped NNReal ContDiff

theorem intrinsic_directional_equation_of_ambient {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ)
    (hambient : ∀ (φ : Ambient d → ℝ) (J B : ℝ≥0),
      HasCompactSupport φ → LipschitzWith J φ → (∀ x, |φ x| ≤ (B : ℝ)) →
      Integrable φ (coordinatePlaneMeasure (affinePlaneSection a L)) →
      (∫ x, φ x ∂coordinatePlaneMeasure (affinePlaneSection a L)) = 0 →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        heightPairingOn n (coordinatePlaneMeasure (affinePlaneSection a L)) a (ball a R) f φ = 0)
    (g : Ambient n → ℝ) (hc : HasCompactSupport g) (hg : ContDiff ℝ ∞ g) (v : Ambient n) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      heightPairingOn n volume (0 : Ambient n) (ball 0 R)
        (fun u => f (a + L u)) (fun u => fderiv ℝ g u v) = 0 := by
  obtain ⟨φ, J, B, hcφ, hφ, hB, hext, hI, hzero⟩ :=
    exists_compact_ambient_directional_test a L g hc hg v
  obtain ⟨R₀, hR₀, hR⟩ := hambient φ J B hcφ hφ hB hI hzero
  refine ⟨R₀, hR₀, fun R hRR => ?_⟩
  have h := hR R hRR
  rw [heightPairingOn_affine_pullback] at h
  have heq : (fun u => φ (a + L u)) = fun u => fderiv ℝ g u v := funext hext
  rwa [heq] at h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_PlaneMeanCorrectionBump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter

theorem radialUnitCutoff_affine_restrict {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (R : ℝ) (u : Ambient n) :
    radialUnitCutoff a R (a + L u) = radialUnitCutoff (0 : Ambient n) R u := by
  simp only [radialUnitCutoff, dist_eq_norm, add_sub_cancel_left, sub_zero, L.norm_map]

theorem radialUnitCutoff_plane_integral_pos {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) :
    0 < ∫ x, radialUnitCutoff a 1 x ∂coordinatePlaneMeasure (affinePlaneSection a L) := by
  have hcont := (radialUnitCutoff_lipschitz (0 : Ambient n) 1).continuous
  have hI : Integrable (radialUnitCutoff (0 : Ambient n) 1) volume :=
    hcont.integrable_of_hasCompactSupport (radialUnitCutoff_hasCompactSupport 0 1)
  have hpos : 0 < ∫ u : Ambient n, radialUnitCutoff 0 1 u :=
    integral_pos_of_integrable_nonneg_nonzero hcont hI
      (fun u => (radialUnitCutoff_bounds 0 1 u).1)
      (show radialUnitCutoff (0 : Ambient n) 1 0 ≠ 0 by norm_num [radialUnitCutoff])
  rw [coordinatePlaneMeasure_affine_eq_map,
    integral_map (show AEMeasurable (fun u : Ambient n => a + L u) volume from (by fun_prop))
      (radialUnitCutoff_lipschitz a 1).continuous.aestronglyMeasurable]
  simpa only [radialUnitCutoff_affine_restrict] using! hpos

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BoundedBoxContainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem ball_subset_boundedProjectionRegion {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e) (H : ℕ) :
    ball (e 0) (planeBoxInnerRadius Q H) ⊆ boundedProjectionRegion π (e 0) K H := by
  intro x hx
  have hH : 0 < (H : ℝ) + 1 := by positivity
  have hden : 0 < (Q : ℝ) + 1 := by positivity
  have hinner : planeBoxInnerRadius Q H ≤ (H : ℝ) + 1 := by
    unfold planeBoxInnerRadius
    apply (div_le_iff₀ hden).mpr
    nlinarith [Q.coe_nonneg]
  have hQinner : (Q : ℝ) * planeBoxInnerRadius Q H < (H : ℝ) + 1 := by
    unfold planeBoxInnerRadius
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hπdist := hπ.dist_le_mul x (e 0)
  rw [hleft 0, dist_zero_right] at hπdist
  have hnorm : ‖π x‖ < (H : ℝ) + 1 :=
    (hπdist.trans (mul_le_mul_of_nonneg_left hx.le Q.coe_nonneg)).trans_lt hQinner
  refine ⟨mem_exhaustionBox_Ioo_of_norm_lt H (π x) hnorm, ?_⟩
  apply mem_ball.mpr
  have hout : (H : ℝ) + 1 ≤ planeBoxOuterRadius K H := by
    unfold planeBoxOuterRadius
    nlinarith [K.coe_nonneg]
  exact hx.trans_le (hinner.trans hout)

theorem eventually_ball_subset_boundedProjectionRegion {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e) (R : ℝ) :
    ∀ᶠ H : ℕ in atTop, ball (e 0) R ⊆ boundedProjectionRegion π (e 0) K H := by
  obtain ⟨H₀, hH₀⟩ := exists_nat_gt (((Q : ℝ) + 1) * R)
  filter_upwards [eventually_ge_atTop H₀] with H hH
  have hH' : (H₀ : ℝ) ≤ H := by exact_mod_cast hH
  have hR : R ≤ planeBoxInnerRadius Q H := by
    unfold planeBoxInnerRadius
    apply (le_div_iff₀ (by positivity : 0 < (Q : ℝ) + 1)).mpr
    nlinarith
  exact (ball_subset_ball hR).trans (ball_subset_boundedProjectionRegion e π K Q hπ hleft H)

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_UniformBallMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem uniform_ball_moments_from_box_moments {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ℕ) (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (μ : ℕ → Measure (Ambient d)) (C : ℝ) (hg : ∀ j, GlobalUpperGrowth m C (μ j))
    (w : ℕ → Ambient d → ℝ)
    (hw : ∀ H j, MemLp (w j) 2 ((μ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B : ℕ → ℝ)
    (hB : ∀ H j, (∫ x, w j x ^ 2 ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B H)
    (R : ℝ) (hR : 0 < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j,
      ((μ j).restrict (ball (e 0) R)).real univ ≤ M ∧
      MemLp (w j) 2 ((μ j).restrict (ball (e 0) R)) ∧
      (∫ x in ball (e 0) R, w j x ^ 2 ∂μ j) ≤ M := by
  obtain ⟨H, hH⟩ := (eventually_ball_subset_boundedProjectionRegion e π K Q hπ hleft R).exists
  let M := max 0 (max (C * R ^ m) (B H))
  refine ⟨M, le_max_left _ _, fun j => ⟨?_, ?_, ?_⟩⟩
  · exact (ball_restriction_mass_bound m C (μ j) (hg j) (e 0) R hR).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact MemLp.mono_measure (Measure.restrict_mono hH le_rfl) (hw H j)
  · calc
      _ ≤ ∫ x, w j x ^ 2 ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H) :=
        integral_mono_measure (Measure.restrict_mono hH le_rfl)
          (Eventually.of_forall (fun x => sq_nonneg (w j x))) (hw H j).integrable_sq
      _ ≤ B H := hB H j
      _ ≤ M := (le_max_right _ _).trans (le_max_right _ _)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_MeanCorrectionAdmissible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal CompactlySupported

theorem compact_meanCorrection_admissible {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (hlocal : CompactTestConvergence μ ν)
    (φ η : Ambient d → ℝ) (Lφ Lη Bφ Bη : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hη : LipschitzWith Lη η)
    (hcφ : HasCompactSupport φ) (hcη : HasCompactSupport η)
    (hBφ : ∀ x, |φ x| ≤ (Bφ : ℝ)) (hBη : ∀ x, |η x| ≤ (Bη : ℝ))
    (hmean : (∫ x, φ x ∂ν) = 0) (hbump : (∫ x, η x ∂ν) ≠ 0) :
    Tendsto (fun j => (∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)) atTop (𝓝 0) ∧
      ∀ᶠ j in atTop,
        (∫ x, η x ∂μ j) ≠ 0 ∧
        Integrable (meanCorrection (μ j) φ η) (μ j) ∧
        (∫ x, meanCorrection (μ j) φ η x ∂μ j) = 0 ∧
        LipschitzWith (Lφ + Lη) (meanCorrection (μ j) φ η) ∧
        (∀ x, |meanCorrection (μ j) φ η x| ≤ ((Bφ + Bη : ℝ≥0) : ℝ)) ∧
        HasCompactSupport (meanCorrection (μ j) φ η) := by
  have hφlim := hlocal (⟨⟨φ, hφ.continuous⟩, hcφ⟩ : C_c(Ambient d, ℝ))
  have hηlim := hlocal (⟨⟨η, hη.continuous⟩, hcη⟩ : C_c(Ambient d, ℝ))
  change Tendsto (fun j => ∫ x, φ x ∂μ j) atTop (𝓝 (∫ x, φ x ∂ν)) at hφlim
  change Tendsto (fun j => ∫ x, η x ∂μ j) atTop (𝓝 (∫ x, η x ∂ν)) at hηlim
  rw [hmean] at hφlim
  have hc := meanCorrection_coefficient_tendsto_zero μ φ η _ hbump hφlim hηlim
  refine ⟨hc, ?_⟩
  have hcabs : Tendsto (fun j => |(∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, norm_zero] using! hc.norm
  filter_upwards [hηlim.eventually (eventually_ne_nhds hbump),
    hcabs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with j hηne hcoef
  have hiφ : Integrable φ (μ j) := hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hiη : Integrable η (μ j) := hη.continuous.integrable_of_hasCompactSupport hcη
  refine ⟨hηne, meanCorrection_integrable (μ j) φ η hiφ hiη,
    meanCorrection_integral_zero (μ j) φ η hiφ hiη hηne, ?_, ?_, ?_⟩
  · apply (meanCorrection_lipschitz (μ j) hφ hη).weaken
    apply add_le_add le_rfl
    have hcNN : ‖(∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)‖₊ ≤ 1 := by
      apply NNReal.coe_le_coe.mp
      simpa only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one] using! hcoef.le
    simpa only [one_mul] using! mul_le_mul_of_nonneg_right hcNN (zero_le)
  · intro x
    unfold meanCorrection
    calc
      _ ≤ |φ x| + |(∫ y, φ y ∂μ j) / (∫ y, η y ∂μ j)| * |η x| := by
        simpa only [sub_zero, zero_sub, abs_neg, abs_mul] using! abs_sub_le (φ x) 0
          (((∫ y, φ y ∂μ j) / (∫ y, η y ∂μ j)) * η x)
      _ ≤ (Bφ : ℝ) + 1 * (Bη : ℝ) :=
        add_le_add (hBφ x) (mul_le_mul hcoef.le (hBη x) (abs_nonneg _) (by norm_num))
      _ = _ := by rw [one_mul, NNReal.coe_add]
  · exact hcφ.sub hcη.mul_left

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LocalTestMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local moments of bounded tests

Compact support makes products of mean-corrected tests with continuous height
functions integrable. Local mass and square-integrability bounds then control
the absolute moments of bounded tests and their height-weighted products.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal

theorem meanCorrection_height_product_integrable {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (φ η w : Ambient d → ℝ) (hφ : Continuous φ) (hη : Continuous η) (hw : Continuous w)
    (hcφ : HasCompactSupport φ) (hcη : HasCompactSupport η) :
    Integrable (fun x => meanCorrection μ φ η x * w x) μ := by
  have hc : HasCompactSupport (meanCorrection μ φ η) := hcφ.sub hcη.mul_left
  exact ((hφ.sub (continuous_const.mul hη)).mul hw).integrable_of_hasCompactSupport hc.mul_right

theorem bounded_test_local_moment_bounds {d : ℕ}
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (w φ : Ambient d → ℝ) (hw : MemLp w 2 ν) (hφm : Measurable φ)
    (B : ℝ≥0) (hB : ∀ x, |φ x| ≤ (B : ℝ))
    (M : ℝ) (hM : 0 ≤ M) (hmass : ν.real univ ≤ M) (hsecond : (∫ x, w x ^ 2 ∂ν) ≤ M) :
    Integrable φ ν ∧ Integrable (fun x => φ x * w x) ν ∧
      (∫ x, |φ x| ∂ν) ≤ (B : ℝ) * M ∧ (∫ x, |φ x * w x| ∂ν) ≤ (B : ℝ) * M := by
  have hφL2 : MemLp φ 2 ν := MemLp.of_bound hφm.aestronglyMeasurable (B : ℝ)
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hB x)
  have hiφ := hφL2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hprod : MemLp (fun x => φ x * w x) 1 ν := MeasureTheory.MemLp.mul (hφ := hφL2) (hf := hw)
  have hiprod := memLp_one_iff_integrable.mp hprod
  refine ⟨hiφ, hiprod, ?_, ?_⟩
  · calc
      _ ≤ ∫ _, (B : ℝ) ∂ν := integral_mono_ae hiφ.abs (integrable_const _)
        (Eventually.of_forall hB)
      _ = (B : ℝ) * ν.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass B.coe_nonneg
  · have hwI := hw.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hwB : (∫ x, |w x| ∂ν) ≤ M := by
      simpa only [one_pow, mul_one] using! integral_abs_le_of_mass_second_moment ν w hw
        M 1 hM (by norm_num) hmass (by simpa only [one_pow, mul_one] using! hsecond)
    calc
      _ ≤ ∫ x, (B : ℝ) * |w x| ∂ν := by
        apply integral_mono_ae hiprod.abs (hwI.abs.const_mul (B : ℝ))
        exact Eventually.of_forall fun x => by
          change |φ x * w x| ≤ (B : ℝ) * |w x|
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
      _ = (B : ℝ) * (∫ x, |w x| ∂ν) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hwB B.coe_nonneg

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_OuterPairingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem outerPairRadius_ge (R : ℝ) (k : ℕ) : R ≤ outerPairRadius R k := by
  unfold outerPairRadius
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem outerPairRadius_pos (R : ℝ) (hR : 0 < R) (k : ℕ) : 0 < outerPairRadius R k :=
  hR.trans_le (outerPairRadius_ge R k)

theorem integral_outer_pair_exhaustion {d : ℕ} (ρ : Measure (Ambient d × Ambient d))
    (a : Ambient d) (R : ℝ) (F : Ambient d × Ambient d → ℝ) (hF : Integrable F ρ) :
    Tendsto (fun k : ℕ => ∫ q in univ ×ˢ ball a (outerPairRadius R k), F q ∂ρ)
      atTop (𝓝 (∫ q, F q ∂ρ)) := by
  let s := fun k : ℕ => (univ : Set (Ambient d)) ×ˢ ball a (outerPairRadius R k)
  have hs (k : ℕ) : MeasurableSet (s k) := MeasurableSet.univ.prod measurableSet_ball
  have hmono : Monotone s := by
    intro k l hkl q hq
    refine ⟨hq.1, ?_⟩
    apply (ball_subset_ball ?_) hq.2
    unfold outerPairRadius
    have hkl' : (k : ℝ) ≤ l := by exact_mod_cast hkl
    linarith
  have hcover : (⋃ k, s k) = univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨k, hk⟩ := exists_nat_gt (dist q.2 a - R)
    apply mem_iUnion.mpr
    refine ⟨k, mem_univ _, ?_⟩
    change dist q.2 a < R + (k : ℝ) + 1
    linarith
  have ht := tendsto_setIntegral_of_monotone hs hmono hF.restrict
  simpa only [hcover, Measure.restrict_univ] using! ht

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_PairingLocalizationIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independence of Riesz pairing localization

Exhaustion by outer balls recovers the scalar Riesz pairing from finite restrictions.
For compactly supported mean-zero Lipschitz tests, the resulting pairing is independent
of the localization center and radius satisfying the support separation bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem ball_subset_outer_of_radius_dist {d : ℕ} (a b : Ambient d) (R T : ℝ)
    (h : R + dist a b ≤ T) : ball a R ⊆ ball b T := by
  intro x hx
  change dist x b < T
  change dist x a < R at hx
  have ht := dist_triangle x a b
  linarith

theorem restrict_nested_balls_of_subset {d : ℕ} (μ : Measure (Ambient d))
    (a b : Ambient d) (R T : ℝ) (hsub : ball a R ⊆ ball b T) :
    (μ.restrict (ball b T)).restrict (ball a R) = μ.restrict (ball a R) := by
  rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr hsub]

theorem rieszScalarPairing_restrict_outer_ball {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a b : Ambient d) (R T : ℝ)
    (hsub : ball a R ⊆ ball b T) (e : Ambient d) (φ : Ambient d → ℝ) :
    rieszScalarPairing m (μ.restrict (ball b T)) a R e φ =
      (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) +
      ∫ q in univ ×ˢ ball b T, rieszFarIntegrand m e φ a q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)) := by
  have hcomm : (μ.restrict (ball b T)).restrict (closedExterior a R) =
      (μ.restrict (closedExterior a R)).restrict (ball b T) := by
    rw [Measure.restrict_restrict (closedExterior_measurable a R),
      Measure.restrict_restrict measurableSet_ball, inter_comm]
  have hprod : (μ.restrict (ball a R)).prod ((μ.restrict (closedExterior a R)).restrict (ball b T)) =
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))).restrict (univ ×ˢ ball b T) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  unfold rieszScalarPairing
  dsimp only
  rw [restrict_nested_balls_of_subset μ a b R T hsub, hcomm, hprod]

theorem rieszScalarPairing_outer_limit_at_center {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a b : Ambient d) (R T₀ : ℝ)
    (hcontain : R + dist a b ≤ T₀) (e : Ambient d) (φ : Ambient d → ℝ)
    (hfar : Integrable (rieszFarIntegrand m e φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)))) :
    Tendsto (fun k : ℕ => rieszScalarPairing m (μ.restrict (ball b (outerPairRadius T₀ k))) a R e φ)
      atTop (𝓝 (rieszScalarPairing m μ a R e φ)) := by
  have ht := integral_outer_pair_exhaustion
    ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))) b T₀
    (rieszFarIntegrand m e φ a) hfar
  have heq : (fun k : ℕ => rieszScalarPairing m (μ.restrict (ball b (outerPairRadius T₀ k))) a R e φ) =
      fun k => (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) +
      ∫ q in univ ×ˢ ball b (outerPairRadius T₀ k), rieszFarIntegrand m e φ a q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)) := by
    funext k
    exact rieszScalarPairing_restrict_outer_ball m μ a b R _
      (ball_subset_outer_of_radius_dist a b R _ (hcontain.trans (outerPairRadius_ge T₀ k))) e φ
  rw [heq]
  exact tendsto_const_nhds.add ht

theorem mean_zero_restrict_of_support {d : ℕ} (μ : Measure (Ambient d))
    (φ : Ambient d → ℝ) (a : Ambient d) (R : ℝ)
    (hsupport : ∀ x ∉ ball a R, φ x = 0) (hzero : (∫ x, φ x ∂μ) = 0) :
    (∫ x in ball a R, φ x ∂μ) = 0 :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hsupport).trans hzero

theorem rieszScalarPairing_localization_independent {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a b : Ambient d) (H J R S : ℝ) (hH : 0 ≤ H) (hJ : 0 ≤ J)
    (hR : 0 < R) (hS : 0 < S) (hHR : 2 * H ≤ R) (hJS : 2 * J ≤ S)
    (hsupportA : ∀ x, φ x ≠ 0 → dist x a ≤ H)
    (hsupportB : ∀ x, φ x ≠ 0 → dist x b ≤ J)
    (hzero : (∫ x, φ x ∂μ) = 0) :
    rieszScalarPairing (p + 1) μ a R e φ = rieszScalarPairing (p + 1) μ b S e φ := by
  let T₀ := R + S + dist a b
  have hcontainA : R + dist a a ≤ T₀ := by dsimp [T₀]; rw [dist_self]; have := dist_nonneg (x := a) (y := b); linarith
  have hcontainB : S + dist b a ≤ T₀ := by dsimp [T₀]; rw [dist_comm b a]; linarith
  have hfarA := rieszFarIntegrand_integrable_of_compact_lipschitz (p + 1) C μ hg e φ L hφ a H R hH hR hHR hsupportA
  have hfarB := rieszFarIntegrand_integrable_of_compact_lipschitz (p + 1) C μ hg e φ L hφ b J S hJ hS hJS hsupportB
  have hlimA := rieszScalarPairing_outer_limit_at_center (p + 1) μ a a R T₀ hcontainA e φ hfarA
  have hlimB := rieszScalarPairing_outer_limit_at_center (p + 1) μ b a S T₀ hcontainB e φ hfarB
  have hφzeroA : ∀ x ∉ ball a R, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupportA x hn).trans_lt (by linarith : H < R))
  have hφzeroB : ∀ x ∉ ball b S, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupportB x hn).trans_lt (by linarith : J < S))
  have heq : (fun k : ℕ => rieszScalarPairing (p + 1) (μ.restrict (ball a (outerPairRadius T₀ k))) a R e φ) =
      fun k => rieszScalarPairing (p + 1) (μ.restrict (ball a (outerPairRadius T₀ k))) b S e φ := by
    funext k
    let T := outerPairRadius T₀ k
    let ν := μ.restrict (ball a T)
    have hRT₀ : R ≤ T₀ := by simpa only [dist_self, add_zero] using! hcontainA
    have hRT : R ≤ T := hRT₀.trans (outerPairRadius_ge T₀ k)
    have hT : 0 < T := hR.trans_le hRT
    have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a T hT
    have hφI : Integrable φ ν := (lipschitz_height_memLp_on_ball (p + 1) C μ hg φ L hφ a T hT).integrable (by norm_num)
    have hzeroν : (∫ x, φ x ∂ν) = 0 := mean_zero_restrict_of_support μ φ a T
      (fun x hx => hφzeroA x (fun hin => hx ((ball_subset_ball hRT) hin))) hzero
    have hF := rieszInteriorIntegrand_integrable_of_lipschitz p C ν
      (globalGrowth_restrict (p + 1) C μ hg (ball a T)) e φ L hφ (2 * T) (by positivity)
      (ball_restriction_pair_diameter μ a T)
    have hA := (finite_pairing_eq_renormalized (p + 1) e ν a R hR φ hφI hφzeroA
      (mean_zero_restrict_of_support ν φ a R hφzeroA hzeroν) hF).2
    have hB := (finite_pairing_eq_renormalized (p + 1) e ν b S hS φ hφI hφzeroB
      (mean_zero_restrict_of_support ν φ b S hφzeroB hzeroν) hF).2
    exact hA.symm.trans hB
  rw [← heq] at hlimB
  exact tendsto_nhds_unique hlimA hlimB

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_OscillationTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem tsupport_subset_ball_of_support_bound {d : ℕ}
    (φ : Ambient d → ℝ) (a : Ambient d) (H A : ℝ) (hHA : H < A)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) : tsupport φ ⊆ ball a A := by
  have hclosed : tsupport φ ⊆ closedBall a H := by
    change closure (Function.support φ) ⊆ closedBall a H
    exact isClosed_closedBall.closure_subset_iff.mpr (fun x hx => hsupport x hx)
  intro x hx
  exact (hclosed hx).trans_lt hHA

theorem ScalarOscillationBound.lipschitz_test_bound {d : ℕ}
    (m : ℕ) (μ : Measure (Ambient d)) (a : Ambient d) (A v : ℝ)
    (hosc : ScalarOscillationBound m μ a A v) (e : Ambient d) (he : ‖e‖ ≤ 1)
    (φ : Ambient d → ℝ) (D : ℝ≥0) (hφ : LipschitzWith D φ)
    (hsupport : tsupport φ ⊆ ball a A) (hzero : (∫ x, φ x ∂μ) = 0) :
    |rieszScalarPairing m μ a (2 * A) e φ| ≤ ((D : ℝ) + 1) * v := by
  let c : ℝ := (D : ℝ) + 1
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hscaled := lipschitz_const_mul_real hφ c⁻¹
  have hcoef : ‖c⁻¹‖₊ * D ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
    rw [abs_of_pos (inv_pos.mpr hc)]
    have hDc : (D : ℝ) ≤ c := by dsimp [c] <;> linarith
    calc
      c⁻¹ * (D : ℝ) = (D : ℝ) / c := by ring
      _ ≤ 1 := (div_le_one hc).mpr hDc
  have hzero' : (∫ x, c⁻¹ * φ x ∂μ) = 0 := by rw [integral_const_mul, hzero, mul_zero]
  have hb := hosc e he (fun x => c⁻¹ * φ x) (hscaled.weaken hcoef)
    (tsupport_mul_subset_right.trans hsupport) hzero'
  rw [rieszScalarPairing_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hc)] at hb
  calc
    |rieszScalarPairing m μ a (2 * A) e φ| = c * (c⁻¹ * |rieszScalarPairing m μ a (2 * A) e φ|) := by
      field_simp
    _ ≤ c * v := mul_le_mul_of_nonneg_left hb hc.le

theorem oscillation_bound_for_localized_test {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (a : Ambient d) (A v : ℝ) (hA : 0 < A) (hosc : ScalarOscillationBound (p + 1) μ a A v)
    (e : Ambient d) (he : ‖e‖ ≤ 1) (φ : Ambient d → ℝ) (D : ℝ≥0) (hφ : LipschitzWith D φ)
    (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R) (hHA : H < A)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) (hzero : (∫ x, φ x ∂μ) = 0) :
    |rieszScalarPairing (p + 1) μ a R e φ| ≤ ((D : ℝ) + 1) * v := by
  have hsupport' : ∀ x, φ x ≠ 0 → dist x a ≤ A := fun x hx => (hsupport x hx).trans hHA.le
  have heq := rieszScalarPairing_localization_independent p C μ hg e φ D hφ a a H A R (2 * A)
    hH hA.le hR (by positivity) hHR le_rfl hsupport hsupport' hzero
  rw [heq]
  exact hosc.lipschitz_test_bound (p + 1) μ a A v e he φ D hφ
    (tsupport_subset_ball_of_support_bound φ a H A hHA hsupport) hzero

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SupportedExteriorPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Supported exterior pairings

Support in a measurable subset allows the left factor of a product measure to be
restricted without changing integrability or the integral. These identities bound
the absolute renormalized pairing over a complement by its exterior integral when
the original set contains a ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

theorem prod_restrict_left_subset {d : ℕ} (μ η : Measure (Ambient d))
    [SFinite μ] [SFinite η]
    (A s : Set (Ambient d)) (hA : MeasurableSet A) (hAs : A ⊆ s) :
    ((μ.restrict s).prod η).restrict (A ×ˢ univ) = (μ.restrict A).prod η := by
  rw [← Measure.prod_restrict, Measure.restrict_univ,
    Measure.restrict_restrict hA, inter_eq_left.mpr hAs]

theorem integrable_prod_iff_of_left_support {d : ℕ} (μ η : Measure (Ambient d))
    [SFinite μ] [SFinite η]
    (A s : Set (Ambient d)) (hA : MeasurableSet A) (hAs : A ⊆ s)
    (F : Ambient d × Ambient d → ℝ) (hzero : ∀ q, q.1 ∉ A → F q = 0) :
    Integrable F ((μ.restrict s).prod η) ↔ Integrable F ((μ.restrict A).prod η) := by
  have hsupp : support F ⊆ A ×ˢ univ := by
    intro q hq
    refine ⟨?_, mem_univ _⟩
    by_contra h
    exact hq (hzero q h)
  have h := integrableOn_iff_integrable_of_support_subset
    (μ := (μ.restrict s).prod η) hsupp
  rw [IntegrableOn, prod_restrict_left_subset μ η A s hA hAs] at h
  exact h.symm

theorem integral_prod_eq_of_left_support {d : ℕ} (μ η : Measure (Ambient d))
    [SFinite μ] [SFinite η]
    (A s : Set (Ambient d)) (hA : MeasurableSet A) (hAs : A ⊆ s)
    (F : Ambient d × Ambient d → ℝ) (hzero : ∀ q, q.1 ∉ A → F q = 0) :
    (∫ q, F q ∂(μ.restrict s).prod η) = ∫ q, F q ∂(μ.restrict A).prod η := by
  have h : (∫ q in A ×ˢ univ, F q ∂(μ.restrict s).prod η) =
      ∫ q, F q ∂(μ.restrict s).prod η := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    apply hzero q
    intro h
    exact hq ⟨h, mem_univ _⟩
  rw [prod_restrict_left_subset μ η A s hA hAs] at h
  exact h.symm

theorem renormalized_pairing_complement_bound {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a : Ambient d) (R : ℝ)
    (A s : Set (Ambient d)) (hA : MeasurableSet A) (hAs : A ⊆ s)
    (hcontain : ball a R ⊆ s) (w φ : Ambient d → ℝ)
    (hφzero : ∀ x ∉ A, φ x = 0)
    (houter : Integrable (renormalizedNormalIntegrand m w φ a)
      ((μ.restrict A).prod (μ.restrict (closedExterior a R)))) :
    Integrable (renormalizedNormalIntegrand m w φ a) ((μ.restrict s).prod (μ.restrict sᶜ)) ∧
      (∫ q, |renormalizedNormalIntegrand m w φ a q| ∂(μ.restrict s).prod (μ.restrict sᶜ)) ≤
        ∫ q, |renormalizedNormalIntegrand m w φ a q|
          ∂(μ.restrict A).prod (μ.restrict (closedExterior a R)) := by
  have hzero : ∀ q : Ambient d × Ambient d, q.1 ∉ A →
      renormalizedNormalIntegrand m w φ a q = 0 := by
    intro q hq
    simp only [renormalizedNormalIntegrand, hφzero q.1 hq, zero_mul]
  have hsub : sᶜ ⊆ closedExterior a R := by
    rw [closedExterior_eq_compl_ball]
    exact compl_subset_compl.mpr hcontain
  have hmeas : (μ.restrict A).prod (μ.restrict sᶜ) ≤
      (μ.restrict A).prod (μ.restrict (closedExterior a R)) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    exact Measure.restrict_mono (Set.prod_mono subset_rfl hsub) le_rfl
  refine ⟨(integrable_prod_iff_of_left_support μ (μ.restrict sᶜ) A s hA hAs
    _ hzero).mpr (houter.mono_measure hmeas), ?_⟩
  rw [integral_prod_eq_of_left_support μ (μ.restrict sᶜ) A s hA hAs
    (fun q => |renormalizedNormalIntegrand m w φ a q|) (by
      intro q hq
      rw [hzero q hq, abs_zero])]
  exact integral_mono_measure hmeas (Eventually.of_forall fun _ => abs_nonneg _) houter.abs

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_HeightPairingOuterLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Outer exhaustion and localization of the height pairing

Restricting to expanding outer balls leaves the local bilinear term unchanged
and exhausts the integrable renormalized far term. Equality of the finite-region
pairings then passes to the limit, proving independence of the localization
region for the same supported, mean-zero test function.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

theorem restrict_set_inside_ball {d : ℕ} (μ : Measure (Ambient d))
    (s : Set (Ambient d)) (hs : MeasurableSet s) (a : Ambient d) (T : ℝ)
    (hsub : s ⊆ ball a T) : (μ.restrict (ball a T)).restrict s = μ.restrict s := by
  rw [Measure.restrict_restrict hs, inter_eq_left.mpr hsub]

theorem heightPairingOn_restrict_outer_ball {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a : Ambient d)
    (s : Set (Ambient d)) (hs : MeasurableSet s) (T : ℝ) (hsub : s ⊆ ball a T)
    (w φ : Ambient d → ℝ) :
    heightPairingOn m (μ.restrict (ball a T)) a s w φ =
      (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m w φ q.1 q.2
        ∂(μ.restrict s).prod (μ.restrict s)) +
      ∫ q in univ ×ˢ ball a T, renormalizedNormalIntegrand m w φ a q
        ∂(μ.restrict s).prod (μ.restrict sᶜ) := by
  have hcomm : (μ.restrict (ball a T)).restrict sᶜ = (μ.restrict sᶜ).restrict (ball a T) := by
    rw [Measure.restrict_restrict hs.compl, Measure.restrict_restrict measurableSet_ball, inter_comm]
  have hprod : (μ.restrict s).prod ((μ.restrict sᶜ).restrict (ball a T)) =
      ((μ.restrict s).prod (μ.restrict sᶜ)).restrict (univ ×ˢ ball a T) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  unfold heightPairingOn
  rw [restrict_set_inside_ball μ s hs a T hsub, hcomm, hprod]

theorem heightPairingOn_outer_limit {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a : Ambient d)
    (s : Set (Ambient d)) (hs : MeasurableSet s) (T₀ : ℝ) (hsub : s ⊆ ball a T₀)
    (w φ : Ambient d → ℝ)
    (hfar : Integrable (renormalizedNormalIntegrand m w φ a) ((μ.restrict s).prod (μ.restrict sᶜ))) :
    Tendsto (fun k => heightPairingOn m (μ.restrict (ball a (outerPairRadius T₀ k))) a s w φ)
      atTop (𝓝 (heightPairingOn m μ a s w φ)) := by
  have ht := integral_outer_pair_exhaustion ((μ.restrict s).prod (μ.restrict sᶜ)) a T₀
    (renormalizedNormalIntegrand m w φ a) hfar
  have heq : (fun k => heightPairingOn m (μ.restrict (ball a (outerPairRadius T₀ k))) a s w φ) =
      fun k => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m w φ q.1 q.2
        ∂(μ.restrict s).prod (μ.restrict s)) +
      ∫ q in univ ×ˢ ball a (outerPairRadius T₀ k), renormalizedNormalIntegrand m w φ a q
        ∂(μ.restrict s).prod (μ.restrict sᶜ) := by
    funext k
    exact heightPairingOn_restrict_outer_ball m μ a s hs _
      (hsub.trans (ball_subset_ball (outerPairRadius_ge T₀ k))) w φ
  rw [heq]
  exact tendsto_const_nhds.add ht

theorem center_height_integrable_finite_region {d : ℕ} (m : ℕ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (w : Ambient d → ℝ) (hw : Integrable w ν)
    (a : Ambient d) (r : ℝ) (hr : 0 < r) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hcontain : ball a r ⊆ s) :
    IntegrableOn (fun y => w y * inverseDistancePow (m + 1) a y) sᶜ ν := by
  apply hw.restrict.mul_bdd (inverseDistancePow_measurable (m + 1) a).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hs.compl] with y hy
  have hd : r ≤ dist a y := by
    by_contra h
    exact hy (hcontain (by simpa only [mem_ball, dist_comm] using! (lt_of_not_ge h)))
  rw [Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  simpa only [inverseDistancePow, one_div] using!
    one_div_le_one_div_of_le (pow_pos hr (m + 1)) (pow_le_pow_left₀ hr.le hd (m + 1))

theorem heightPairingOn_localization_independent {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasureOnCompacts μ] (a : Ambient d)
    (s t : Set (Ambient d)) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (r T₀ : ℝ) (hr : 0 < r) (hins : ball a r ⊆ s) (hint : ball a r ⊆ t)
    (hsout : s ⊆ ball a T₀) (htout : t ⊆ ball a T₀)
    (w φ : Ambient d → ℝ) (hφ : Integrable φ μ)
    (hφs : ∀ x ∉ s, φ x = 0) (hφt : ∀ x ∉ t, φ x = 0) (hzero : (∫ x, φ x ∂μ) = 0)
    (hw : ∀ k, Integrable w (μ.restrict (ball a (outerPairRadius T₀ k))))
    (hF : ∀ k, Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2)
      ((μ.restrict (ball a (outerPairRadius T₀ k))).prod
        (μ.restrict (ball a (outerPairRadius T₀ k)))))
    (hfarS : Integrable (renormalizedNormalIntegrand m w φ a) ((μ.restrict s).prod (μ.restrict sᶜ)))
    (hfarT : Integrable (renormalizedNormalIntegrand m w φ a) ((μ.restrict t).prod (μ.restrict tᶜ))) :
    heightPairingOn m μ a s w φ = heightPairingOn m μ a t w φ := by
  have hlimS := heightPairingOn_outer_limit m μ a s hs T₀ hsout w φ hfarS
  have hlimT := heightPairingOn_outer_limit m μ a t ht T₀ htout w φ hfarT
  have heq : (fun k => heightPairingOn m (μ.restrict (ball a (outerPairRadius T₀ k))) a s w φ) =
      fun k => heightPairingOn m (μ.restrict (ball a (outerPairRadius T₀ k))) a t w φ := by
    funext k
    let T := outerPairRadius T₀ k
    let ν := μ.restrict (ball a T)
    let : IsFiniteMeasure ν := ⟨by
      simpa only [ν, Measure.restrict_apply_univ] using!
        (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a T).measure_lt_top⟩
    have hsubS : s ⊆ ball a T := hsout.trans (ball_subset_ball (outerPairRadius_ge T₀ k))
    have hsubT : t ⊆ ball a T := htout.trans (ball_subset_ball (outerPairRadius_ge T₀ k))
    have hzS : (∫ x in s, φ x ∂ν) = 0 := by
      rw [show ν.restrict s = μ.restrict s from restrict_set_inside_ball μ s hs a T hsubS]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero hφs).trans hzero
    have hzT : (∫ x in t, φ x ∂ν) = 0 := by
      rw [show ν.restrict t = μ.restrict t from restrict_set_inside_ball μ t ht a T hsubT]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero hφt).trans hzero
    have hS := (finite_height_pairing_eq_renormalized m w φ ν a s hs hφ.restrict hφs hzS
      (center_height_integrable_finite_region m ν w (hw k) a r hr s hs hins) (hF k)).2
    have hT := (finite_height_pairing_eq_renormalized m w φ ν a t ht hφ.restrict hφt hzT
      (center_height_integrable_finite_region m ν w (hw k) a r hr t ht hint) (hF k)).2
    exact hS.symm.trans hT
  rw [heq] at hlimS
  exact tendsto_nhds_unique hlimS hlimT

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RegionOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Oscillation bounds on localized regions

Lipschitz height functions give integrable far pairings on regions containing a
ball. Localization identifies each such height pairing with the scalar Riesz
pairing, transferring its oscillation estimate to the normalized height.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem region_far_integrable_of_lipschitz_height {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (A s : Set (Ambient d)) (hA : MeasurableSet A) [IsFiniteMeasure (μ.restrict A)]
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hAR : A ⊆ ball a R) (hcontain : ball a R ⊆ s)
    (u φ : Ambient d → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u) (hφm : Measurable φ)
    (hφ : Integrable φ (μ.restrict A)) (hφu : Integrable (fun x => φ x * u x) (μ.restrict A))
    (hzero : ∀ x ∉ A, φ x = 0) (hnear : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    Integrable (renormalizedNormalIntegrand m u φ a) ((μ.restrict s).prod (μ.restrict sᶜ)) := by
  obtain ⟨hi, hb⟩ := weighted_height_closed_tail_bound m C μ hg u K hu a R hR
  have houter := (renormalized_far_pairing_integrable_and_bound m C μ (μ.restrict A) hg u φ
    hu.continuous.measurable hφm hφ hφu a H R hH hR hHR
    (Eventually.of_forall hnear) hi _ hb).1
  exact (renormalized_pairing_complement_bound m μ a R A s hA (hAR.trans hcontain)
    hcontain u φ hzero houter).1

theorem heightPairingOn_region_eq_riesz {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    (hg : GlobalUpperGrowth (p + 1) C μ) (e : Ambient d) (u φ : Ambient d → ℝ)
    (K L : ℝ≥0) (hu : LipschitzWith K u) (hφ : LipschitzWith L φ)
    (hdiff : ∀ x y, u x - u y = inner ℝ e (x - y))
    (a : Ambient d) (H R T : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hRT : R ≤ T) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hins : ball a R ⊆ s) (hout : s ⊆ ball a T)
    (hφI : Integrable φ μ) (hzero : (∫ x, φ x ∂μ) = 0)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H)
    (hfar : Integrable (renormalizedNormalIntegrand (p + 1) u φ a)
      ((μ.restrict s).prod (μ.restrict sᶜ))) :
    heightPairingOn (p + 1) μ a s u φ = rieszScalarPairing (p + 1) μ a R e φ := by
  have hφball : ∀ x ∉ ball a R, φ x = 0 := by
    intro x hx
    by_contra h
    exact hx ((hsupport x h).trans_lt (by linarith : H < R))
  have hφs : ∀ x ∉ s, φ x = 0 := fun x hx => hφball x (fun hin => hx (hins hin))
  have hmean : (∫ x in ball a R, φ x ∂μ) = 0 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hφball).trans hzero
  let ν := μ.restrict (ball a R)
  let : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
  have huφ : Integrable (fun x => φ x * u x) ν := by
    have hprod : MemLp (fun x => φ x * u x) 1 ν :=
      MeasureTheory.MemLp.mul (hφ := (lipschitz_height_memLp_on_ball (p + 1) C μ hg φ L hφ a R hR))
        (hf := (lipschitz_height_memLp_on_ball (p + 1) C μ hg u K hu a R hR))
    exact memLp_one_iff_integrable.mp hprod
  obtain ⟨hweight, hweightBound⟩ := weighted_height_closed_tail_bound (p + 1) C μ hg u K hu a R hR
  have hballFar := (renormalized_far_pairing_integrable_and_bound (p + 1) C μ ν hg u φ
    hu.continuous.measurable hφ.continuous.measurable hφI.restrict huφ a H R hH hR hHR
    (Eventually.of_forall hsupport) hweight _ hweightBound).1
  have hw : ∀ k, Integrable u (μ.restrict (ball a (outerPairRadius T k))) := by
    intro k
    have hT : 0 < outerPairRadius T k := hR.trans_le (hRT.trans (outerPairRadius_ge T k))
    let := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a _ hT
    exact (lipschitz_height_memLp_on_ball (p + 1) C μ hg u K hu a _ hT).integrable (by norm_num)
  have hF : ∀ k, Integrable (fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) u φ q.1 q.2)
      ((μ.restrict (ball a (outerPairRadius T k))).prod (μ.restrict (ball a (outerPairRadius T k)))) := by
    intro k
    let T' := outerPairRadius T k
    have hT' : 0 < T' := hR.trans_le (hRT.trans (outerPairRadius_ge T k))
    let := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a T' hT'
    have hi := rieszInteriorIntegrand_integrable_of_lipschitz p C (μ.restrict (ball a T'))
      (globalGrowth_restrict (p + 1) C μ hg (ball a T')) e φ L hφ (2 * T') (by positivity)
      (ball_restriction_pair_diameter μ a T')
    have heq : rieszInteriorIntegrand (p + 1) e φ =
        fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) u φ q.1 q.2 :=
      funext (rieszInteriorIntegrand_eq_fractionalBilinear (p + 1) e u φ hdiff)
    rwa [heq] at hi
  have hballFar' : Integrable (renormalizedNormalIntegrand (p + 1) u φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (ball a R)ᶜ)) := by
    rwa [← closedExterior_eq_compl_ball]
  have heq := heightPairingOn_localization_independent (p + 1) μ a s (ball a R)
    hs measurableSet_ball R T hR hins subset_rfl hout (ball_subset_ball hRT)
    u φ hφI hφs hφball hzero hw hF hfar hballFar'
  exact heq.trans (heightPairingOn_ball_eq_rieszScalarPairing (p + 1) C μ hg e u φ hdiff
    a R hR hφI.restrict hmean hballFar)

theorem normalized_region_pairing_oscillation_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    (hg : GlobalUpperGrowth (p + 1) C μ) (e : Ambient d) (he : ‖e‖ ≤ 1)
    (u φ : Ambient d → ℝ) (K L : ℝ≥0) (hu : LipschitzWith K u) (hφ : LipschitzWith L φ)
    (hdiff : ∀ x y, u x - u y = inner ℝ e (x - y))
    (a : Ambient d) (H R T A v δ : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hRT : R ≤ T) (hHA : H < A) (hδ : 0 < δ)
    (hosc : ScalarOscillationBound (p + 1) μ a A v)
    (s : Set (Ambient d)) (hs : MeasurableSet s) (hins : ball a R ⊆ s) (hout : s ⊆ ball a T)
    (hφI : Integrable φ μ) (hzero : (∫ x, φ x ∂μ) = 0)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H)
    (hfar : Integrable (renormalizedNormalIntegrand (p + 1) u φ a)
      ((μ.restrict s).prod (μ.restrict sᶜ))) :
    |heightPairingOn (p + 1) μ a s (fun x => u x / δ) φ| ≤ ((L : ℝ) + 1) * (v / δ) := by
  rw [heightPairingOn_height_div, heightPairingOn_region_eq_riesz p C μ hg e u φ K L hu hφ
    hdiff a H R T hH hR hHR hRT s hs hins hout hφI hzero hsupport hfar,
    abs_div, abs_of_pos hδ]
  have hb := oscillation_bound_for_localized_test p C μ hg a A v (by linarith) hosc e he φ L hφ
    H R hH hR hHR hHA hsupport hzero
  exact (div_le_div_of_nonneg_right hb hδ.le).trans_eq (by ring)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ShiftedHeightTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Height tails after a dyadic shift

Rescaling the initial radius reindexes the dyadic annuli. Applying the weighted
height-tail estimate at this shifted radius yields a geometric decay term and a
Lipschitz-controlled far tail for the normalized height.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem dyadicAnnulus_shift {d : ℕ} (a : Ambient d) (R : ℝ) (ℓ k : ℕ) :
    dyadicAnnulus a (R * 2 ^ ℓ) k = dyadicAnnulus a R (ℓ + k) := by
  ext y
  simp only [dyadicAnnulus, mem_ofPred_eq, pow_add, mul_assoc]

theorem normalized_weighted_height_tail_shifted {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N ℓ : ℕ) (hℓ : ℓ ≤ N)
    (δ b W : ℝ) (hδ : 0 < δ) (hb0 : 0 ≤ b) (hb2 : b < 2) (hW : |w a| ≤ W)
    (hsecond : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    IntegrableOn (fun y => |w y / δ| * inverseDistancePow (m + 2) a y)
      (closedExterior a (R * 2 ^ ℓ)) μ ∧
      (∫ y in closedExterior a (R * 2 ^ ℓ), |w y / δ| * inverseDistancePow (m + 2) a y ∂μ) ≤
        (B / R) / (1 - b / 2) * (b / 2) ^ ℓ +
          (((K : ℝ) + W / R) * (2 * (C * 2 ^ m))) * ((R * 2 ^ N)⁻¹ / δ) := by
  have hshift : ∀ k < N - ℓ,
      (∫ y in dyadicAnnulus a (R * 2 ^ ℓ) k, w y ^ 2 ∂μ) ≤
        (B * ((R * 2 ^ ℓ) * 2 ^ k) ^ m) *
          ((δ * b ^ ℓ) * ((R * 2 ^ ℓ) * 2 ^ k) * b ^ k) ^ 2 := by
    intro k hk
    rw [dyadicAnnulus_shift]
    have h := hsecond (ℓ + k) (by omega)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    simp only [pow_add, mul_pow]
    ring
  obtain ⟨hi, hb⟩ := improved_weighted_height_tail_bound m C B μ hg hCB w K hw a
    (R * 2 ^ ℓ) (by positivity) (N - ℓ) (δ * b ^ ℓ) b (by positivity) hb0 hb2 hshift
  have hrad : (R * 2 ^ ℓ) * 2 ^ (N - ℓ) = R * (2 : ℝ) ^ N := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hℓ]
  rw [hrad] at hb
  have heq : (fun y => |w y / δ| * inverseDistancePow (m + 2) a y) =
      (fun y => (|w y| * inverseDistancePow (m + 2) a y) / δ) := by
    funext y
    rw [abs_div, abs_of_pos hδ]
    ring
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hi.div_const δ
  · rw [heq, integral_div]
    have hden : 0 < 1 - b / 2 := by linarith
    have hmain : ((B * (δ * b ^ ℓ) / (R * 2 ^ ℓ)) / (1 - b / 2)) / δ =
        (B / R) / (1 - b / 2) * (b / 2) ^ ℓ := by
      rw [div_pow]
      field_simp
    have hTpos : 0 < R * (2 : ℝ) ^ N := by positivity
    have hRT : R ≤ R * (2 : ℝ) ^ N := by
      simpa only [mul_one] using! mul_le_mul_of_nonneg_left
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
    have hW0 : 0 ≤ W := (abs_nonneg _).trans hW
    have hcenter : |w a| / (R * 2 ^ N) ≤ W / R :=
      (div_le_div_of_nonneg_right hW hTpos.le).trans
        (div_le_div_of_nonneg_left hW0 hR hRT)
    have htail : (((K : ℝ) + |w a| / (R * 2 ^ N)) * (2 * (C * 2 ^ m / (R * 2 ^ N)))) / δ ≤
        (((K : ℝ) + W / R) * (2 * (C * 2 ^ m))) * ((R * 2 ^ N)⁻¹ / δ) := by
      calc
        _ ≤ (((K : ℝ) + W / R) * (2 * (C * 2 ^ m / (R * 2 ^ N)))) / δ :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (add_le_add le_rfl hcenter) (by positivity [hg.1])) hδ.le
        _ = _ := by ring
    calc
      _ ≤ ((B * (δ * b ^ ℓ) / (R * 2 ^ ℓ)) / (1 - b / 2) +
        ((K : ℝ) + |w a| / (R * 2 ^ N)) * (2 * (C * 2 ^ m / (R * 2 ^ N)))) / δ :=
          div_le_div_of_nonneg_right hb hδ.le
      _ = (B / R) / (1 - b / 2) * (b / 2) ^ ℓ +
        (((K : ℝ) + |w a| / (R * 2 ^ N)) * (2 * (C * 2 ^ m / (R * 2 ^ N)))) / δ := by
          rw [add_div, hmain]
      _ ≤ _ := add_le_add le_rfl htail

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalizedExteriorPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem normalized_far_pairing_bound_shifted {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasure ν]
    (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (u φ : Ambient d → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u)
    (hφm : Measurable φ) (hφ : Integrable φ ν)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hnear : ∀ᵐ x ∂ν, φ x ≠ 0 → dist x a ≤ H)
    (N ℓ : ℕ) (hℓ : ℓ ≤ N) (δ b W P : ℝ)
    (hδ : 0 < δ) (hb0 : 0 ≤ b) (hb2 : b < 2) (hW : |u a| ≤ W)
    (hφu : Integrable (fun x => φ x * (u x / δ)) ν)
    (hPφ : (∫ x, |φ x| ∂ν) ≤ P) (hPu : (∫ x, |φ x * (u x / δ)| ∂ν) ≤ P)
    (hsecond : ∀ k < N, (∫ y in dyadicAnnulus a R k, u y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    Integrable (renormalizedNormalIntegrand m (fun x => u x / δ) φ a)
      (ν.prod (μ.restrict (closedExterior a (R * 2 ^ ℓ)))) ∧
      (∫ q, |renormalizedNormalIntegrand m (fun x => u x / δ) φ a q|
        ∂ν.prod (μ.restrict (closedExterior a (R * 2 ^ ℓ)))) ≤
        normalizedExteriorBound m C B H R b K W P ℓ ((R * 2 ^ N)⁻¹ / δ) := by
  obtain ⟨hweight, hZ⟩ := normalized_weighted_height_tail_shifted m C B μ hg hCB u K hu
    a R hR N ℓ hℓ δ b W hδ hb0 hb2 hW hsecond
  let Z := (B / R) / (1 - b / 2) * (b / 2) ^ ℓ +
    (((K : ℝ) + W / R) * (2 * (C * 2 ^ m))) * ((R * 2 ^ N)⁻¹ / δ)
  have hZ0 : 0 ≤ Z := (integral_nonneg (fun _ =>
    mul_nonneg (abs_nonneg _) (inverseDistancePow_nonneg _ _ _))).trans hZ
  have hRℓ : 0 < R * (2 : ℝ) ^ ℓ := by positivity
  have hRle : R ≤ R * (2 : ℝ) ^ ℓ := by
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
  obtain ⟨hi, hb⟩ := renormalized_far_pairing_integrable_and_bound m C μ ν hg
    (fun x => u x / δ) φ (hu.continuous.measurable.div_const δ) hφm hφ hφu
    a H (R * 2 ^ ℓ) hH hRℓ (hHR.trans hRle) hnear hweight Z hZ
  refine ⟨hi, hb.trans ?_⟩
  calc
    _ ≤ 2 ^ (m + 1) * (P * (2 * (C * 2 ^ m / (R * 2 ^ ℓ)))) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) * (P * Z) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hPu (by positivity [hg.1])) (by positivity)
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hPφ hZ0) (by positivity)
    _ = _ := by
      have hhalf : ((2 : ℝ) ^ ℓ)⁻¹ = (1 / 2 : ℝ) ^ ℓ := by rw [one_div, inv_pow]
      have hbase : 2 * (C * 2 ^ m / (R * 2 ^ ℓ)) =
          (2 * (C * 2 ^ m / R)) * (1 / 2 : ℝ) ^ ℓ := by
        rw [div_eq_mul_inv, mul_inv_rev, hhalf]
        ring
      rw [hbase]
      unfold normalizedExteriorBound Z
      ring

theorem normalized_far_pairings_vanish {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ ν : ℕ → Measure (Ambient d)) [∀ j, SFinite (μ j)] [∀ j, IsFiniteMeasure (ν j)]
    (hg : ∀ j, GlobalUpperGrowth m C (μ j)) (hCB : C * 2 ^ m ≤ B)
    (u φ : ℕ → Ambient d → ℝ) (K : ℝ≥0) (hu : ∀ j, LipschitzWith K (u j))
    (hφm : ∀ j, Measurable (φ j)) (hφ : ∀ j, Integrable (φ j) (ν j))
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hnear : ∀ j, ∀ᵐ x ∂ν j, φ j x ≠ 0 → dist x a ≤ H)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j)
    (b W P : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2) (hW : ∀ j, |u j a| ≤ W)
    (hφu : ∀ j, Integrable (fun x => φ j x * (u j x / δ j)) (ν j))
    (hPφ : ∀ᶠ j in atTop, (∫ x, |φ j x| ∂ν j) ≤ P)
    (hPu : ∀ᶠ j in atTop, (∫ x, |φ j x * (u j x / δ j)| ∂ν j) ≤ P)
    (hlast : Tendsto (fun j => (R * (2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsecond : ∀ j k, k < N j → (∫ y in dyadicAnnulus a R k, u j y ^ 2 ∂μ j) ≤
      (B * (R * 2 ^ k) ^ m) * (δ j * (R * 2 ^ k) * b ^ k) ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ ℓ : ℕ, ∀ᶠ j in atTop,
      Integrable (renormalizedNormalIntegrand m (fun x => u j x / δ j) (φ j) a)
        ((ν j).prod ((μ j).restrict (closedExterior a (R * 2 ^ ℓ)))) ∧
      (∫ q, |renormalizedNormalIntegrand m (fun x => u j x / δ j) (φ j) a q|
        ∂(ν j).prod ((μ j).restrict (closedExterior a (R * 2 ^ ℓ)))) < ε := by
  intro ε hε
  let A₀ := 2 ^ (m + 1) * (P * (2 * (C * 2 ^ m / R)))
  let A₁ := ((m + 1 : ℝ) * 2 ^ (m + 2) * H) * (P * ((B / R) / (1 - b / 2)))
  let A₂ := ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
    (P * (((K : ℝ) + W / R) * (2 * (C * 2 ^ m))))
  have hg₀ := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul A₀
  have hg₁ := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ b / 2)
    (by linarith : b / 2 < 1)).const_mul A₁
  have hgeom : Tendsto (fun ℓ : ℕ => A₀ * (1 / 2 : ℝ) ^ ℓ + A₁ * (b / 2) ^ ℓ) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using! hg₀.add hg₁
  obtain ⟨ℓ, hℓ⟩ := (hgeom.eventually (gt_mem_nhds (half_pos hε))).exists
  refine ⟨ℓ, ?_⟩
  have hrem : Tendsto (fun j => A₂ * ((R * (2 : ℝ) ^ N j)⁻¹ / δ j)) atTop (𝓝 0) := by
    simpa only [mul_zero] using! hlast.const_mul A₂
  filter_upwards [hN.eventually (eventually_ge_atTop ℓ), hrem.eventually (gt_mem_nhds (half_pos hε)),
    hPφ, hPu] with j hjN hjrem hjPφ hjPu
  obtain ⟨hi, hb⟩ := normalized_far_pairing_bound_shifted m C B (μ j) (ν j) (hg j) hCB
    (u j) (φ j) K (hu j) (hφm j) (hφ j) a H R hH hR hHR (hnear j)
    (N j) ℓ hjN (δ j) b W P (hδ j) hb0 hb2 (hW j) (hφu j) hjPφ hjPu (hsecond j)
  refine ⟨hi, hb.trans_lt ?_⟩
  change A₀ * (1 / 2 : ℝ) ^ ℓ + A₁ * (b / 2) ^ ℓ + A₂ * ((R * 2 ^ N j)⁻¹ / δ j) < ε
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RegionTailDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem normalized_region_tails_vanish {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, SFinite (μ j)]
    (A : Set (Ambient d)) (hA : MeasurableSet A) [∀ j, IsFiniteMeasure ((μ j).restrict A)]
    (s : ℕ → Set (Ambient d)) (a : Ambient d)
    (hcontain : ∀ r : ℝ, ∀ᶠ H in atTop, ball a r ⊆ s H)
    (hg : ∀ j, GlobalUpperGrowth m C (μ j)) (hCB : C * 2 ^ m ≤ B)
    (u φ : ℕ → Ambient d → ℝ) (K : ℝ≥0) (hu : ∀ j, LipschitzWith K (u j))
    (hφm : ∀ j, Measurable (φ j)) (hφ : ∀ j, Integrable (φ j) ((μ j).restrict A))
    (hφzero : ∀ j x, x ∉ A → φ j x = 0)
    (H₀ R : ℝ) (hH₀ : 0 ≤ H₀) (hR : 0 < R) (hHR : 2 * H₀ ≤ R) (hAR : A ⊆ ball a R)
    (hnear : ∀ j, ∀ᵐ x ∂(μ j).restrict A, φ j x ≠ 0 → dist x a ≤ H₀)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j)
    (b W P : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2) (hW : ∀ j, |u j a| ≤ W)
    (hφu : ∀ j, Integrable (fun x => φ j x * (u j x / δ j)) ((μ j).restrict A))
    (hPφ : ∀ᶠ j in atTop, (∫ x in A, |φ j x| ∂μ j) ≤ P)
    (hPu : ∀ᶠ j in atTop, (∫ x in A, |φ j x * (u j x / δ j)| ∂μ j) ≤ P)
    (hlast : Tendsto (fun j => (R * (2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsecond : ∀ j k, k < N j → (∫ y in dyadicAnnulus a R k, u j y ^ 2 ∂μ j) ≤
      (B * (R * 2 ^ k) ^ m) * (δ j * (R * 2 ^ k) * b ^ k) ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ H in atTop, ∀ᶠ j in atTop,
      Integrable (renormalizedNormalIntegrand m (fun x => u j x / δ j) (φ j) a)
        (((μ j).restrict (s H)).prod ((μ j).restrict (s H)ᶜ)) ∧
      (∫ q, |renormalizedNormalIntegrand m (fun x => u j x / δ j) (φ j) a q|
        ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H)ᶜ)) < ε := by
  intro ε hε
  obtain ⟨ℓ, hℓ⟩ := normalized_far_pairings_vanish m C B μ (fun j => (μ j).restrict A)
    hg hCB u φ K hu hφm hφ a H₀ R hH₀ hR hHR hnear N hN δ hδ b W P hb0 hb2 hW
    hφu hPφ hPu hlast hsecond ε hε
  have hRle : R ≤ R * (2 : ℝ) ^ ℓ := by
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
  filter_upwards [hcontain (R * 2 ^ ℓ)] with H hH
  filter_upwards [hℓ] with j hj
  obtain ⟨hi, hb⟩ := renormalized_pairing_complement_bound m (μ j) a (R * 2 ^ ℓ) A (s H) hA
    (hAR.trans ((ball_subset_ball hRle).trans hH)) hH
    (fun x => u j x / δ j) (φ j) (hφzero j) hj.1
  exact ⟨hi, hb.trans_lt hj.2⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CorrectedSingularTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

theorem fractionalBilinear_test_sub {d : ℕ} (m : ℕ) (w φ η : Ambient d → ℝ)
    (c : ℝ) (x y : Ambient d) :
    fractionalBilinear m w (fun z => φ z - c * η z) x y =
      fractionalBilinear m w φ x y - c * fractionalBilinear m w η x y := by
  unfold fractionalBilinear
  ring

theorem fractionalBilinear_integral_test_sub {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (w φ η : Ambient d → ℝ) (c : ℝ)
    (hφ : Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2)
      (μ.prod μ))
    (hη : Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w η q.1 q.2)
      (μ.prod μ)) :
    (∫ q : Ambient d × Ambient d, fractionalBilinear m w (fun z => φ z - c * η z) q.1 q.2
      ∂μ.prod μ) =
      (∫ q : Ambient d × Ambient d, fractionalBilinear m w φ q.1 q.2 ∂μ.prod μ) -
      c * (∫ q : Ambient d × Ambient d, fractionalBilinear m w η q.1 q.2 ∂μ.prod μ) := by
  simp only [fractionalBilinear_test_sub]
  rw [integral_sub hφ (hη.const_mul c), integral_const_mul]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CorrectedLocalLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

theorem globally_corrected_local_singular_limit {d : ℕ} (m : ℕ)
    (μ : ℕ → Measure (Ambient d)) (s : Set (Ambient d))
    (w : ℕ → Ambient d → ℝ) (φ η : Ambient d → ℝ)
    (hc : Tendsto (fun j => (∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)) atTop (𝓝 0))
    (hφ : ∀ j, Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m (w j) φ q.1 q.2)
      (((μ j).restrict s).prod ((μ j).restrict s)))
    (hη : ∀ j, Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m (w j) η q.1 q.2)
      (((μ j).restrict s).prod ((μ j).restrict s)))
    (P Q : ℝ)
    (hP : Tendsto (fun j => ∫ q : Ambient d × Ambient d, fractionalBilinear m (w j) φ q.1 q.2
      ∂((μ j).restrict s).prod ((μ j).restrict s)) atTop (𝓝 P))
    (hQ : Tendsto (fun j => ∫ q : Ambient d × Ambient d, fractionalBilinear m (w j) η q.1 q.2
      ∂((μ j).restrict s).prod ((μ j).restrict s)) atTop (𝓝 Q)) :
    Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      fractionalBilinear m (w j) (meanCorrection (μ j) φ η) q.1 q.2
      ∂((μ j).restrict s).prod ((μ j).restrict s)) atTop (𝓝 P) := by
  have heq : ∀ j, (∫ q : Ambient d × Ambient d,
      fractionalBilinear m (w j) (meanCorrection (μ j) φ η) q.1 q.2
        ∂((μ j).restrict s).prod ((μ j).restrict s)) =
      (∫ q : Ambient d × Ambient d, fractionalBilinear m (w j) φ q.1 q.2
        ∂((μ j).restrict s).prod ((μ j).restrict s)) -
        ((∫ x, φ x ∂μ j) / (∫ x, η x ∂μ j)) *
          (∫ q : Ambient d × Ambient d, fractionalBilinear m (w j) η q.1 q.2
            ∂((μ j).restrict s).prod ((μ j).restrict s)) := by
    intro j
    exact fractionalBilinear_integral_test_sub m ((μ j).restrict s) (w j) φ η _ (hφ j) (hη j)
  simp only [heq]
  simpa only [zero_mul, sub_zero] using! hP.sub (hc.mul hQ)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_LimitingHeightEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

theorem limiting_height_equation_of_local_limits {d : ℕ} (m : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (a : Ambient d) (s : ℕ → Set (Ambient d))
    (w φ : ℕ → Ambient d → ℝ) (f ψ : Ambient d → ℝ)
    (hlocal : ∀ H, Tendsto
      (fun j => ∫ q : Ambient d × Ambient d, fractionalBilinear m (w j) (φ j) q.1 q.2
        ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H))) atTop
      (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear m f ψ q.1 q.2
        ∂(ν.restrict (s H)).prod (ν.restrict (s H)))))
    (error : ℕ → ℝ) (herror : Tendsto error atTop (𝓝 0))
    (hsmall : ∀ᶠ H in atTop, ∀ᶠ j in atTop,
      |heightPairingOn m (μ j) a (s H) (w j) (φ j)| ≤ error j)
    (htail : ∀ ε : ℝ, 0 < ε → ∀ᶠ H in atTop, ∀ᶠ j in atTop,
      (∫ q, |renormalizedNormalIntegrand m (w j) (φ j) a q|
        ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H)ᶜ)) < ε) :
    Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear m f ψ q.1 q.2 ∂(ν.restrict (s H)).prod (ν.restrict (s H))))
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  have htail' := htail (ε / 3) hthird
  have herror' := herror.eventually (gt_mem_nhds hthird)
  have hfinal : ∀ᶠ H in atTop,
      dist ((1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m f ψ q.1 q.2
        ∂(ν.restrict (s H)).prod (ν.restrict (s H)))) 0 < ε := by
    filter_upwards [hsmall, htail'] with H hHsmall hHtail
    have hlim : Tendsto (fun j => |(1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
        fractionalBilinear m (w j) (φ j) q.1 q.2
          ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H)))|) atTop
        (𝓝 (|(1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m f ψ q.1 q.2
          ∂(ν.restrict (s H)).prod (ν.restrict (s H)))|)) := by
      simpa only [Real.norm_eq_abs] using! ((hlocal H).const_mul (1 / 2 : ℝ)).norm
    have hbound : ∀ᶠ j in atTop, |(1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
        fractionalBilinear m (w j) (φ j) q.1 q.2
          ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H)))| ≤ 2 * ε / 3 := by
      filter_upwards [hHsmall, hHtail, herror'] with j hj hjtail hjerror
      let I := (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
        fractionalBilinear m (w j) (φ j) q.1 q.2
          ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H)))
      let F := ∫ q, renormalizedNormalIntegrand m (w j) (φ j) a q
        ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H)ᶜ)
      have hF : |F| < ε / 3 := by
        apply lt_of_le_of_lt _ hjtail
        simpa only [Real.norm_eq_abs] using! norm_integral_le_integral_norm
          (renormalizedNormalIntegrand m (w j) (φ j) a)
      change |I + F| ≤ error j at hj
      have hI : |I| ≤ |I + F| + |F| := by
        have h := abs_add_le (I + F) (-F)
        rw [show I + F + -F = I by ring, abs_neg] at h
        exact h
      change |I| ≤ 2 * ε / 3
      linarith
    have hlimit := le_of_tendsto hlim hbound
    rw [Real.dist_eq, sub_zero]
    linarith
  exact eventually_atTop.mp hfinal

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CorrectedRieszLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Corrected Riesz limiting equation

Mean-corrected compact tests connect the local bilinear limits to the Riesz
oscillation estimates. Together with the normalized height tail bounds, this
shows that the limiting fractional pairing vanishes along the region exhaustion.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem corrected_riesz_limiting_equation {d : ℕ} (p : ℕ) (C B : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, SFinite (μ j)] [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (hweak : CompactTestConvergence μ ν)
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j)) (hCB : C * 2 ^ (p + 1) ≤ B)
    (a : Ambient d) (s : ℕ → Set (Ambient d)) (hs : ∀ H, MeasurableSet (s H))
    (hcontain : ∀ r : ℝ, ∀ᶠ H in atTop, ball a r ⊆ s H)
    (H₀ R : ℝ) (hH₀ : 0 ≤ H₀) (hR : 0 < R) (hHR : 2 * H₀ ≤ R)
    (T : ℕ → ℝ) (hRT : ∀ H, R ≤ T H) (hout : ∀ H, s H ⊆ ball a (T H))
    (u : ℕ → Ambient d → ℝ) (K : ℝ≥0) (hu : ∀ j, LipschitzWith K (u j))
    (e : ℕ → Ambient d) (he : ∀ j, ‖e j‖ ≤ 1)
    (hdiff : ∀ j x y, u j x - u j y = inner ℝ (e j) (x - y))
    (δ A v : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) a (A j) (v j))
    (hratio : Tendsto (fun j => v j / δ j) atTop (𝓝 0))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (b W : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2) (hW : ∀ j, |u j a| ≤ W)
    (hlast : Tendsto (fun j => (R * (2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsecond : ∀ j k, k < N j → (∫ y in dyadicAnnulus a R k, u j y ^ 2 ∂μ j) ≤
      (B * (R * 2 ^ k) ^ (p + 1)) * (δ j * (R * 2 ^ k) * b ^ k) ^ 2)
    (M : ℝ) (hM : 0 ≤ M)
    (hmass : ∀ j, ((μ j).restrict (ball a R)).real univ ≤ M)
    (hL2 : ∀ j, MemLp (fun x => u j x / δ j) 2 ((μ j).restrict (ball a R)))
    (hsecondLocal : ∀ j, (∫ x in ball a R, (u j x / δ j) ^ 2 ∂μ j) ≤ M)
    (hwI : ∀ H j, Integrable (fun x => u j x / δ j) ((μ j).restrict (s H)))
    (henergy : ∀ H j, Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2)
      (((μ j).restrict (s H)).prod ((μ j).restrict (s H))))
    (f φ η : Ambient d → ℝ) (Lφ Lη Bφ Bη : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hη : LipschitzWith Lη η)
    (hcφ : HasCompactSupport φ) (hcη : HasCompactSupport η)
    (hBφ : ∀ x, |φ x| ≤ (Bφ : ℝ)) (hBη : ∀ x, |η x| ≤ (Bη : ℝ))
    (hφsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H₀)
    (hηsupport : ∀ x, η x ≠ 0 → dist x a ≤ H₀)
    (hmean : (∫ x, φ x ∂ν) = 0) (hbump : (∫ x, η x ∂ν) ≠ 0)
    (hlimitφ : ∀ H, Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) (fun x => u j x / δ j) φ q.1 q.2
        ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H))) atTop
      (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) f φ q.1 q.2
        ∂(ν.restrict (s H)).prod (ν.restrict (s H)))))
    (hlimitη : ∀ H, Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) (fun x => u j x / δ j) η q.1 q.2
        ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H))) atTop
      (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) f η q.1 q.2
        ∂(ν.restrict (s H)).prod (ν.restrict (s H))))) :
    Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) f φ q.1 q.2 ∂(ν.restrict (s H)).prod (ν.restrict (s H))))
      atTop (𝓝 0) := by
  let ξ := fun j => meanCorrection (μ j) φ η
  let w := fun j x => u j x / δ j
  let (j : ℕ) : IsFiniteMeasure ((μ j).restrict (ball a R)) :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C (μ j) (hg j) a R hR
  let (H j : ℕ) : IsFiniteMeasure ((μ j).restrict (s H)) := ⟨by
    have hi := (isCompact_closedBall a (T H)).measure_lt_top (μ := μ j)
    simpa only [Measure.restrict_apply_univ] using!
      (measure_mono ((hout H).trans ball_subset_closedBall)).trans_lt hi⟩
  obtain ⟨hc, hadmissible⟩ := compact_meanCorrection_admissible μ ν hweak φ η Lφ Lη Bφ Bη
    hφ hη hcφ hcη hBφ hBη hmean hbump
  have hξcont : ∀ j, Continuous (ξ j) :=
    fun j => (meanCorrection_lipschitz (μ j) hφ hη).continuous
  have hξI : ∀ j, Integrable (ξ j) (μ j) := fun j => meanCorrection_integrable (μ j) φ η
    (hφ.continuous.integrable_of_hasCompactSupport hcφ)
    (hη.continuous.integrable_of_hasCompactSupport hcη)
  have hξnear : ∀ j x, ξ j x ≠ 0 → dist x a ≤ H₀ := by
    intro j x hx
    by_contra h
    have hφx : φ x = 0 := by by_contra hn; exact h (hφsupport x hn)
    have hηx : η x = 0 := by by_contra hn; exact h (hηsupport x hn)
    exact hx (by simp only [ξ, meanCorrection, hφx, hηx, mul_zero, sub_zero])
  have hξzero : ∀ j x, x ∉ ball a R → ξ j x = 0 := by
    intro j x hx
    by_contra hn
    exact hx ((hξnear j x hn).trans_lt (by linarith : H₀ < R))
  have hξu : ∀ j, Integrable (fun x => ξ j x * u j x) (μ j) := fun j =>
    meanCorrection_height_product_integrable (μ j) φ η (u j)
      hφ.continuous hη.continuous (hu j).continuous hcφ hcη
  have hξw : ∀ j, Integrable (fun x => ξ j x * w j x) (μ j) := fun j =>
    meanCorrection_height_product_integrable (μ j) φ η (w j)
      hφ.continuous hη.continuous ((hu j).continuous.div_const (δ j)) hcφ hcη
  let P := ((Bφ + Bη : ℝ≥0) : ℝ) * M
  have hmoments : ∀ᶠ j in atTop,
      (∫ x in ball a R, |ξ j x| ∂μ j) ≤ P ∧
      (∫ x in ball a R, |ξ j x * w j x| ∂μ j) ≤ P := by
    filter_upwards [hadmissible] with j hj
    exact (bounded_test_local_moment_bounds ((μ j).restrict (ball a R)) (w j) (ξ j) (hL2 j)
      (hξcont j).measurable (Bφ + Bη) hj.2.2.2.2.1 M hM (hmass j) (hsecondLocal j)).2.2
  have htail := normalized_region_tails_vanish (p + 1) C B μ (ball a R) measurableSet_ball
    s a hcontain hg hCB u ξ K hu (fun j => (hξcont j).measurable) (fun j => (hξI j).restrict)
    hξzero H₀ R hH₀ hR hHR subset_rfl (fun j => Eventually.of_forall (hξnear j))
    N hN δ hδ b W P hb0 hb2 hW (fun j => (hξw j).restrict)
    (hmoments.mono fun _ h => h.1) (hmoments.mono fun _ h => h.2) hlast hsecond
  have hcorrectedLimits : ∀ H, Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) (w j) (ξ j) q.1 q.2
        ∂((μ j).restrict (s H)).prod ((μ j).restrict (s H))) atTop
      (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) f φ q.1 q.2
        ∂(ν.restrict (s H)).prod (ν.restrict (s H)))) := by
    intro H
    apply globally_corrected_local_singular_limit (p + 1) μ (s H) w φ η hc
    · intro j
      exact (fractional_bilinear_integrable_and_cap_error p C ((μ j).restrict (s H))
        (globalGrowth_restrict (p + 1) C (μ j) (hg j) (s H)) (w j) φ
        ((hu j).continuous.div_const (δ j)).measurable (hwI H j) Lφ Bφ hφ hBφ
        (henergy H j) 1 (by norm_num)).1
    · intro j
      exact (fractional_bilinear_integrable_and_cap_error p C ((μ j).restrict (s H))
        (globalGrowth_restrict (p + 1) C (μ j) (hg j) (s H)) (w j) η
        ((hu j).continuous.div_const (δ j)).measurable (hwI H j) Lη Bη hη hBη
        (henergy H j) 1 (by norm_num)).1
    · exact hlimitφ H
    · exact hlimitη H
  let error := fun j => (((Lφ + Lη : ℝ≥0) : ℝ) + 1) * (v j / δ j)
  have herror : Tendsto error atTop (𝓝 0) := by
    simpa only [mul_zero] using! hratio.const_mul (((Lφ + Lη : ℝ≥0) : ℝ) + 1)
  have hsmall : ∀ᶠ H in atTop, ∀ᶠ j in atTop,
      |heightPairingOn (p + 1) (μ j) a (s H) (w j) (ξ j)| ≤ error j := by
    filter_upwards [hcontain R] with H hH
    filter_upwards [hadmissible, hA.eventually (eventually_gt_atTop H₀)] with j hj hjA
    have hfar := region_far_integrable_of_lipschitz_height (p + 1) C (μ j) (hg j)
      (ball a R) (s H) measurableSet_ball a H₀ R hH₀ hR hHR subset_rfl hH
      (u j) (ξ j) K (hu j) (hξcont j).measurable (hξI j).restrict (hξu j).restrict
      (hξzero j) (hξnear j)
    exact normalized_region_pairing_oscillation_bound p C (μ j) (hg j) (e j) (he j)
      (u j) (ξ j) K (Lφ + Lη) (hu j) hj.2.2.2.1 (hdiff j) a H₀ R (T H) (A j) (v j) (δ j)
      hH₀ hR hHR (hRT H) hjA (hδ j) (hosc j) (s H) (hs H) hH (hout H)
      (hξI j) hj.2.2.1 (hξnear j) hfar
  exact limiting_height_equation_of_local_limits (p + 1) μ ν a s w ξ f φ hcorrectedLimits
    error herror hsmall (fun ε hε => (htail ε hε).mono fun _ h => h.mono fun _ hj => hj.2)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_HeightPairingExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

theorem integral_outer_regions_exhaustion {d : ℕ}
    (ρ : Measure (Ambient d × Ambient d)) (a : Ambient d) (s : ℕ → Set (Ambient d))
    (hs : ∀ H, MeasurableSet (s H))
    (hcontain : ∀ R : ℝ, ∀ᶠ H in atTop, ball a R ⊆ s H)
    (F : Ambient d × Ambient d → ℝ) (hF : Integrable F ρ) :
    Tendsto (fun H => ∫ q in univ ×ˢ s H, F q ∂ρ) atTop (𝓝 (∫ q, F q ∂ρ)) := by
  let G := fun H => (univ ×ˢ s H).indicator F
  have hGmeas : ∀ H, AEStronglyMeasurable (G H) ρ :=
    fun H => hF.aestronglyMeasurable.indicator (MeasurableSet.univ.prod (hs H))
  have hGbound : ∀ H, ∀ᵐ q ∂ρ, ‖G H q‖ ≤ ‖F q‖ := by
    intro H
    apply Eventually.of_forall
    intro q
    by_cases hq : q ∈ univ ×ˢ s H
    · simp only [G, indicator_of_mem hq, le_refl]
    · simp only [G, indicator_of_notMem hq, norm_zero, norm_nonneg]
  have hGlim : ∀ᵐ q ∂ρ, Tendsto (fun H => G H q) atTop (𝓝 (F q)) := by
    apply Eventually.of_forall
    intro q
    apply tendsto_const_nhds.congr'
    filter_upwards [hcontain (dist q.2 a + 1)] with H hH
    have hq : q ∈ univ ×ˢ s H :=
      ⟨mem_univ _, hH (by change dist q.2 a < dist q.2 a + 1; linarith)⟩
    exact (indicator_of_mem hq F).symm
  have ht := tendsto_integral_of_dominated_convergence (fun q => ‖F q‖) hGmeas hF.norm hGbound hGlim
  simpa only [G, integral_indicator (MeasurableSet.univ.prod (hs _))] using! ht

theorem heightPairingOn_as_exhaustion {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a : Ambient d)
    (A : Set (Ambient d)) (hA : MeasurableSet A) (r T : ℝ) (hr : 0 < r)
    (hinner : ball a r ⊆ A) (houter : A ⊆ ball a T)
    (s : ℕ → Set (Ambient d)) (hs : ∀ H, MeasurableSet (s H))
    [∀ H, IsFiniteMeasure (μ.restrict (s H))]
    (hcontain : ∀ R : ℝ, ∀ᶠ H in atTop, ball a R ⊆ s H)
    (w φ : Ambient d → ℝ) (hφI : Integrable φ μ) (hφzero : ∀ x ∉ A, φ x = 0)
    (hmean : (∫ x, φ x ∂μ) = 0)
    (hw : ∀ H, Integrable w (μ.restrict (s H)))
    (hF : ∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2)
      ((μ.restrict (s H)).prod (μ.restrict (s H))))
    (hfar : Integrable (renormalizedNormalIntegrand m w φ a) ((μ.restrict A).prod (μ.restrict Aᶜ))) :
    Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear m w φ q.1 q.2 ∂(μ.restrict (s H)).prod (μ.restrict (s H))))
      atTop (𝓝 (heightPairingOn m μ a A w φ)) := by
  have ht := integral_outer_regions_exhaustion ((μ.restrict A).prod (μ.restrict Aᶜ))
    a s hs hcontain (renormalizedNormalIntegrand m w φ a) hfar
  have hlim : Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear m w φ q.1 q.2 ∂(μ.restrict A).prod (μ.restrict A)) +
      ∫ q in univ ×ˢ s H, renormalizedNormalIntegrand m w φ a q
        ∂(μ.restrict A).prod (μ.restrict Aᶜ)) atTop (𝓝 (heightPairingOn m μ a A w φ)) :=
    tendsto_const_nhds.add ht
  apply hlim.congr'
  filter_upwards [hcontain T] with H hH
  have hAs : A ⊆ s H := houter.trans hH
  have hrestrict : (μ.restrict (s H)).restrict A = μ.restrict A := by
    rw [Measure.restrict_restrict hA, inter_eq_left.mpr hAs]
  have hmeanA : (∫ x in A, φ x ∂μ.restrict (s H)) = 0 := by
    rw [hrestrict]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hφzero).trans hmean
  have hfinite := (finite_height_pairing_eq_renormalized m w φ (μ.restrict (s H)) a A hA
    hφI.restrict hφzero hmeanA
    (center_height_integrable_finite_region m (μ.restrict (s H)) w (hw H) a r hr A hA hinner)
    (hF H)).2
  have hcomm : (μ.restrict (s H)).restrict Aᶜ = (μ.restrict Aᶜ).restrict (s H) := by
    rw [Measure.restrict_restrict hA.compl, Measure.restrict_restrict (hs H), inter_comm]
  have hprod : (μ.restrict A).prod ((μ.restrict Aᶜ).restrict (s H)) =
      ((μ.restrict A).prod (μ.restrict Aᶜ)).restrict (univ ×ˢ s H) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  unfold heightPairingOn at hfinite
  rw [hrestrict, hcomm, hprod] at hfinite
  exact hfinite.symm

theorem heightPairingOn_zero_of_exhaustion {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a : Ambient d)
    (A : Set (Ambient d)) (hA : MeasurableSet A) (r T : ℝ) (hr : 0 < r)
    (hinner : ball a r ⊆ A) (houter : A ⊆ ball a T)
    (s : ℕ → Set (Ambient d)) (hs : ∀ H, MeasurableSet (s H))
    [∀ H, IsFiniteMeasure (μ.restrict (s H))]
    (hcontain : ∀ R : ℝ, ∀ᶠ H in atTop, ball a R ⊆ s H)
    (w φ : Ambient d → ℝ) (hφI : Integrable φ μ) (hφzero : ∀ x ∉ A, φ x = 0)
    (hmean : (∫ x, φ x ∂μ) = 0)
    (hw : ∀ H, Integrable w (μ.restrict (s H)))
    (hF : ∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2)
      ((μ.restrict (s H)).prod (μ.restrict (s H))))
    (hfar : Integrable (renormalizedNormalIntegrand m w φ a) ((μ.restrict A).prod (μ.restrict Aᶜ)))
    (hzero : Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear m w φ q.1 q.2 ∂(μ.restrict (s H)).prod (μ.restrict (s H)))) atTop (𝓝 0)) :
    heightPairingOn m μ a A w φ = 0 :=
  tendsto_nhds_unique (heightPairingOn_as_exhaustion m μ a A hA r T hr hinner houter
    s hs hcontain w φ hφI hφzero hmean hw hF hfar) hzero

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_InfiniteHeightTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

theorem finiteShellRegion_measurable {d : ℕ} (a : Ambient d) (R : ℝ) (N : ℕ) :
    MeasurableSet (finiteShellRegion a R N) :=
  MeasurableSet.iUnion (fun k => MeasurableSet.iUnion (fun _ => dyadicAnnulus_measurable a R k))

theorem finiteShellRegion_monotone {d : ℕ} (a : Ambient d) (R : ℝ) :
    Monotone (finiteShellRegion a R) := by
  intro N M hNM y hy
  obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp hy
  exact mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le hNM), hyk⟩

theorem infinite_shell_weighted_height_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (w : Ambient d → ℝ) (hwm : Measurable w)
    (hw : ∀ k, MemLp w 2 (μ.restrict (dyadicAnnulus a R k)))
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hsecond : ∀ k, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ ∧
      (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        (B * δ / R) / (1 - b / 2) := by
  classical
  let f := fun y => |w y| * inverseDistancePow (m + 2) a y
  let g := (closedExterior a R).indicator f
  have hm : Measurable g :=
    (hwm.abs.mul (inverseDistancePow_measurable (m + 2) a)).indicator (closedExterior_measurable a R)
  have hpos : ∀ y, 0 ≤ g y := fun _ => indicator_nonneg (fun _ _ =>
    mul_nonneg (abs_nonneg _) (inverseDistancePow_nonneg _ _ _)) _
  have hsub : ∀ N, finiteShellRegion a R N ⊆ closedExterior a R := by
    intro N y hy
    rw [finiteShellRegion_eq a R hR N] at hy
    exact hy.1
  have heq : ∀ N, EqOn f g (finiteShellRegion a R N) := by
    intro N y hy
    exact (indicator_of_mem (hsub N hy) f).symm
  have hcover : support g ⊆ ⋃ N, finiteShellRegion a R N := by
    intro y hy
    have hyext : y ∈ closedExterior a R := by
      by_contra h
      exact hy (indicator_of_notMem h f)
    obtain ⟨k, hk⟩ := mem_iUnion.mp (closedExterior_subset_iUnion_dyadicAnnulus a R hR hyext)
    exact mem_iUnion.mpr ⟨k + 1, mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), hk⟩⟩
  have hlocal := fun N => finite_shell_weighted_height_bound m C B μ hg hCB a R hR N w
    (fun k _ => hw k) δ b hδ hb0 hb2 (fun k _ => hsecond k)
  have hI : ∀ N, IntegrableOn g (finiteShellRegion a R N) μ :=
    fun N => (hlocal N).1.congr_fun (heq N) (finiteShellRegion_measurable a R N)
  have hbound : ∀ N, (∫ y in finiteShellRegion a R N, g y ∂μ) ≤ (B * δ / R) / (1 - b / 2) := by
    intro N
    have hi : (∫ y in finiteShellRegion a R N, g y ∂μ) = ∫ y in finiteShellRegion a R N, f y ∂μ :=
      setIntegral_congr_fun (finiteShellRegion_measurable a R N) (fun y hy => (heq N hy).symm)
    rw [hi]
    exact (hlocal N).2
  obtain ⟨hgI, hgB⟩ := nonnegative_integrable_of_exhaustion μ g hm hpos (finiteShellRegion a R)
    (finiteShellRegion_measurable a R) (finiteShellRegion_monotone a R) hcover hI
    ((B * δ / R) / (1 - b / 2)) hbound
  refine ⟨(integrable_indicator_iff (closedExterior_measurable a R)).mp hgI, ?_⟩
  simpa only [g, integral_indicator (closedExterior_measurable a R)] using! hgB

theorem infinite_weighted_height_tail_shifted {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (w : Ambient d → ℝ) (hwm : Measurable w)
    (hw : ∀ k, MemLp w 2 (μ.restrict (dyadicAnnulus a R k)))
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hsecond : ∀ k, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) (ℓ : ℕ) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a (R * 2 ^ ℓ)) μ ∧
      (∫ y in closedExterior a (R * 2 ^ ℓ), |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        ((B * δ / R) / (1 - b / 2)) * (b / 2) ^ ℓ := by
  have hw' : ∀ k, MemLp w 2 (μ.restrict (dyadicAnnulus a (R * 2 ^ ℓ) k)) := by
    intro k
    rw [dyadicAnnulus_shift]
    exact hw (ℓ + k)
  have hs' : ∀ k, (∫ y in dyadicAnnulus a (R * 2 ^ ℓ) k, w y ^ 2 ∂μ) ≤
      (B * ((R * 2 ^ ℓ) * 2 ^ k) ^ m) * ((δ * b ^ ℓ) * ((R * 2 ^ ℓ) * 2 ^ k) * b ^ k) ^ 2 := by
    intro k
    rw [dyadicAnnulus_shift]
    convert! hsecond (ℓ + k) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [pow_add, mul_pow]
    ring
  obtain ⟨hi, hb⟩ := infinite_shell_weighted_height_bound m C B μ hg hCB a (R * 2 ^ ℓ)
    (by positivity) w hwm hw' (δ * b ^ ℓ) b (by positivity) hb0 hb2 hs'
  refine ⟨hi, hb.trans_eq ?_⟩
  have hden : 0 < 1 - b / 2 := by linarith
  rw [div_pow]
  field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_InheritedHeightMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem dyadic_annulus_subset_bounded_box {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (R : ℝ) (M : ℕ) (hM : 2 * R * ((Q : ℝ) + 1) ≤ M) (k : ℕ) :
    dyadicAnnulus (e 0) R k ⊆ boundedProjectionRegion π (e 0) K (M * 2 ^ k) := by
  have hinner : R * (2 : ℝ) ^ (k + 1) ≤ planeBoxInnerRadius Q (M * 2 ^ k) := by
    unfold planeBoxInnerRadius
    apply (le_div_iff₀ (by positivity : 0 < (Q : ℝ) + 1)).mpr
    push_cast
    rw [pow_succ]
    have hm := mul_le_mul_of_nonneg_right hM (by positivity : 0 ≤ (2 : ℝ) ^ k)
    nlinarith
  exact (dyadicAnnulus_subset_ball (e 0) R k).trans ((ball_subset_ball hinner).trans
    (ball_subset_boundedProjectionRegion e π K Q hπ hleft (M * 2 ^ k)))

theorem dyadic_bounded_box_subset_ball {ι : Type*} {d : ℕ}
    (π : Ambient d → ι → ℝ) (a : Ambient d) (K : ℝ≥0) (M k : ℕ) :
    boundedProjectionRegion π a K (M * 2 ^ k) ⊆
      ball a ((((K : ℝ) + 1) * ((M : ℝ) + 1)) * (2 : ℝ) ^ k) := by
  intro x hx
  apply (ball_subset_ball ?_) hx.2
  unfold planeBoxOuterRadius
  push_cast
  have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  nlinarith [K.coe_nonneg]

theorem inherited_annular_second_moments {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (R : ℝ) (M : ℕ) (hM : 2 * R * ((Q : ℝ) + 1) ≤ M)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (w : ℕ → Ambient d → ℝ) (f : Ambient d → ℝ)
    (hf : ∀ H, MemLp f 2 (ν.restrict (boundedProjectionRegion π (e 0) K H)))
    (hlimit : ∀ H, Tendsto (fun j => ∫ x, w j x ^ 2
      ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
      (𝓝 (∫ x, f x ^ 2 ∂ν.restrict (boundedProjectionRegion π (e 0) K H))))
    (hw : ∀ k j, MemLp (w j) 2 ((μ j).restrict
      (ball (e 0) ((((K : ℝ) + 1) * ((M : ℝ) + 1)) * (2 : ℝ) ^ k))))
    (bound : ℕ → ℝ)
    (hbound : ∀ k, ∀ᶠ j in atTop,
      (∫ x in ball (e 0) ((((K : ℝ) + 1) * ((M : ℝ) + 1)) * (2 : ℝ) ^ k),
        w j x ^ 2 ∂μ j) ≤ bound k) :
    ∀ k, MemLp f 2 (ν.restrict (dyadicAnnulus (e 0) R k)) ∧
      (∫ x in dyadicAnnulus (e 0) R k, f x ^ 2 ∂ν) ≤ bound k := by
  intro k
  let H := M * 2 ^ k
  have hsub := dyadic_annulus_subset_bounded_box e π K Q hπ hleft R M hM k
  have hνle : ν.restrict (dyadicAnnulus (e 0) R k) ≤
      ν.restrict (boundedProjectionRegion π (e 0) K H) := Measure.restrict_mono hsub le_rfl
  refine ⟨MemLp.mono_measure hνle (hf H), ?_⟩
  have hlocalBound : ∀ᶠ j in atTop,
      (∫ x, w j x ^ 2 ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ bound k := by
    filter_upwards [hbound k] with j hj
    have hm := Measure.restrict_mono (dyadic_bounded_box_subset_ball π (e 0) K M k)
      (le_rfl : μ j ≤ μ j)
    exact (integral_mono_measure hm (Eventually.of_forall fun x => sq_nonneg (w j x))
      (hw k j).integrable_sq).trans hj
  have hlimitBound := le_of_tendsto (hlimit H) hlocalBound
  exact (integral_mono_measure hνle (Eventually.of_forall fun x => sq_nonneg (f x))
    (hf H).integrable_sq).trans hlimitBound

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_InheritedHeightTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem inherited_height_tail_bound {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ℕ) (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (R : ℝ) (hR : 0 < R) (M : ℕ) (hM : 2 * R * ((Q : ℝ) + 1) ≤ M)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (C B : ℝ) (hg : GlobalUpperGrowth m C ν) (hCB : C * 2 ^ m ≤ B)
    (w : ℕ → Ambient d → ℝ) (f : Ambient d → ℝ) (hfm : Measurable f)
    (hf : ∀ H, MemLp f 2 (ν.restrict (boundedProjectionRegion π (e 0) K H)))
    (hlimit : ∀ H, Tendsto (fun j => ∫ x, w j x ^ 2
      ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
      (𝓝 (∫ x, f x ^ 2 ∂ν.restrict (boundedProjectionRegion π (e 0) K H))))
    (hw : ∀ k j, MemLp (w j) 2 ((μ j).restrict
      (ball (e 0) ((((K : ℝ) + 1) * ((M : ℝ) + 1)) * (2 : ℝ) ^ k))))
    (b : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hbound : ∀ k, ∀ᶠ j in atTop,
      (∫ x in ball (e 0) ((((K : ℝ) + 1) * ((M : ℝ) + 1)) * (2 : ℝ) ^ k), w j x ^ 2 ∂μ j) ≤
        (B * (R * 2 ^ k) ^ m) * ((R * 2 ^ k) * b ^ k) ^ 2) :
    ∀ ℓ, IntegrableOn (fun y => |f y| * inverseDistancePow (m + 2) (e 0) y)
      (closedExterior (e 0) (R * 2 ^ ℓ)) ν ∧
      (∫ y in closedExterior (e 0) (R * 2 ^ ℓ), |f y| * inverseDistancePow (m + 2) (e 0) y ∂ν) ≤
        ((B / R) / (1 - b / 2)) * (b / 2) ^ ℓ := by
  have hmoments := inherited_annular_second_moments e π K Q hπ hleft R M hM μ ν w f
    hf hlimit hw (fun k => (B * (R * 2 ^ k) ^ m) * ((R * 2 ^ k) * b ^ k) ^ 2) hbound
  intro ℓ
  have ht := infinite_weighted_height_tail_shifted m C B ν hg hCB (e 0) R hR f hfm
    (fun k => (hmoments k).1) 1 b (by norm_num) hb0 hb2
    (fun k => by simpa only [one_mul] using! (hmoments k).2) ℓ
  simpa only [mul_one] using! ht

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_RenormalizedLimitEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Renormalized equation from source moments

Local square-integrability and inherited source-moment tail bounds make the
renormalized height pairing integrable. Exhaustion by bounded projection regions
then turns the vanishing limiting bilinear pairings into a zero ball pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem renormalized_limit_equation_from_source_moments {ι : Type*} [Fintype ι] {d : ℕ}
    (p : ℕ) (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (H₀ R : ℝ) (hH₀ : 0 ≤ H₀) (hR : 0 < R) (hHR : 2 * H₀ ≤ R)
    (M : ℕ) (hM : 2 * R * ((Q : ℝ) + 1) ≤ M)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [SFinite ν] [IsFiniteMeasureOnCompacts ν]
    (C B : ℝ) (hg : GlobalUpperGrowth (p + 1) C ν) (hCB : C * 2 ^ (p + 1) ≤ B)
    (w : ℕ → Ambient d → ℝ) (f : Ambient d → ℝ) (hfm : Measurable f)
    (hf : ∀ H, MemLp f 2 (ν.restrict (boundedProjectionRegion π (e 0) K H)))
    (hlimit : ∀ H, Tendsto (fun j => ∫ x, w j x ^ 2
      ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
      (𝓝 (∫ x, f x ^ 2 ∂ν.restrict (boundedProjectionRegion π (e 0) K H))))
    (hw : ∀ k j, MemLp (w j) 2 ((μ j).restrict
      (ball (e 0) ((((K : ℝ) + 1) * ((M : ℝ) + 1)) * (2 : ℝ) ^ k))))
    (b : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hbound : ∀ k, ∀ᶠ j in atTop,
      (∫ x in ball (e 0) ((((K : ℝ) + 1) * ((M : ℝ) + 1)) * (2 : ℝ) ^ k), w j x ^ 2 ∂μ j) ≤
        (B * (R * 2 ^ k) ^ (p + 1)) * ((R * 2 ^ k) * b ^ k) ^ 2)
    (henergy : ∀ H, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
      ((ν.restrict (boundedProjectionRegion π (e 0) K H)).prod
        (ν.restrict (boundedProjectionRegion π (e 0) K H))))
    (φ : Ambient d → ℝ) (L D : ℝ≥0) (hφ : LipschitzWith L φ) (hcφ : HasCompactSupport φ)
    (hD : ∀ x, |φ x| ≤ (D : ℝ)) (hsupport : ∀ x, φ x ≠ 0 → dist x (e 0) ≤ H₀)
    (hmean : (∫ x, φ x ∂ν) = 0)
    (hzero : Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) f φ q.1 q.2
        ∂(ν.restrict (boundedProjectionRegion π (e 0) K H)).prod
          (ν.restrict (boundedProjectionRegion π (e 0) K H)))) atTop (𝓝 0)) :
    heightPairingOn (p + 1) ν (e 0) (ball (e 0) R) f φ = 0 := by
  let s := fun H => boundedProjectionRegion π (e 0) K H
  let (H : ℕ) : IsFiniteMeasure (ν.restrict (s H)) :=
    boundedProjectionRegion_finite ν π (e 0) K H
  let : IsFiniteMeasure (ν.restrict (ball (e 0) R)) :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C ν hg (e 0) R hR
  have hcontain := eventually_ball_subset_boundedProjectionRegion e π K Q hπ hleft
  obtain ⟨J, hJ⟩ := (hcontain R).exists
  have hfball : MemLp f 2 (ν.restrict (ball (e 0) R)) :=
    MemLp.mono_measure (Measure.restrict_mono hJ le_rfl) (hf J)
  have hφI : Integrable φ ν := hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hφf : Integrable (fun x => φ x * f x) (ν.restrict (ball (e 0) R)) := by
    have hprod : MemLp (fun x => φ x * f x) 1 (ν.restrict (ball (e 0) R)) :=
      MeasureTheory.MemLp.mul (hφ := (lipschitz_height_memLp_on_ball (p + 1) C ν hg φ L hφ (e 0) R hR)) (hf := hfball)
    exact memLp_one_iff_integrable.mp hprod
  have htail := inherited_height_tail_bound (p + 1) e π K Q hπ hleft R hR M hM μ ν
    C B hg hCB w f hfm hf hlimit hw b hb0 hb2 hbound 0
  simp only [pow_zero, mul_one] at htail
  have hfar := (renormalized_far_pairing_integrable_and_bound (p + 1) C ν
    (ν.restrict (ball (e 0) R)) hg f φ hfm hφ.continuous.measurable hφI.restrict hφf
    (e 0) H₀ R hH₀ hR hHR (Eventually.of_forall hsupport) htail.1 _ htail.2).1
  have hfar' : Integrable (renormalizedNormalIntegrand (p + 1) f φ (e 0))
      ((ν.restrict (ball (e 0) R)).prod (ν.restrict (ball (e 0) R)ᶜ)) := by
    rwa [← closedExterior_eq_compl_ball]
  have hφzero : ∀ x ∉ ball (e 0) R, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupport x hn).trans_lt (by linarith : H₀ < R))
  apply heightPairingOn_zero_of_exhaustion (p + 1) ν (e 0) (ball (e 0) R)
    measurableSet_ball R R hR subset_rfl subset_rfl s
    (fun H => (boundedProjectionRegion_isOpen π hπ.continuous (e 0) K H).measurableSet)
    hcontain f φ hφI hφzero hmean (fun H => (hf H).integrable (by norm_num))
    _ hfar' hzero
  intro H
  exact (fractional_bilinear_integrable_and_cap_error p C (ν.restrict (s H))
    (globalGrowth_restrict (p + 1) C ν hg (s H)) f φ hfm ((hf H).integrable (by norm_num))
    L D hφ hD (henergy H) 1 (by norm_num)).1

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CommonHeightEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A common height satisfying renormalized equations

The common subsequential height limit inherits the corrected Riesz equations from
uniform local moments and vanishing normalized oscillation. Source-moment tail
control further identifies its renormalized pairing on each admissible ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_common_height_with_renormalized_equations {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)] [∀ j, SFinite (σ j)]
    (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e))
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (σ j))
    (hlower : ∀ j x, x ∈ (σ j).support → ∀ r : ℝ, AdmissibleRadius (σ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (σ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (σ j).support)
    (u : ℕ → Ambient d → ℝ) (Ku : ℝ≥0) (hu : ∀ j, LipschitzWith Ku (u j))
    (z : ℕ → Ambient d) (hz : ∀ j, ‖z j‖ ≤ 1)
    (hdiff : ∀ j x y, u j x - u j y = inner ℝ (z j) (x - y))
    (δ A v : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (σ j) (e 0) (A j) (v j))
    (hratio : Tendsto (fun j => v j / δ j) atTop (𝓝 0))
    (W : ℝ) (hW : ∀ j, |u j (e 0)| ≤ W)
    (hw : ∀ H j, MemLp (fun x => u j x / δ j) 2
      ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B₀ E₀ : ℕ → ℝ)
    (hB₀ : ∀ H j, (∫ x, (u j x / δ j) ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B₀ H)
    (henergy : ∀ H j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2)
      (((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H))))
    (hE₀ : ∀ H j, (∫ q : Ambient d × Ambient d,
      fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2
      ∂(((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ f : Ambient d → ℝ, Measurable f ∧
      (∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
      (∀ H, Tendsto (fun j => ∫ x, (u (ρ j) x / δ (ρ j)) ^ 2
        ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
        (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      (∀ H (ψ : Ambient d → ℝ) (L D : ℝ≥0), HasCompactSupport ψ →
        LipschitzWith L ψ → (∀ x, |ψ x| ≤ (D : ℝ)) →
        Tendsto (fun j => ∫ x, (u (ρ j) x / δ (ρ j)) * ψ x
          ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
          (𝓝 (∫ x, f x * ψ x
            ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      (∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
        (((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
          ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
        (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) f q.1 q.2
          ∂(((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
            ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H) ∧
      ∀ (H₀ R : ℝ), 0 ≤ H₀ → 0 < R → 2 * H₀ ≤ R →
        ∀ (B b : ℝ) (N : ℕ → ℕ), G * 2 ^ (p + 1) ≤ B → 0 ≤ b → b < 2 →
          Tendsto N atTop atTop →
          Tendsto (fun j => (R * (2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0) →
          (∀ j k, k < N j → (∫ y in dyadicAnnulus (e 0) R k, u j y ^ 2 ∂σ j) ≤
            (B * (R * 2 ^ k) ^ (p + 1)) * (δ j * (R * 2 ^ k) * b ^ k) ^ 2) →
          ∀ (φ η : Ambient d → ℝ) (Lφ Lη Bφ Bη : ℝ≥0),
            LipschitzWith Lφ φ → LipschitzWith Lη η → HasCompactSupport φ → HasCompactSupport η →
            (∀ x, |φ x| ≤ (Bφ : ℝ)) → (∀ x, |η x| ≤ (Bη : ℝ)) →
            (∀ x, φ x ≠ 0 → dist x (e 0) ≤ H₀) →
            (∀ x, η x ≠ 0 → dist x (e 0) ≤ H₀) →
            (∫ x, φ x ∂coordinatePlaneMeasure e) = 0 → (∫ x, η x ∂coordinatePlaneMeasure e) ≠ 0 →
            (Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
              fractionalBilinear (p + 1) f φ q.1 q.2
                ∂((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
                  ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))))
              atTop (𝓝 0)) ∧
            ∀ (J : ℕ) (Bfar : ℝ), 2 * R * ((Q : ℝ) + 1) ≤ J →
              (2 * (Q : ℝ)) ^ (p + 1) * 2 ^ (p + 1) ≤ Bfar →
              (∀ k, ∀ᶠ j in atTop,
                (∫ x in ball (e 0) ((((K : ℝ) + 1) * ((J : ℝ) + 1)) * (2 : ℝ) ^ k),
                  (u j x / δ j) ^ 2 ∂σ j) ≤
                  (Bfar * (R * 2 ^ k) ^ (p + 1)) * ((R * 2 ^ k) * b ^ k) ^ 2) →
              heightPairingOn (p + 1) (coordinatePlaneMeasure e) (e 0) (ball (e 0) R) f φ = 0 := by
  let w := fun j x => u j x / δ j
  obtain ⟨ρ, hρ, f, hfm, hf, hsecond, hmoment, hlim⟩ :=
    exists_global_height_with_local_singular_limits p e π K Q he hπ hleft σ hlocal C G hC hg
      hlower hdiam w (fun j => ((hu j).continuous.div_const (δ j)).measurable)
      hw B₀ E₀ hB₀ henergy hE₀
  refine ⟨ρ, hρ, f, hfm, hf, hsecond, hmoment, fun H => ⟨(hlim H).1, (hlim H).2.1⟩, ?_⟩
  intro H₀ R hH₀ hR hHR B b N hGB hb0 hb2 hN hlast hshell
    φ η Lφ Lη Bφ Bη hφ hη hcφ hcη hBφ hBη hsφ hsη hmean hbump
  let s := boundedProjectionRegion π (e 0) K
  let T := fun H => max R (planeBoxOuterRadius K H) + 1
  have hRT : ∀ H, R ≤ T H := fun H => (le_max_left _ _).trans (le_add_of_nonneg_right (by norm_num))
  have hout : ∀ H, s H ⊆ ball (e 0) (T H) := by
    intro H x hx
    exact hx.2.trans ((le_max_right R (planeBoxOuterRadius K H)).trans_lt (lt_add_one _))
  obtain ⟨M, hM, hnear⟩ := uniform_ball_moments_from_box_moments (p + 1) e π K Q hπ hleft
    σ G hg w hw B₀ hB₀ R hR
  let (H j : ℕ) : IsFiniteMeasure ((σ (ρ j)).restrict (s H)) :=
    boundedProjectionRegion_finite (σ (ρ j)) π (e 0) K H
  have hzero : Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) f φ q.1 q.2
        ∂((coordinatePlaneMeasure e).restrict (s H)).prod
          ((coordinatePlaneMeasure e).restrict (s H)))) atTop (𝓝 0) := by
    apply corrected_riesz_limiting_equation p G B (fun j => σ (ρ j)) (coordinatePlaneMeasure e)
      (fun ψ => (hlocal ψ).comp hρ.tendsto_atTop) (fun j => hg (ρ j)) hGB (e 0) s
      (fun H => (boundedProjectionRegion_isOpen π hπ.continuous (e 0) K H).measurableSet)
      (eventually_ball_subset_boundedProjectionRegion e π K Q hπ hleft)
      H₀ R hH₀ hR hHR T hRT hout (fun j => u (ρ j)) Ku (fun j => hu (ρ j))
      (fun j => z (ρ j)) (fun j => hz (ρ j)) (fun j => hdiff (ρ j))
      (fun j => δ (ρ j)) (fun j => A (ρ j)) (fun j => v (ρ j)) (fun j => hδ (ρ j))
      (hA.comp hρ.tendsto_atTop) (fun j => hosc (ρ j)) (hratio.comp hρ.tendsto_atTop)
      (fun j => N (ρ j)) (hN.comp hρ.tendsto_atTop) b W hb0 hb2 (fun j => hW (ρ j))
      (hlast.comp hρ.tendsto_atTop) (fun j k hk => hshell (ρ j) k hk)
      M hM (fun j => (hnear (ρ j)).1) (fun j => (hnear (ρ j)).2.1)
      (fun j => (hnear (ρ j)).2.2)
      (fun H j => (hw H (ρ j)).integrable (by norm_num)) (fun H j => henergy H (ρ j))
      f φ η Lφ Lη Bφ Bη hφ hη hcφ hcη hBφ hBη hsφ hsη hmean hbump
    · intro H
      exact (hlim H).2.2 φ Lφ Bφ hφ hBφ
    · intro H
      exact (hlim H).2.2 η Lη Bη hη hBη
  refine ⟨hzero, ?_⟩
  intro J Bfar hJ hBfar hball
  have hνg : GlobalUpperGrowth (p + 1) ((2 * (Q : ℝ)) ^ (p + 1)) (coordinatePlaneMeasure e) := by
    simpa only [Fintype.card_fin] using! coordinatePlaneMeasure_upper_growth e π
      he.continuous.measurable Q hπ hleft
  let := hνg.finite_on_compacts
  have hballL2 : ∀ k j, MemLp (fun x => u (ρ j) x / δ (ρ j)) 2 ((σ (ρ j)).restrict
      (ball (e 0) ((((K : ℝ) + 1) * ((J : ℝ) + 1)) * (2 : ℝ) ^ k))) := by
    intro k j
    obtain ⟨H, hH⟩ := (eventually_ball_subset_boundedProjectionRegion e π K Q hπ hleft
      ((((K : ℝ) + 1) * ((J : ℝ) + 1)) * (2 : ℝ) ^ k)).exists
    exact MemLp.mono_measure (Measure.restrict_mono hH le_rfl) (hw H (ρ j))
  exact renormalized_limit_equation_from_source_moments p e π K Q hπ hleft H₀ R hH₀ hR hHR
    J hJ (fun j => σ (ρ j)) (coordinatePlaneMeasure e) ((2 * (Q : ℝ)) ^ (p + 1)) Bfar
    hνg hBfar (fun j x => u (ρ j) x / δ (ρ j)) f hfm hf hsecond hballL2 b hb0 hb2
    (fun k => hρ.tendsto_atTop.eventually (hball k)) (fun H => (hlim H).1)
    φ Lφ Bφ hφ hcφ hBφ hsφ hmean hzero

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_DyadicSourceTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem dyadic_shifted_last_error_identity (q N : ℕ) (hN : q + 1 ≤ N) (δ : ℝ) :
    ((2 : ℝ) ^ q * 2 ^ (N - (q + 1)))⁻¹ / δ = 2 * (((2 : ℝ) ^ N)⁻¹ / δ) := by
  have hp : (2 : ℝ) ^ (q + 1) * 2 ^ (N - (q + 1)) = (2 : ℝ) ^ N := by
    rw [← pow_add, Nat.add_sub_of_le hN]
  rw [pow_succ] at hp
  have hr : (2 : ℝ) ^ q * 2 ^ (N - (q + 1)) = (2 : ℝ) ^ N / 2 := by nlinarith [hp]
  rw [hr, inv_div]
  ring

theorem dyadic_shifted_last_error_tendsto (q : ℕ) (N : ℕ → ℕ) (δ : ℕ → ℝ)
    (hN : Tendsto N atTop atTop)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0)) :
    Tendsto (fun j => N j - (q + 1)) atTop atTop ∧
      Tendsto (fun j => ((2 : ℝ) ^ q * 2 ^ (N j - (q + 1)))⁻¹ / δ j) atTop (𝓝 0) := by
  refine ⟨(tendsto_sub_atTop_nat (q + 1)).comp hN, ?_⟩
  have h := hlast.const_mul 2
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [hN.eventually (eventually_ge_atTop (q + 1))] with j hj
  exact (dyadic_shifted_last_error_identity q (N j) hj (δ j)).symm

theorem dyadic_ball_to_shell_moment_identity (m q k : ℕ) (D δ b : ℝ) :
    δ ^ 2 * D * ((2 : ℝ) ^ (q + k + 1)) ^ m *
        ((2 : ℝ) ^ (q + k + 1) * b ^ (q + k + 1)) ^ 2 =
      ((D * (2 : ℝ) ^ (m + 2) * (b ^ (q + 1)) ^ 2) * ((2 : ℝ) ^ q * 2 ^ k) ^ m) *
        (δ * ((2 : ℝ) ^ q * 2 ^ k) * b ^ k) ^ 2 := by
  simp only [pow_add, pow_succ, mul_pow]
  ring

theorem controlled_shell_moments_from_dyadic_balls {d : ℕ} (m : ℕ)
    (μ : ℕ → Measure (Ambient d)) (a : Ambient d) (u : ℕ → Ambient d → ℝ)
    (δ : ℕ → ℝ) (N : ℕ → ℕ) (D b Bmin : ℝ)
    (hw : ∀ l j, MemLp (u j) 2 ((μ j).restrict (ball a ((2 : ℝ) ^ l))))
    (hbound : ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), u j x ^ 2 ∂μ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ m * ((2 : ℝ) ^ l * b ^ l) ^ 2) (q : ℕ) :
    ∃ B : ℝ, Bmin ≤ B ∧ ∀ j k, k < N j - (q + 1) →
      (∫ x in dyadicAnnulus a ((2 : ℝ) ^ q) k, u j x ^ 2 ∂μ j) ≤
        (B * ((2 : ℝ) ^ q * 2 ^ k) ^ m) * (δ j * ((2 : ℝ) ^ q * 2 ^ k) * b ^ k) ^ 2 := by
  let B₀ := D * (2 : ℝ) ^ (m + 2) * (b ^ (q + 1)) ^ 2
  refine ⟨max Bmin B₀, le_max_left _ _, ?_⟩
  intro j k hk
  have hcontrol : q + k + 1 ≤ N j := by omega
  have hsub : dyadicAnnulus a ((2 : ℝ) ^ q) k ⊆ ball a ((2 : ℝ) ^ (q + k + 1)) := by
    convert! dyadicAnnulus_subset_ball a ((2 : ℝ) ^ q) k using 1
    all_goals try with_reducible_and_instances rfl
    rw [← pow_add]
    congr 2
  calc
    _ ≤ ∫ x in ball a ((2 : ℝ) ^ (q + k + 1)), u j x ^ 2 ∂μ j :=
      integral_mono_measure (Measure.restrict_mono hsub le_rfl)
        (Eventually.of_forall (fun x => sq_nonneg (u j x))) (hw (q + k + 1) j).integrable_sq
    _ ≤ δ j ^ 2 * D * ((2 : ℝ) ^ (q + k + 1)) ^ m *
        ((2 : ℝ) ^ (q + k + 1) * b ^ (q + k + 1)) ^ 2 := hbound j (q + k + 1) hcontrol
    _ = (B₀ * ((2 : ℝ) ^ q * 2 ^ k) ^ m) *
        (δ j * ((2 : ℝ) ^ q * 2 ^ k) * b ^ k) ^ 2 :=
      dyadic_ball_to_shell_moment_identity m q k D (δ j) b
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right Bmin B₀) (by positivity)) (sq_nonneg _)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_DyadicSourceMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem normalized_second_moment_bound {d : ℕ}
    (μ : Measure (Ambient d)) (u : Ambient d → ℝ) (δ D : ℝ) (hδ : 0 < δ)
    (hbound : (∫ x, u x ^ 2 ∂μ) ≤ δ ^ 2 * D) :
    (∫ x, (u x / δ) ^ 2 ∂μ) ≤ D := by
  simp only [div_pow, integral_div]
  exact (div_le_iff₀ (sq_pos_of_pos hδ)).mpr (by simpa only [mul_comm D] using! hbound)

theorem dyadic_second_moment_rescale (m q k : ℕ) (D b R : ℝ) (hR : 0 < R) :
    ((D * ((2 : ℝ) ^ q) ^ m * ((2 : ℝ) ^ q * b ^ q) ^ 2) / R ^ (m + 2)) *
        (R * 2 ^ k) ^ m * ((R * 2 ^ k) * b ^ k) ^ 2 =
      D * ((2 : ℝ) ^ (q + k)) ^ m * ((2 : ℝ) ^ (q + k) * b ^ (q + k)) ^ 2 := by
  rw [pow_add R m 2]
  simp only [pow_add, mul_pow]
  field_simp

theorem comparable_ball_moments_from_dyadic_control {d : ℕ} (m : ℕ)
    (μ : ℕ → Measure (Ambient d)) (a : Ambient d) (w : ℕ → Ambient d → ℝ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ)
    (hw : ∀ l j, MemLp (w j) 2 ((μ j).restrict (ball a ((2 : ℝ) ^ l))))
    (hbound : ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), w j x ^ 2 ∂μ j) ≤
      D * ((2 : ℝ) ^ l) ^ m * ((2 : ℝ) ^ l * b ^ l) ^ 2)
    (T R Bmin : ℝ) (hR : 0 < R) :
    ∃ B : ℝ, Bmin ≤ B ∧
      (∀ k j, MemLp (w j) 2 ((μ j).restrict (ball a (T * (2 : ℝ) ^ k)))) ∧
      ∀ k, ∀ᶠ j in atTop,
        (∫ x in ball a (T * (2 : ℝ) ^ k), w j x ^ 2 ∂μ j) ≤
          (B * (R * 2 ^ k) ^ m) * ((R * 2 ^ k) * b ^ k) ^ 2 := by
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt T (by norm_num : (1 : ℝ) < 2)
  let B₀ := (D * ((2 : ℝ) ^ q) ^ m * ((2 : ℝ) ^ q * b ^ q) ^ 2) / R ^ (m + 2)
  let B := max Bmin B₀
  have hrad : ∀ k, T * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (q + k) := by
    intro k
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right hq.le (by positivity)
  have hμ : ∀ k j, (μ j).restrict (ball a (T * (2 : ℝ) ^ k)) ≤
      (μ j).restrict (ball a ((2 : ℝ) ^ (q + k))) :=
    fun k j => Measure.restrict_mono (ball_subset_ball (hrad k)) le_rfl
  refine ⟨B, le_max_left _ _, fun k j => MemLp.mono_measure (hμ k j) (hw (q + k) j), ?_⟩
  intro k
  filter_upwards [hN.eventually (eventually_ge_atTop (q + k))] with j hj
  calc
    _ ≤ ∫ x in ball a ((2 : ℝ) ^ (q + k)), w j x ^ 2 ∂μ j :=
      integral_mono_measure (hμ k j) (Eventually.of_forall (fun x => sq_nonneg (w j x)))
        (hw (q + k) j).integrable_sq
    _ ≤ D * ((2 : ℝ) ^ (q + k)) ^ m * ((2 : ℝ) ^ (q + k) * b ^ (q + k)) ^ 2 :=
      hbound j (q + k) hj
    _ = (B₀ * (R * 2 ^ k) ^ m) * ((R * 2 ^ k) * b ^ k) ^ 2 :=
      (dyadic_second_moment_rescale m q k D b R hR).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right Bmin B₀) (by positivity)) (sq_nonneg _)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_InheritedDyadicTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem limiting_height_tail_from_dyadic_source {ι : Type*} [Fintype ι] {d : ℕ} (m : ℕ)
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (C : ℝ) (hg : GlobalUpperGrowth m C ν)
    (w : ℕ → Ambient d → ℝ) (f : Ambient d → ℝ) (hfm : Measurable f)
    (hf : ∀ H, MemLp f 2 (ν.restrict (boundedProjectionRegion π (e 0) K H)))
    (hlimit : ∀ H, Tendsto (fun j => ∫ x, w j x ^ 2
      ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
      (𝓝 (∫ x, f x ^ 2 ∂ν.restrict (boundedProjectionRegion π (e 0) K H))))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hw : ∀ l j, MemLp (w j) 2 ((μ j).restrict (ball (e 0) ((2 : ℝ) ^ l))))
    (hbound : ∀ j l, l ≤ N j → (∫ x in ball (e 0) ((2 : ℝ) ^ l), w j x ^ 2 ∂μ j) ≤
      D * ((2 : ℝ) ^ l) ^ m * ((2 : ℝ) ^ l * b ^ l) ^ 2) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun x => |f x| * inverseDistancePow (m + 2) (e 0) x)
      (closedExterior (e 0) R) ν := by
  obtain ⟨J, hJ⟩ := exists_nat_ge (2 * R * ((Q : ℝ) + 1))
  obtain ⟨B, hB, hballs, hb⟩ := comparable_ball_moments_from_dyadic_control m μ (e 0) w N hN D b
    hw hbound (((K : ℝ) + 1) * ((J : ℝ) + 1)) R (C * 2 ^ m) hR
  have h := (inherited_height_tail_bound m e π K Q hπ hleft R hR J hJ μ ν C B hg hB
    w f hfm hf hlimit hballs b hb0 hb2 hb 0).1
  simpa only [pow_zero, mul_one] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LocalHeightData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem local_height_data_on_balls {ι : Type*} [Fintype ι] {d : ℕ} (m : ℕ)
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (μ : Measure (Ambient d)) [SFinite μ] (f : Ambient d → ℝ)
    (hf : ∀ H, MemLp f 2 (μ.restrict (boundedProjectionRegion π (e 0) K H)))
    (henergy : ∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m f q.1 q.2)
      ((μ.restrict (boundedProjectionRegion π (e 0) K H)).prod
        (μ.restrict (boundedProjectionRegion π (e 0) K H)))) (R : ℝ) :
    MemLp f 2 (μ.restrict (ball (e 0) R)) ∧
      Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m f q.1 q.2)
        ((μ.restrict (ball (e 0) R)).prod (μ.restrict (ball (e 0) R))) := by
  obtain ⟨H, hH⟩ := (eventually_ball_subset_boundedProjectionRegion e π K Q hπ hleft R).exists
  refine ⟨MemLp.mono_measure (Measure.restrict_mono hH le_rfl) (hf H), ?_⟩
  apply (henergy H).mono_measure
  rw [Measure.prod_restrict, Measure.prod_restrict]
  exact Measure.restrict_mono (prod_mono hH hH) le_rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_HeightBallRadiusIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independence of the height-pairing radius

Local square integrability and a weighted tail bound make the renormalized far
pairing integrable. Local fractional energy then permits comparison through common
outer balls, showing that a mean-zero compact test gives the same height pairing
for either admissible localization radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem renormalized_far_integrable_of_ball_L2 {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (f φ : Ambient d → ℝ) (hfm : Measurable f)
    (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hf : MemLp f 2 (μ.restrict (ball a R))) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (hcφ : HasCompactSupport φ) (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H)
    (htail : IntegrableOn (fun x => |f x| * inverseDistancePow (m + 2) a x) (closedExterior a R) μ) :
    Integrable (renormalizedNormalIntegrand m f φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (ball a R)ᶜ)) := by
  let := hg.finite_on_compacts
  let := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  have hφI : Integrable φ μ := hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hprod : MemLp (fun x => φ x * f x) 1 (μ.restrict (ball a R)) :=
    MeasureTheory.MemLp.mul (hφ := (lipschitz_height_memLp_on_ball m C μ hg φ L hφ a R hR)) (hf := hf)
  have h := (renormalized_far_pairing_integrable_and_bound m C μ (μ.restrict (ball a R)) hg
    f φ hfm hφ.continuous.measurable hφI.restrict (memLp_one_iff_integrable.mp hprod)
    a H R hH hR hHR (Eventually.of_forall hsupport) htail _ le_rfl).1
  rwa [closedExterior_eq_compl_ball] at h

theorem heightPairingOn_ball_independent_from_local_energy {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (a : Ambient d) (f φ : Ambient d → ℝ) (hfm : Measurable f)
    (hf : ∀ T : ℝ, 0 < T → MemLp f 2 (μ.restrict (ball a T)))
    (henergy : ∀ T : ℝ, 0 < T → Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
      ((μ.restrict (ball a T)).prod (μ.restrict (ball a T))))
    (L B : ℝ≥0) (hφ : LipschitzWith L φ) (hcφ : HasCompactSupport φ)
    (hB : ∀ x, |φ x| ≤ (B : ℝ)) (hmean : (∫ x, φ x ∂μ) = 0)
    (H R S : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hS : 0 < S)
    (hHR : 2 * H ≤ R) (hHS : 2 * H ≤ S) (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H)
    (htailR : IntegrableOn (fun x => |f x| * inverseDistancePow (p + 1 + 2) a x) (closedExterior a R) μ)
    (htailS : IntegrableOn (fun x => |f x| * inverseDistancePow (p + 1 + 2) a x) (closedExterior a S) μ) :
    heightPairingOn (p + 1) μ a (ball a R) f φ = heightPairingOn (p + 1) μ a (ball a S) f φ := by
  let := hg.finite_on_compacts
  let T := max R S
  have hT : 0 < T := hR.trans_le (le_max_left _ _)
  have hpos : ∀ k, 0 < outerPairRadius T k := outerPairRadius_pos T hT
  let (k : ℕ) : IsFiniteMeasure (μ.restrict (ball a (outerPairRadius T k))) :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a (outerPairRadius T k) (hpos k)
  have hzR : ∀ x ∉ ball a R, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupport x hn).trans_lt (by linarith : H < R))
  have hzS : ∀ x ∉ ball a S, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupport x hn).trans_lt (by linarith : H < S))
  apply heightPairingOn_localization_independent (p + 1) μ a (ball a R) (ball a S)
    measurableSet_ball measurableSet_ball (min R S) T (lt_min hR hS)
    (ball_subset_ball (min_le_left _ _)) (ball_subset_ball (min_le_right _ _))
    (ball_subset_ball (le_max_left _ _)) (ball_subset_ball (le_max_right _ _))
    f φ (hφ.continuous.integrable_of_hasCompactSupport hcφ) hzR hzS hmean
    (fun k => (hf _ (hpos k)).integrable (by norm_num))
  · intro k
    exact (fractional_bilinear_integrable_and_cap_error p C (μ.restrict (ball a (outerPairRadius T k)))
      (globalGrowth_restrict (p + 1) C μ hg (ball a (outerPairRadius T k))) f φ hfm
      ((hf _ (hpos k)).integrable (by norm_num)) L B hφ hB (henergy _ (hpos k)) 1 (by norm_num)).1
  · exact renormalized_far_integrable_of_ball_L2 (p + 1) C μ hg a f φ hfm H R hH hR hHR
      (hf R hR) L hφ hcφ hsupport htailR
  · exact renormalized_far_integrable_of_ball_L2 (p + 1) C μ hg a f φ hfm H S hH hS hHS
      (hf S hS) L hφ hcφ hsupport htailS

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_DyadicCommonHeightEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Intrinsic equations for a common limiting height

Dyadic source moment bounds supply the integrable tails needed to pass from
renormalized height equations to radius-independent pairings on the limiting plane.
The resulting common height retains local square integrability and fractional
energy bounds, represents a tempered distribution in intrinsic coordinates, and
annihilates directional derivatives of compactly supported smooth tests.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology SchwartzMap
open scoped NNReal ENNReal ContDiff

theorem exists_common_height_with_intrinsic_equation {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (a : Ambient d) (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (hplane : e = affinePlaneSection a L)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)] [∀ j, SFinite (σ j)]
    (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e))
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (σ j))
    (hlower : ∀ j x, x ∈ (σ j).support → ∀ r : ℝ, AdmissibleRadius (σ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (σ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (σ j).support)
    (u : ℕ → Ambient d → ℝ) (Ku : ℝ≥0) (hu : ∀ j, LipschitzWith Ku (u j))
    (z : ℕ → Ambient d) (hz : ∀ j, ‖z j‖ ≤ 1)
    (hdiff : ∀ j x y, u j x - u j y = inner ℝ (z j) (x - y))
    (δ A v : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (σ j) (e 0) (A j) (v j))
    (hratio : Tendsto (fun j => v j / δ j) atTop (𝓝 0))
    (W : ℝ) (hW : ∀ j, |u j (e 0)| ≤ W)
    (hw : ∀ H j, MemLp (fun x => u j x / δ j) 2
      ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B₀ E₀ : ℕ → ℝ)
    (hB₀ : ∀ H j, (∫ x, (u j x / δ j) ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B₀ H)
    (henergy : ∀ H j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2)
      (((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H))))
    (hE₀ : ∀ H j, (∫ q : Ambient d × Ambient d,
      fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2
      ∂(((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball (e 0) ((2 : ℝ) ^ l), u j x ^ 2 ∂σ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ f : Ambient d → ℝ, Measurable f ∧
      (∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
      (∀ H, Tendsto (fun j => ∫ x, (u (ρ j) x / δ (ρ j)) ^ 2
        ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
        (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      (∀ H (ψ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport ψ →
        LipschitzWith J ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
        Tendsto (fun j => ∫ x, (u (ρ j) x / δ (ρ j)) * ψ x
          ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
          (𝓝 (∫ x, f x * ψ x
            ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      (∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
        (((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
          ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
        (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) f q.1 q.2
          ∂(((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
            ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H) ∧
      (∀ R : ℝ, 0 < R → IntegrableOn
        (fun x => |f x| * inverseDistancePow (p + 1 + 2) (e 0) x)
        (closedExterior (e 0) R) (coordinatePlaneMeasure e)) ∧
      (∀ (φ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport φ → LipschitzWith J φ →
        (∀ x, |φ x| ≤ (B : ℝ)) → (∫ x, φ x ∂coordinatePlaneMeasure e) = 0 →
        ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
          heightPairingOn (p + 1) (coordinatePlaneMeasure e) (e 0) (ball (e 0) R) f φ = 0) ∧
      ∃ T : 𝓢'(Ambient (p + 1), ℂ),
        (∀ ψ : 𝓢(Ambient (p + 1), ℂ),
          Integrable (fun x : Ambient (p + 1) => f (a + L x) • ψ x)
            (volume : Measure (Ambient (p + 1))) ∧
          T ψ = ∫ x : Ambient (p + 1), f (a + L x) • ψ x) ∧
        ∀ g : Ambient (p + 1) → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
          ∀ v : Ambient (p + 1), ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
            heightPairingOn (p + 1) volume (0 : Ambient (p + 1)) (ball 0 R)
              (fun x => f (a + L x)) (fun x => fderiv ℝ g x v) = 0 := by
  obtain ⟨ρ, hρ, f, hfm, hf, hsecond, hmoment, hfenergy, hEq⟩ :=
    exists_common_height_with_renormalized_equations p e π K Q he hπ hleft σ hlocal C G hC hg
      hlower hdiam u Ku hu z hz hdiff δ A v hδ hA hosc hratio W hW hw B₀ E₀ hB₀ henergy hE₀
  have huL2 : ∀ l j, MemLp (u j) 2 ((σ j).restrict (ball (e 0) ((2 : ℝ) ^ l))) :=
    fun l j => lipschitz_height_memLp_on_ball (p + 1) G (σ j) (hg j)
      (u j) Ku (hu j) (e 0) ((2 : ℝ) ^ l) (by positivity)
  have hwL2 : ∀ l j, MemLp (fun x => u j x / δ j) 2 ((σ j).restrict (ball (e 0) ((2 : ℝ) ^ l))) := by
    intro l j
    obtain ⟨H, hH⟩ := (eventually_ball_subset_boundedProjectionRegion e π K Q hπ hleft ((2 : ℝ) ^ l)).exists
    exact MemLp.mono_measure (Measure.restrict_mono hH le_rfl) (hw H j)
  have hnorm : ∀ j l, l ≤ N j → (∫ x in ball (e 0) ((2 : ℝ) ^ l), (u j x / δ j) ^ 2 ∂σ j) ≤
      D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2 := by
    intro j l hl
    apply normalized_second_moment_bound ((σ j).restrict (ball (e 0) ((2 : ℝ) ^ l)))
      (u j) (δ j) _ (hδ j)
    convert! hsource j l hl using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hνg : GlobalUpperGrowth (p + 1) ((2 * (Q : ℝ)) ^ (p + 1)) (coordinatePlaneMeasure e) := by
    simpa only [Fintype.card_fin] using! coordinatePlaneMeasure_upper_growth e π
      he.continuous.measurable Q hπ hleft
  let := hνg.finite_on_compacts
  have hTail : ∀ R : ℝ, 0 < R → IntegrableOn
      (fun x => |f x| * inverseDistancePow (p + 1 + 2) (e 0) x)
      (closedExterior (e 0) R) (coordinatePlaneMeasure e) := by
    intro R hR
    exact limiting_height_tail_from_dyadic_source (p + 1) e π K Q hπ hleft
      (fun j => σ (ρ j)) (coordinatePlaneMeasure e) ((2 * (Q : ℝ)) ^ (p + 1)) hνg
      (fun j x => u (ρ j) x / δ (ρ j)) f hfm hf hsecond (fun j => N (ρ j))
      (hN.comp hρ.tendsto_atTop) D b hb0 hb2 (fun l j => hwL2 l (ρ j))
      (fun j l hl => hnorm (ρ j) l hl) R hR
  have hdata := local_height_data_on_balls (p + 1) e π K Q hπ hleft (coordinatePlaneMeasure e)
    f hf (fun H => (hfenergy H).1)
  have hCompact : ∀ (φ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport φ → LipschitzWith J φ →
      (∀ x, |φ x| ≤ (B : ℝ)) → (∫ x, φ x ∂coordinatePlaneMeasure e) = 0 →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        heightPairingOn (p + 1) (coordinatePlaneMeasure e) (e 0) (ball (e 0) R) f φ = 0 := by
    intro φ Jφ Bφ hcφ hφ hBφ hmean
    obtain ⟨H₀, hH₀two, hsupport⟩ := hcφ.isBounded.subset_closedBall_lt 2 (e 0)
    obtain ⟨q₀, hq₀⟩ := pow_unbounded_of_one_lt (2 * H₀) (by norm_num : (1 : ℝ) < 2)
    have hH₀ : 0 ≤ H₀ := by linarith
    let η := radialUnitCutoff (e 0) 1
    have hη := radialUnitCutoff_lipschitz (e 0) 1
    have hBη : ∀ x, |η x| ≤ (1 : ℝ≥0) := by
      intro x
      rw [abs_of_nonneg (radialUnitCutoff_bounds (e 0) 1 x).1]
      exact (radialUnitCutoff_bounds (e 0) 1 x).2
    have hsη : ∀ x, η x ≠ 0 → dist x (e 0) ≤ H₀ := by
      intro x hx
      exact (radialUnitCutoff_support_bound (e 0) 1 x hx).trans (by linarith)
    have he0 : e 0 = a := by rw [hplane]; simp [affinePlaneSection]
    have hbump : (∫ x, η x ∂coordinatePlaneMeasure e) ≠ 0 := by
      change (∫ x, radialUnitCutoff (e 0) 1 x ∂coordinatePlaneMeasure e) ≠ 0
      rw [he0, hplane]
      exact ne_of_gt (radialUnitCutoff_plane_integral_pos a L)
    have hDyadic : ∀ q : ℕ, q₀ ≤ q → heightPairingOn (p + 1) (coordinatePlaneMeasure e)
        (e 0) (ball (e 0) ((2 : ℝ) ^ q)) f φ = 0 := by
      intro q hq
      have hR : 0 < (2 : ℝ) ^ q := by positivity
      have hHR : 2 * H₀ ≤ (2 : ℝ) ^ q := hq₀.le.trans (pow_le_pow_right₀ (by norm_num) hq)
      obtain ⟨B, hGB, hshell⟩ := controlled_shell_moments_from_dyadic_balls (p + 1) σ (e 0) u δ N D b
        (G * 2 ^ (p + 1)) huL2 hsource q
      obtain ⟨hN', hlast'⟩ := dyadic_shifted_last_error_tendsto q N δ hN hlast
      obtain ⟨J, hJ⟩ := exists_nat_ge (2 * (2 : ℝ) ^ q * ((Q : ℝ) + 1))
      obtain ⟨Bfar, hBfar, _, hball⟩ := comparable_ball_moments_from_dyadic_control (p + 1) σ (e 0)
        (fun j x => u j x / δ j) N hN D b hwL2 hnorm (((K : ℝ) + 1) * ((J : ℝ) + 1))
        ((2 : ℝ) ^ q) ((2 * (Q : ℝ)) ^ (p + 1) * 2 ^ (p + 1)) hR
      exact (hEq H₀ ((2 : ℝ) ^ q) hH₀ hR hHR B b (fun j => N j - (q + 1))
        hGB hb0 hb2 hN' hlast' hshell φ η Jφ 1 Bφ 1 hφ hη hcφ
        (radialUnitCutoff_hasCompactSupport (e 0) 1) hBφ hBη
        (fun x hx => hsupport (subset_tsupport φ hx)) hsη hmean hbump).2 J Bfar hJ hBfar hball
    refine ⟨(2 : ℝ) ^ q₀, by positivity, ?_⟩
    intro R hR
    have hRp : 0 < R := (by positivity : 0 < (2 : ℝ) ^ q₀).trans_le hR
    have hsame := heightPairingOn_ball_independent_from_local_energy p ((2 * (Q : ℝ)) ^ (p + 1))
      (coordinatePlaneMeasure e) hνg (e 0) f φ hfm (fun T _ => (hdata T).1)
      (fun T _ => (hdata T).2) Jφ Bφ hφ hcφ hBφ hmean H₀ R ((2 : ℝ) ^ q₀)
      hH₀ hRp (by positivity) (hq₀.le.trans hR) hq₀.le
      (fun x hx => hsupport (subset_tsupport φ hx)) (hTail R hRp) (hTail _ (by positivity))
    exact hsame.trans (hDyadic q₀ le_rfl)

  have he0 : e 0 = a := by rw [hplane]; simp [affinePlaneSection]
  let : IsFiniteMeasure ((coordinatePlaneMeasure e).restrict (ball (e 0) 1)) :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) ((2 * (Q : ℝ)) ^ (p + 1))
      (coordinatePlaneMeasure e) hνg (e 0) 1 (by norm_num)
  have hnearOne : IntegrableOn f (ball a 1) (coordinatePlaneMeasure (affinePlaneSection a L)) := by
    have hi : IntegrableOn f (ball (e 0) 1) (coordinatePlaneMeasure e) :=
      (hdata 1).1.integrable (by norm_num)
    rw [he0, hplane] at hi
    exact hi
  have htailOne : IntegrableOn (fun x => |f x| * inverseDistancePow (p + 1 + 2) a x)
      (closedExterior a 1) (coordinatePlaneMeasure (affinePlaneSection a L)) := by
    have hi := hTail 1 (by norm_num)
    rw [he0, hplane] at hi
    exact hi
  obtain ⟨T, hT⟩ := exists_intrinsic_height_distribution_from_tail (p + 1 + 2) a L f hfm
    1 (by norm_num) hnearOne htailOne
  refine ⟨ρ, hρ, f, hfm, hf, hsecond, hmoment, hfenergy, hTail, hCompact, T, hT, ?_⟩
  intro g hc hg v
  apply intrinsic_directional_equation_of_ambient a L f _ g hc hg v
  intro φ J B hcφ hφ hB _ hmean
  have hm : (∫ x, φ x ∂coordinatePlaneMeasure e) = 0 := by
    simpa only [hplane] using! hmean
  have hi := hCompact φ J B hcφ hφ hB hm
  rw [he0, hplane] at hi
  exact hi

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_IntrinsicHeightData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem affine_plane_ball_preimage {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (R : ℝ) :
    (fun u : Ambient n => a + L u) ⁻¹' ball a R = ball 0 R := by
  ext u
  simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero, L.norm_map]

theorem affine_plane_exterior_preimage {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (R : ℝ) :
    (fun u : Ambient n => a + L u) ⁻¹' closedExterior a R = closedExterior 0 R := by
  rw [closedExterior_eq_compl_ball, preimage_compl, affine_plane_ball_preimage,
    ← closedExterior_eq_compl_ball]

theorem affine_plane_integrableOn_iff {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (F : Ambient d → ℝ) :
    IntegrableOn F s (coordinatePlaneMeasure (affinePlaneSection a L)) ↔
      IntegrableOn (fun u : Ambient n => F (a + L u))
        ((fun u : Ambient n => a + L u) ⁻¹' s) volume := by
  have he : Isometry (fun u : Ambient n => a + L u) := by
    apply Isometry.of_dist_eq
    intro u v
    simp only [dist_add_left, L.dist_map]
  rw [IntegrableOn, coordinatePlaneMeasure_affine_eq_map,
    Measure.restrict_map he.continuous.measurable hs]
  exact he.isClosedEmbedding.measurableEmbedding.integrable_map_iff

theorem height_local_integrable_affine_pullback {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ) (R : ℝ)
    (hi : IntegrableOn f (ball a R) (coordinatePlaneMeasure (affinePlaneSection a L))) :
    IntegrableOn (fun u : Ambient n => f (a + L u)) (ball 0 R) volume := by
  simpa only [affine_plane_ball_preimage] using!
    (affine_plane_integrableOn_iff a L (ball a R) measurableSet_ball f).mp hi

theorem height_tail_integrable_affine_pullback {n d : ℕ} (q : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ) (R : ℝ)
    (hi : IntegrableOn (fun x => |f x| * inverseDistancePow q a x) (closedExterior a R)
      (coordinatePlaneMeasure (affinePlaneSection a L))) :
    IntegrableOn (fun u : Ambient n => |f (a + L u)| * inverseDistancePow q 0 u)
      (closedExterior 0 R) volume := by
  have h := (affine_plane_integrableOn_iff a L (closedExterior a R)
    (closedExterior_measurable a R) (fun x => |f x| * inverseDistancePow q a x)).mp hi
  have hd (u : Ambient n) : dist a (a + L u) = dist (0 : Ambient n) u := by
    simpa only [map_zero, add_zero] using!
      (show dist (a + L 0) (a + L u) = dist (0 : Ambient n) u from by
        rw [dist_add_left, L.dist_map])
  simpa only [affine_plane_exterior_preimage, inverseDistancePow, hd] using! h

theorem height_energy_integrable_affine_pullback {n d : ℕ} (m : ℕ) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ) (R : ℝ)
    (hi : Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m f q.1 q.2)
      (((coordinatePlaneMeasure (affinePlaneSection a L)).restrict (ball a R)).prod
        ((coordinatePlaneMeasure (affinePlaneSection a L)).restrict (ball a R)))) :
    Integrable (fun q : Ambient n × Ambient n =>
      fractionalPairEnergy m (fun u => f (a + L u)) q.1 q.2)
      ((volume.restrict (ball (0 : Ambient n) R)).prod (volume.restrict (ball 0 R))) := by
  have h := (affine_plane_pair_integrable_iff a L (ball a R) (ball a R)
    measurableSet_ball measurableSet_ball
    (fun q => fractionalPairEnergy m f q.1 q.2)).mp hi
  simpa only [affine_plane_ball_preimage, fractionalPairEnergy, dist_add_left, L.dist_map] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_IntrinsicCompactEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set SchwartzMap
open scoped NNReal

theorem intrinsic_compact_schwartz_equation_of_ambient {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ)
    (hambient : ∀ (φ : Ambient d → ℝ) (J B : ℝ≥0),
      HasCompactSupport φ → LipschitzWith J φ → (∀ x, |φ x| ≤ (B : ℝ)) →
      Integrable φ (coordinatePlaneMeasure (affinePlaneSection a L)) →
      (∫ x, φ x ∂coordinatePlaneMeasure (affinePlaneSection a L)) = 0 →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        heightPairingOn n (coordinatePlaneMeasure (affinePlaneSection a L)) a (ball a R) f φ = 0)
    (g : 𝓢(Ambient n, ℝ)) (hc : HasCompactSupport g) (hg : (∫ x, g x) = 0) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      heightPairingOn n volume (0 : Ambient n) (ball 0 R) (fun u => f (a + L u)) g = 0 := by
  obtain ⟨K, B, hK, hB⟩ := schwartz_real_bounded_lipschitz g
  obtain ⟨φ, J, hcφ, hφ, hBφ, hext, hI, hmean⟩ :=
    exists_compact_ambient_plane_test a L g hc K B hK hB
  obtain ⟨R₀, hR₀, hR⟩ := hambient φ J B hcφ hφ hBφ hI (hmean.trans hg)
  refine ⟨R₀, hR₀, fun R hRR => ?_⟩
  have h := hR R hRR
  rw [heightPairingOn_affine_pullback] at h
  have heq : (fun u => φ (a + L u)) = g := funext hext
  rwa [heq] at h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_CommonHeightFractionalEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The intrinsic fractional equation for a common height

Local square integrability, pair energy, and tail bounds on a coordinate plane pull back along
its affine isometry. Ambient compact-test equations therefore imply the fractional equation
for every intrinsic mean-zero Schwartz test.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function SchwartzMap
open scoped NNReal

theorem common_height_fractional_equation {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (a : Ambient d) (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (hplane : e = affinePlaneSection a L)
    (f : Ambient d → ℝ) (hfm : Measurable f)
    (hf : ∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))
    (henergy : ∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
      (((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))))
    (htail : ∀ R : ℝ, 0 < R → IntegrableOn
      (fun x => |f x| * inverseDistancePow (p + 1 + 2) (e 0) x)
      (closedExterior (e 0) R) (coordinatePlaneMeasure e))
    (hcompact : ∀ (φ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport φ → LipschitzWith J φ →
      (∀ x, |φ x| ≤ (B : ℝ)) → (∫ x, φ x ∂coordinatePlaneMeasure e) = 0 →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        heightPairingOn (p + 1) (coordinatePlaneMeasure e) (e 0) (ball (e 0) R) f φ = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hg : (∫ x, g x) = 0) :
    (∫ x, f (a + L x) • fractionalSchwartzTest p g x) = 0 := by
  have he0 : e 0 = a := by rw [hplane]; simp [affinePlaneSection]
  have hνg : GlobalUpperGrowth (p + 1) ((2 * (Q : ℝ)) ^ (p + 1)) (coordinatePlaneMeasure e) := by
    simpa only [Fintype.card_fin] using! coordinatePlaneMeasure_upper_growth e π
      he.continuous.measurable Q hπ hleft
  let := hνg.finite_on_compacts
  have hdata := local_height_data_on_balls (p + 1) e π K Q hπ hleft (coordinatePlaneMeasure e)
    f hf henergy
  apply schwartz_fractional_equation_of_real_pairing p 0 (fun x => f (a + L x))
    (hfm.comp (show Measurable (fun x : Ambient (p + 1) => a + L x) by fun_prop))
    ?_ ?_ ?_ ?_ g hg
  · intro R hR
    let : IsFiniteMeasure ((coordinatePlaneMeasure e).restrict (ball (e 0) R)) :=
      finiteMeasure_restrict_ball_of_globalGrowth (p + 1) ((2 * (Q : ℝ)) ^ (p + 1))
        (coordinatePlaneMeasure e) hνg (e 0) R hR
    have hi : IntegrableOn f (ball (e 0) R) (coordinatePlaneMeasure e) :=
      (hdata R).1.integrable (by norm_num)
    rw [he0, hplane] at hi
    exact height_local_integrable_affine_pullback a L f R hi
  · intro R hR
    have hi := htail R hR
    rw [he0, hplane] at hi
    exact height_tail_integrable_affine_pullback (p + 1 + 2) a L f R hi
  · intro R _
    have hi := (hdata R).2
    rw [he0, hplane] at hi
    exact height_energy_integrable_affine_pullback (p + 1) a L f R hi
  · intro φ hc hφ
    apply intrinsic_compact_schwartz_equation_of_ambient a L f ?_ φ hc hφ
    intro ψ J B hcψ hψ hB _ hmean
    have hm : (∫ x, ψ x ∂coordinatePlaneMeasure e) = 0 := by
      simpa only [hplane] using! hmean
    have hi := hcompact ψ J B hcψ hψ hB hm
    rw [he0, hplane] at hi
    exact hi

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_DyadicCommonFractionalEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A common dyadic height satisfying the fractional equation

The subsequential height obtained from dyadic growth bounds retains its local second moments,
test moments, energy, and tail control. Applying the common-height fractional equation adds
vanishing against mean-zero fractional Schwartz tests without changing the subsequence or the
associated tempered distribution and directional equations.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology SchwartzMap
open scoped NNReal ENNReal ContDiff

theorem exists_common_height_with_fractional_equation_oai {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (a : Ambient d) (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (hplane : e = affinePlaneSection a L)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)] [∀ j, SFinite (σ j)]
    (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e))
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (σ j))
    (hlower : ∀ j x, x ∈ (σ j).support → ∀ r : ℝ, AdmissibleRadius (σ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (σ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (σ j).support)
    (u : ℕ → Ambient d → ℝ) (Ku : ℝ≥0) (hu : ∀ j, LipschitzWith Ku (u j))
    (z : ℕ → Ambient d) (hz : ∀ j, ‖z j‖ ≤ 1)
    (hdiff : ∀ j x y, u j x - u j y = inner ℝ (z j) (x - y))
    (δ A v : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (σ j) (e 0) (A j) (v j))
    (hratio : Tendsto (fun j => v j / δ j) atTop (𝓝 0))
    (W : ℝ) (hW : ∀ j, |u j (e 0)| ≤ W)
    (hw : ∀ H j, MemLp (fun x => u j x / δ j) 2
      ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B₀ E₀ : ℕ → ℝ)
    (hB₀ : ∀ H j, (∫ x, (u j x / δ j) ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B₀ H)
    (henergy : ∀ H j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2)
      (((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H))))
    (hE₀ : ∀ H j, (∫ q : Ambient d × Ambient d,
      fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2
      ∂(((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball (e 0) ((2 : ℝ) ^ l), u j x ^ 2 ∂σ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ f : Ambient d → ℝ, Measurable f ∧
      (∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
      (∀ H, Tendsto (fun j => ∫ x, (u (ρ j) x / δ (ρ j)) ^ 2
        ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
        (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      (∀ H (ψ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport ψ →
        LipschitzWith J ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
        Tendsto (fun j => ∫ x, (u (ρ j) x / δ (ρ j)) * ψ x
          ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
          (𝓝 (∫ x, f x * ψ x
            ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      (∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
        (((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
          ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
        (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) f q.1 q.2
          ∂(((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
            ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H) ∧
      (∀ R : ℝ, 0 < R → IntegrableOn
        (fun x => |f x| * inverseDistancePow (p + 1 + 2) (e 0) x)
        (closedExterior (e 0) R) (coordinatePlaneMeasure e)) ∧
      (∀ (φ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport φ → LipschitzWith J φ →
        (∀ x, |φ x| ≤ (B : ℝ)) → (∫ x, φ x ∂coordinatePlaneMeasure e) = 0 →
        ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
          heightPairingOn (p + 1) (coordinatePlaneMeasure e) (e 0) (ball (e 0) R) f φ = 0) ∧
      (∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
        (∫ x, f (a + L x) • fractionalSchwartzTest p g x) = 0) ∧
      ∃ T : 𝓢'(Ambient (p + 1), ℂ),
        (∀ ψ : 𝓢(Ambient (p + 1), ℂ),
          Integrable (fun x : Ambient (p + 1) => f (a + L x) • ψ x)
            (volume : Measure (Ambient (p + 1))) ∧
          T ψ = ∫ x : Ambient (p + 1), f (a + L x) • ψ x) ∧
        ∀ g : Ambient (p + 1) → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
          ∀ v : Ambient (p + 1), ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
            heightPairingOn (p + 1) volume (0 : Ambient (p + 1)) (ball 0 R)
              (fun x => f (a + L x)) (fun x => fderiv ℝ g x v) = 0 := by
  obtain ⟨ρ, hρ, f, hfm, hf, hsecond, hmoment, hfenergy, hTail, hCompact, T, hT, hDir⟩ :=
    exists_common_height_with_intrinsic_equation p e π K Q he hπ hleft a L hplane
      σ hlocal C G hC hg hlower hdiam u Ku hu z hz hdiff δ A v hδ hA hosc hratio W hW
      hw B₀ E₀ hB₀ henergy hE₀ N hN D b hb0 hb2 hlast hsource
  refine ⟨ρ, hρ, f, hfm, hf, hsecond, hmoment, hfenergy, hTail, hCompact, ?_, T, hT, hDir⟩
  exact common_height_fractional_equation p e π K Q he hπ hleft a L hplane f hfm hf
    (fun H => (hfenergy H).1) hTail hCompact

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.exists_common_height_with_fractional_equation_oai := @OAI.RieszRectifiability.exists_common_height_with_fractional_equation_oai
