-- Prove2me | solution 1 for OAI.RieszRectifiability.quantitative_selected_restart_uniform_deficit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:56.167666+00:00
-- url     : https://prove2.me/submissions/1ae54a12-7590-4df3-960f-79ce558a04e8

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000
import Theorems.Thm_OAI_RieszRectifiability_exists_uniform_bad_descendant_total_mass
import Theorems.Thm_OAI_RieszRectifiability_exists_uniform_dyadic_chain_propagation
import Theorems.Thm_OAI_RieszRectifiability_exists_uniform_no_flat_descendant_total_mass

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_PlanarPullbackMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Pullback along the adjoint of an isometric embedding transports a measure supported on
its range to Euclidean coordinates, preserving ball masses and upper growth bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem globalGrowth_finite_on_compacts {n d : ℕ} (C : ℝ)
    (ν : Measure (Ambient d)) (hg : GlobalUpperGrowth n C ν) : IsFiniteMeasureOnCompacts ν := by
  let : IsLocallyFiniteMeasure ν := ⟨fun x => ⟨ball x 1, ball_mem_nhds x zero_lt_one,
    (hg.2 x 1 zero_lt_one).trans_lt ENNReal.ofReal_lt_top⟩⟩
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LeastSquaredExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Least-squared approximation by affine planes

The squared excess minimizes the radius-normalized quadratic distance over affine planes
of the prescribed dimension. Local finiteness ensures that these distance integrals exist
on balls.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem squared_infDist_integrableOn_ball {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (a : Ambient d) (r : ℝ)
    (s : Set (Ambient d)) (hs : s.Nonempty) :
    IntegrableOn (fun x => infDist x s ^ 2) (ball a r) μ := by
  have : IsFiniteMeasure (μ.restrict (ball a r)) := isFiniteMeasure_restrict.mpr
    (ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a r).measure_lt_top))
  obtain ⟨p, hp⟩ := hs
  have hm : MemLp (fun x => infDist x s) 2 (μ.restrict (ball a r)) := by
    apply MemLp.of_bound (continuous_infDist_pt s).aestronglyMeasurable (r + dist a p)
    filter_upwards [ae_restrict_mem (μ := μ) measurableSet_ball] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg infDist_nonneg]
    have hx' : dist x a ≤ r := hx.le
    exact (infDist_le_dist_of_mem hp).trans ((dist_triangle x a p).trans
      (add_le_add hx' (le_refl (dist a p))))
  exact hm.integrable_sq

theorem quadraticPlaneError_nonneg {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r) (S : AffineSubspace ℝ (Ambient d)) :
    0 ≤ quadraticPlaneError n μ a r S :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hr _))
    (integral_nonneg fun x => sq_nonneg (infDist x (S : Set (Ambient d))))

theorem squaredExcess_le_planeError {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) :
    squaredExcess n μ a r ≤ quadraticPlaneError n μ a r S := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨T, _hT, rfl⟩
    exact quadraticPlaneError_nonneg n μ a r hr T
  · exact ⟨S, hS, rfl⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BilateralBeta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem directedBallDeviation_nonneg {d : ℕ} (s t : Set (Ambient d))
    (a : Ambient d) (r : ℝ) : 0 ≤ directedBallDeviation s t a r := by
  apply Real.sSup_nonneg
  rintro v ⟨x, _, rfl⟩
  exact infDist_nonneg

theorem directedBallDeviation_le {d : ℕ} (s t : Set (Ambient d))
    (a : Ambient d) (r η : ℝ) (hη : 0 ≤ η)
    (hpoint : ∀ x ∈ ball a r, x ∈ s → infDist x t ≤ η) :
    directedBallDeviation s t a r ≤ η := by
  apply Real.sSup_le _ hη
  rintro v ⟨x, hx, rfl⟩
  exact hpoint x hx.1 hx.2

theorem bilateralPlaneError_nonneg {d : ℕ} (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r) (S : AffineSubspace ℝ (Ambient d)) :
    0 ≤ bilateralPlaneError μ a r S :=
  div_nonneg (add_nonneg (directedBallDeviation_nonneg _ _ a r)
    (directedBallDeviation_nonneg _ _ a r)) hr

theorem bilateralBeta_le_planeError {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) :
    bilateralBeta n μ a r ≤ bilateralPlaneError μ a r S := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨T, _, rfl⟩
    exact bilateralPlaneError_nonneg μ a r hr T
  · exact ⟨S, hS, rfl⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SeparatedSupportNets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Maximal separated extensions give covering nets. Positive separation also gives discreteness,
countability in separable spaces, and finiteness on compact sets.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set TopologicalSpace

theorem separated_set_countable {X : Type*} [MetricSpace X] [SeparableSpace X]
    (N : Set X) (r : ℝ) (hr : 0 < r)
    (hsep : N.Pairwise fun x y => r ≤ dist x y) : N.Countable := by
  have hd : N.PairwiseDisjoint (fun x => ball x (r / 2)) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    linarith [hsep hx hy hxy]
  exact hd.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun x _ => ⟨x, mem_ball_self (by positivity)⟩)

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ADHoleDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
AD lower bounds and global upper growth quantify the density lost to a ball-shaped hole.
Persistent holes at vanishing scales force a measurable set to have zero measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem ballHoleDensityDefect_pos (n : ℕ) (C G : ℝ) (hC : 0 < C) (hG : 0 < G) :
    0 < ballHoleDensityDefect n C G := by
  unfold ballHoleDensityDefect
  positivity

theorem ad_ball_hole_density_bound {n d : ℕ} (μ : Measure (Ambient d)) (C G : ℝ)
    (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (A : Set (Ambient d)) (x z : Ambient d) (r : ℝ) (hr : 0 < r)
    (hz : z ∈ μ.support) (hnear : dist x z ≤ r) (hcore : AdmissibleRadius μ (r / 4))
    (hhole : Disjoint A (ball z (r / 4))) :
    0 < μ.real (closedBall x (2 * r)) ∧
      μ.real (A ∩ closedBall x (2 * r)) / μ.real (closedBall x (2 * r)) ≤
        1 - ballHoleDensityDefect n C G := by
  have hsub : ball z (r / 4) ⊆ closedBall x (2 * r) := by
    intro y hy
    change dist y x ≤ 2 * r
    have ht := dist_triangle y z x
    rw [dist_comm z x] at ht
    change dist y z < r / 4 at hy
    linarith
  have hbig : μ (closedBall x (2 * r)) ≤ ENNReal.ofReal (G * (3 * r) ^ n) :=
    (measure_mono (closedBall_subset_ball (by linarith : 2 * r < 3 * r))).trans
      (hg.2 x (3 * r) (by positivity))
  have hfin : μ (closedBall x (2 * r)) ≠ ∞ := (hbig.trans_lt ENNReal.ofReal_lt_top).ne
  have hholefin := measure_ne_top_of_subset hsub hfin
  have hsmall : (r / 4) ^ n / C ≤ μ.real (ball z (r / 4)) := by
    have h := ENNReal.toReal_mono hholefin (hlower z hz (r / 4) hcore)
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (r / 4) ^ n / C), Measure.real] using! h
  have hpos : 0 < μ.real (closedBall x (2 * r)) :=
    (by positivity : 0 < (r / 4) ^ n / C).trans_le
      (hsmall.trans (measureReal_mono hsub hfin))
  refine ⟨hpos, ?_⟩
  have hsum : μ.real (A ∩ closedBall x (2 * r)) + μ.real (ball z (r / 4)) ≤
      μ.real (closedBall x (2 * r)) := by
    rw [← measureReal_union (hhole.mono_left inter_subset_left) measurableSet_ball
      (measure_ne_top_of_subset inter_subset_right hfin) hholefin]
    exact measureReal_mono (union_subset inter_subset_right hsub) hfin
  have hupper : μ.real (closedBall x (2 * r)) ≤ G * (3 * r) ^ n :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hbig
  have hidentity : ballHoleDensityDefect n C G * (G * (3 * r) ^ n) = (r / 4) ^ n / C := by
    unfold ballHoleDensityDefect
    simp only [mul_pow, div_pow]
    field_simp
  have hdef : ballHoleDensityDefect n C G * μ.real (closedBall x (2 * r)) ≤
      μ.real (ball z (r / 4)) := by
    calc
      _ ≤ ballHoleDensityDefect n C G * (G * (3 * r) ^ n) :=
        mul_le_mul_of_nonneg_left hupper (ballHoleDensityDefect_pos n C G hC hG).le
      _ = _ := hidentity
      _ ≤ _ := hsmall
  apply (div_le_iff₀ hpos).mpr
  linarith

theorem measurable_set_null_of_uniform_ball_holes {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (A : Set (Ambient d)) (hA : MeasurableSet A)
    (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (ht : Tendsto r atTop (𝓝 0))
    (hcore : ∀ k, AdmissibleRadius μ (r k / 4))
    (hhole : ∀ x ∈ A, ∀ k, ∃ z ∈ μ.support, dist x z ≤ r k ∧ Disjoint A (ball z (r k / 4))) :
    μ A = 0 := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  have hrt : Tendsto (fun k => 2 * r k) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall (fun k => ?_)⟩
    · simpa only [mul_zero] using! ht.const_mul 2
    · change 0 < 2 * r k
      exact mul_pos (by norm_num) (hr k)
  have hzero : ∀ᵐ x ∂μ.restrict A, False := by
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ A, ae_restrict_mem hA] with x hx hxA
    have hd := hx.comp hrt
    have hdreal : Tendsto (fun k => μ.real (A ∩ closedBall x (2 * r k)) /
        μ.real (closedBall x (2 * r k))) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_one, Measure.real] using!
        (ENNReal.continuousAt_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞)).tendsto.comp hd
    have hb : (1 : ℝ) ≤ 1 - ballHoleDensityDefect n C G := by
      apply le_of_tendsto hdreal
      apply Filter.Eventually.of_forall
      intro k
      obtain ⟨z, hz, hnear, hh⟩ := hhole x hxA k
      exact (ad_ball_hole_density_bound μ C G hC hG hg hlower A x z (r k) (hr k)
        hz hnear (hcore k) hh).2
    have hp := ballHoleDensityDefect_pos n C G hC hG
    linarith
  simpa using! (ae_iff.mp hzero)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_NetDescendantCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem netDescendants_subset {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E) : netDescendants N k z ⊆ E := by
  rintro x ⟨t, hx, _, _⟩
  exact hx

theorem closedNetCell_isClosed {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E) : IsClosed (closedNetCell N k z) :=
  isClosed_closure

theorem closedNetCell_subset {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (hE : IsClosed E) (k : ℕ) (z : E) :
    closedNetCell N k z ⊆ E :=
  hE.closure_subset_iff.mpr (netDescendants_subset N k z)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ClosedNetCellCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Covering by closed net cells

The geometric decay of lattice radii lets fine net points approximate every point of the
underlying set. Ancestor forcing places relative balls inside their closed cells, while
properness reduces nearby ancestors to finitely many choices and yields a closed-cell cover.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set Filter Topology

theorem exists_closedNetCell_containing {X : Type*} [MetricSpace X] [ProperSpace X]
    {E : Set X} (R : ℝ) (hR : 0 < R)
    (N : (k : ℕ) → SeparatedCover E (latticeRadius R k)) (k : ℕ) (y : E) :
    ∃ z : E, (z : X) ∈ (N k).points ∧ (y : X) ∈ closedNetCell N k z := by
  classical
  let S := (N k).points ∩ closedBall (y : X) (3 * latticeRadius R k)
  have hS : S.Finite := separated_set_finite_inter_compact _ _ (latticeRadius R k)
    (latticeRadius_pos R hR k) (N k).separated (isCompact_closedBall _ _)
  let : Fintype S := hS.fintype
  let center : S → E := fun z => ⟨z, (N k).subset z.property.1⟩
  have hclosure : (y : X) ∈ closure (⋃ z : S, netDescendants N k (center z)) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨t, ht⟩ := exists_latticeRadius_tail_lt R hR k ε hε
    obtain ⟨x, hxN, hyx⟩ := (N (k + t + 1)).covers y y.property
    have hxE := (N (k + t + 1)).subset hxN
    let z := netAncestor N k (t + 1) ⟨x, hxE⟩
    have hzN : (z : X) ∈ (N k).points := netAncestor_mem N k t _
    have hzy : dist (z : X) (y : X) ≤ 3 * latticeRadius R k := by
      have hd := dist_triangle (z : X) x (y : X)
      rw [dist_comm (z : X) x, dist_comm x (y : X)] at hd
      have ha := netAncestor_dist_le_latticeRadius R hR N k (t + 1) ⟨x, hxE⟩
      have hs := latticeRadius_antitone R hR.le (show k ≤ k + t + 1 by omega)
      change dist x (z : X) ≤ _ at ha
      linarith
    let w : S := ⟨z, ⟨hzN, hzy⟩⟩
    refine ⟨x, mem_iUnion.mpr ⟨w, ?_⟩, hyx.trans ht⟩
    refine ⟨t + 1, hxE, ?_, ?_⟩
    · simpa only [Nat.add_succ] using! hxN
    · rfl
  rw [closure_iUnion_of_finite] at hclosure
  obtain ⟨z, hz⟩ := mem_iUnion.mp hclosure
  exact ⟨center z, z.property.1, hz⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ConstructedSupportCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem supportLatticeNets_countable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) : (supportLatticeNets μ R hR k).points.Countable :=
  separated_set_countable _ _ (latticeRadius_pos R hR k) (supportLatticeNets μ R hR k).separated

theorem supportLatticeCell_closed {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : IsClosed (supportLatticeCell μ R hR k z) :=
  closedNetCell_isClosed _ _ _

theorem supportLatticeCell_subset_support {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : supportLatticeCell μ R hR k z ⊆ μ.support :=
  closedNetCell_subset _ μ.isClosed_support _ _

theorem supportLatticeCell_cover {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (x : Ambient d) (hx : x ∈ μ.support) :
    ∃ z : (supportLatticeNets μ R hR k).points, x ∈ supportLatticeCell μ R hR k z := by
  obtain ⟨z, hz, hcell⟩ := exists_closedNetCell_containing R hR (supportLatticeNets μ R hR) k ⟨x, hx⟩
  exact ⟨⟨z, hz⟩, hcell⟩

theorem supportLatticeCell_compact {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : IsCompact (supportLatticeCell μ R hR k z) :=
  (isCompact_closedBall (z : Ambient d) (2 * latticeRadius R k)).of_isClosed_subset
    (supportLatticeCell_closed μ R hR k z) (supportLatticeCell_bounds μ R hR k z).2

theorem supportLatticeCell_measure_bounds {n d : ℕ} (μ : Measure (Ambient d)) (C G : ℝ)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    ENNReal.ofReal ((latticeRadius R k / 8) ^ n / C) ≤ μ (supportLatticeCell μ R hR k z) ∧
      μ (supportLatticeCell μ R hR k z) ≤ ENNReal.ofReal (G * (3 * latticeRadius R k) ^ n) := by
  have hball : μ (μ.support ∩ ball (z : Ambient d) (latticeRadius R k / 8)) =
      μ (ball (z : Ambient d) (latticeRadius R k / 8)) := by
    apply measure_congr
    filter_upwards [μ.support_mem_ae] with x hx
    apply propext
    change (x ∈ μ.support ∧ x ∈ ball (z : Ambient d) (latticeRadius R k / 8)) ↔
      x ∈ ball (z : Ambient d) (latticeRadius R k / 8)
    simp only [hx, true_and]
  constructor
  · calc
      _ ≤ μ (ball (z : Ambient d) (latticeRadius R k / 8)) :=
        hlower z ((supportLatticeNets μ R hR k).subset z.property) _ hcore
      _ = _ := hball.symm
      _ ≤ _ := measure_mono (supportLatticeCell_bounds μ R hR k z).1
  · have hsub : closedBall (z : Ambient d) (2 * latticeRadius R k) ⊆
        ball (z : Ambient d) (3 * latticeRadius R k) :=
      closedBall_subset_ball (by have hp := latticeRadius_pos R hR k; linarith)
    apply (measure_mono ((supportLatticeCell_bounds μ R hR k z).2.trans hsub)).trans
    exact hg.2 z _ (mul_pos (by norm_num) (latticeRadius_pos R hR k))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SupportCellOverlaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Null overlaps of support lattice cells

The countable union of intersections of distinct closed cells is measurable and avoids
every deep core ball. Upper growth and lower AD bounds turn these holes into nullity;
when a core radius exceeds the support diameter, separation makes the overlap empty.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem supportLatticeOverlap_measurable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ)
    (hR : 0 < R) (k : ℕ) : MeasurableSet (supportLatticeOverlap μ R hR k) := by
  classical
  let : Countable (supportLatticeNets μ R hR k).points :=
    (supportLatticeNets_countable μ R hR k).to_subtype
  apply MeasurableSet.iUnion
  intro z
  apply MeasurableSet.iUnion
  intro w
  split_ifs
  · exact MeasurableSet.empty
  · exact (supportLatticeCell_closed μ R hR k z).measurableSet.inter
      (supportLatticeCell_closed μ R hR k w).measurableSet

theorem supportLatticeOverlap_subset_support {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ)
    (hR : 0 < R) (k : ℕ) : supportLatticeOverlap μ R hR k ⊆ μ.support := by
  intro x hx
  obtain ⟨z, _, _, hz, _⟩ := (mem_supportLatticeOverlap μ R hR k x).mp hx
  exact supportLatticeCell_subset_support μ R hR k z hz

theorem supportLatticeOverlap_null_of_admissible_core {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 4)) :
    μ (supportLatticeOverlap μ R hR k) = 0 := by
  apply measurable_set_null_of_uniform_ball_holes μ C G hC hG hg hlower
    (supportLatticeOverlap μ R hR k) (supportLatticeOverlap_measurable μ R hR k)
    (fun q => latticeRadius R (k + q)) (fun q => latticeRadius_pos R hR (k + q))
  · simpa only [latticeRadius_add, mul_zero] using!
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 64)
        (by norm_num : (1 / 64 : ℝ) < 1)).const_mul (latticeRadius R k)
  · intro q
    refine ⟨div_pos (latticeRadius_pos R hR (k + q)) (by norm_num), ?_⟩
    exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (latticeRadius_antitone R hR.le (Nat.le_add_right k q)) (by norm_num))).trans hcore.2
  · intro x hx q
    have hxE := supportLatticeOverlap_subset_support μ R hR k hx
    obtain ⟨z, hz, hnear⟩ := (supportLatticeNets μ R hR (k + q)).covers x hxE
    exact ⟨z, (supportLatticeNets μ R hR (k + q)).subset hz, hnear.le,
      supportLatticeOverlap_disjoint_deep_core μ R hR k q ⟨z, hz⟩⟩

theorem supportLatticeOverlap_null {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) : μ (supportLatticeOverlap μ R hR k) = 0 := by
  by_cases hcore : ENNReal.ofReal (latticeRadius R k / 4) ≤ ediam μ.support
  · exact supportLatticeOverlap_null_of_admissible_core μ C G hC hG hg hlower R hR k
      ⟨div_pos (latticeRadius_pos R hR k) (by norm_num), hcore⟩
  · have hempty : supportLatticeOverlap μ R hR k = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨z, w, hne, _, _⟩ := (mem_supportLatticeOverlap μ R hR k x).mp hx
      have hsep := (supportLatticeNets μ R hR k).separated z.property w.property
        (fun h => hne (Subtype.ext h))
      have hdiam := edist_le_ediam_of_mem
        ((supportLatticeNets μ R hR k).subset z.property)
        ((supportLatticeNets μ R hR k).subset w.property)
      apply hcore
      have hp := latticeRadius_pos R hR k
      have hd : latticeRadius R k / 4 ≤ dist (z : Ambient d) (w : Ambient d) := by linarith
      exact (ENNReal.ofReal_le_ofReal hd).trans (by simpa only [edist_dist] using! hdiam)
    rw [hempty, measure_empty]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_CleanSupportPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cleaning the support lattice partition

Removing the union of all cell overlaps produces nested, disjoint measurable cells that
cover the support outside one exceptional set. Net centers avoid that set, so cleaning
preserves the closed cells as closures. Under the growth bounds, it also preserves cell
mass and gives a unique cell at every scale almost everywhere.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem supportLatticeExceptional_measurable {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) : MeasurableSet (supportLatticeExceptional μ R hR) :=
  MeasurableSet.iUnion (supportLatticeOverlap_measurable μ R hR)

theorem supportLatticeExceptional_null {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) : μ (supportLatticeExceptional μ R hR) = 0 :=
  measure_iUnion_null (fun k => supportLatticeOverlap_null μ C G hC hG hg hlower R hR k)

theorem cleanSupportCell_measurable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ)
    (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    MeasurableSet (cleanSupportCell μ R hR k z) :=
  (supportLatticeCell_closed μ R hR k z).measurableSet.diff
    (supportLatticeExceptional_measurable μ R hR)

theorem cleanSupportCell_cover {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (x : Ambient d) (hx : x ∈ μ.support) (hgood : x ∉ supportLatticeExceptional μ R hR) :
    ∃ z : (supportLatticeNets μ R hR k).points, x ∈ cleanSupportCell μ R hR k z := by
  obtain ⟨z, hz⟩ := supportLatticeCell_cover μ R hR k x hx
  exact ⟨z, hz, hgood⟩

theorem cleanSupportCell_measure_eq {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    μ (cleanSupportCell μ R hR k z) = μ (supportLatticeCell μ R hR k z) :=
  measure_sdiff_null (supportLatticeExceptional_null μ C G hC hG hg hlower R hR)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_FiniteSupportRefinements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem cleanSupportCell_eq_iUnion_descendants {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k t : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    cleanSupportCell μ R hR k z =
      ⋃ w ∈ supportDescendantsAt μ R hR k t z, cleanSupportCell μ R hR (k + t) w := by
  ext x
  constructor
  · intro hx
    have hxE := supportLatticeCell_subset_support μ R hR k z hx.1
    obtain ⟨w, hw⟩ := cleanSupportCell_cover μ R hR (k + t) x hxE hx.2
    have hp := cleanSupportCell_nested μ R hR k t w hw
    have hanc : supportLatticeAncestor μ R hR k t w = z := by
      by_contra hne
      exact Set.disjoint_left.mp (cleanSupportCell_disjoint μ R hR k _ z hne) hp hx
    exact mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨hanc, hw⟩⟩
  · intro hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx
    obtain ⟨hanc, hxw⟩ := mem_iUnion.mp hw
    have hp := cleanSupportCell_nested μ R hR k t w hxw
    change supportLatticeAncestor μ R hR k t w = z at hanc
    simpa only [hanc] using! hp

theorem cleanSupportCell_measure_bounds {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    ENNReal.ofReal ((latticeRadius R k / 8) ^ n / C) ≤ μ (cleanSupportCell μ R hR k z) ∧
      μ (cleanSupportCell μ R hR k z) ≤ ENNReal.ofReal (G * (3 * latticeRadius R k) ^ n) := by
  rw [cleanSupportCell_measure_eq μ C G hC hG hg hlower R hR k z]
  exact supportLatticeCell_measure_bounds μ C G hg hlower R hR k hcore z

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_LatticeMassPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mass bounds for lattice descendants

Each descendant cell is contained in a ball with controlled radius. Global
upper growth therefore bounds its mass by a constant times the corresponding
power of its radius, both in extended and real-valued form.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem SupportCellDescendant.measure_upper {n d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (G : ℝ) (hg : GlobalUpperGrowth n G μ) :
    μ i.cell ≤ ENNReal.ofReal (G * (3 * i.radius) ^ n) := by
  have hr := i.radius_pos
  have hs := (supportLatticeCell_bounds μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩).2
  have hb : closedBall i.center (2 * i.radius) ⊆ ball i.center (3 * i.radius) :=
    closedBall_subset_ball (by linarith [i.radius_pos])
  exact (measure_mono ((sdiff_subset.trans hs).trans hb)).trans
    (hg.2 i.center (3 * i.radius) (by positivity))

theorem cleanSupportCell_real_measure_bounds {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    (latticeRadius R k / 8) ^ n / C ≤ μ.real (cleanSupportCell μ R hR k z) ∧
      μ.real (cleanSupportCell μ R hR k z) ≤ (G * 3 ^ n) * latticeRadius R k ^ n := by
  have hr := latticeRadius_pos R hR k
  have hb := cleanSupportCell_measure_bounds μ C G hC hG hg hlower R hR k hcore z
  have hf : μ (cleanSupportCell μ R hR k z) ≠ ∞ := (hb.2.trans_lt ENNReal.ofReal_lt_top).ne
  constructor
  · simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (latticeRadius R k / 8) ^ n / C),
      Measure.real] using! ENNReal.toReal_mono hf hb.1
  · have hu := ENNReal.toReal_le_of_le_ofReal
      (by positivity : 0 ≤ G * (3 * latticeRadius R k) ^ n) hb.2
    simpa only [mul_pow, mul_assoc, Measure.real] using! hu

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellChainGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem SupportCellDescendant.exists_ancestor_at_depth {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (h : ℕ) (hh : h ≤ i.depth) :
    ∃ j : SupportCellDescendant μ R hR k z,
      j.depth = h ∧ i.cell ⊆ j.cell ∧ i.center ∈ j.cell := by
  have hlevel : k + h + (i.depth - h) = k + i.depth := by omega
  let v : (supportLatticeNets μ R hR (k + h + (i.depth - h))).points :=
    ⟨i.center, by rw [hlevel]; exact i.mem_net⟩
  let w := supportLatticeAncestor μ R hR (k + h) (i.depth - h) v
  have hsub : i.cell ⊆ cleanSupportCell μ R hR (k + h) w := by
    have ht := cleanSupportCell_nested μ R hR (k + h) (i.depth - h) v
    have heq : cleanSupportCell μ R hR (k + h + (i.depth - h)) v = i.cell := by
      simp only [SupportCellDescendant.cell, cleanSupportCell, supportLatticeCell,
        supportLatticeCenter, v, hlevel]
    rw [← heq]
    exact ht
  have hc := hsub i.center_mem_cell
  have hanc : supportLatticeAncestor μ R hR k h w = z := by
    have ht := cleanSupportCell_nested μ R hR k h w hc
    have hz := i.cell_subset_top i.center_mem_cell
    by_contra hne
    exact Set.disjoint_left.mp (cleanSupportCell_disjoint μ R hR k _ z hne) ht hz
  let j : SupportCellDescendant μ R hR k z :=
    { depth := h, center := w, mem_net := w.property, ancestor := hanc }
  exact ⟨j, rfl, hsub, hc⟩

theorem SupportCellDescendant.dist_center_of_mem {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (a : Ambient d) (ha : a ∈ i.cell) :
    dist a i.center ≤ 2 * i.radius :=
  (supportLatticeCell_bounds μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩).2 ha.1

theorem SupportCellDescendant.cell_subset_of_center_mem {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i q : SupportCellDescendant μ R hR k z) (hq : q.depth ≤ i.depth)
    (hc : i.center ∈ q.cell) : i.cell ⊆ q.cell := by
  have hlevel : k + q.depth + (i.depth - q.depth) = k + i.depth := by omega
  let v : (supportLatticeNets μ R hR (k + q.depth + (i.depth - q.depth))).points :=
    ⟨i.center, by rw [hlevel]; exact i.mem_net⟩
  let w := supportLatticeAncestor μ R hR (k + q.depth) (i.depth - q.depth) v
  have hsub : i.cell ⊆ cleanSupportCell μ R hR (k + q.depth) w := by
    have ht := cleanSupportCell_nested μ R hR (k + q.depth) (i.depth - q.depth) v
    have heq : cleanSupportCell μ R hR (k + q.depth + (i.depth - q.depth)) v = i.cell := by
      simp only [SupportCellDescendant.cell, cleanSupportCell, supportLatticeCell,
        supportLatticeCenter, v, hlevel]
    rw [← heq]
    exact ht
  have hw : w = ⟨q.center, q.mem_net⟩ := by
    by_contra hne
    exact Set.disjoint_left.mp (cleanSupportCell_disjoint μ R hR (k + q.depth)
      w ⟨q.center, q.mem_net⟩ hne) (hsub i.center_mem_cell) hc
  rw [hw] at hsub
  exact hsub

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FlatCellCenterTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem HasFlatCell.mono {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (A B α β : ℝ)
    (hBA : B ≤ A) (hαβ : α ≤ β) (hflat : HasFlatCell n μ R hR k z A α) :
    HasFlatCell n μ R hR k z B β := by
  obtain ⟨S, hS, hf, hb⟩ := hflat
  have hr := (latticeRadius_pos R hR k).le
  have hsub := ball_subset_ball (x := (z : Ambient d)) (mul_le_mul_of_nonneg_right hBA hr)
  have hbound := mul_le_mul_of_nonneg_right hαβ hr
  exact ⟨S, hS, fun x hx hs => (hf x (hsub hx) hs).trans hbound,
    fun x hx hs => (hb x (hsub hx) hs).trans hbound⟩

theorem HasFlatCell.tube_at_descendant_center {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (H α : ℝ) (K : ℕ)
    (hH : 1 ≤ H) (hα : 0 ≤ α)
    (hflat : HasFlatCell n μ R hR k z (H * (2 : ℝ) ^ K + 2) α)
    (i : SupportCellDescendant μ R hR k z) :
    ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
      ∀ x ∈ ball i.center ((H * latticeRadius R k) * (2 : ℝ) ^ K), x ∈ μ.support →
        infDist x (S : Set (Ambient d)) ≤ α * (H * latticeRadius R k) := by
  obtain ⟨S, hS, hf, _⟩ := hflat
  refine ⟨S, hS, ?_⟩
  have hp := latticeRadius_pos R hR k
  have hsub : ball i.center ((H * latticeRadius R k) * (2 : ℝ) ^ K) ⊆
      ball (z : Ambient d) ((H * (2 : ℝ) ^ K + 2) * latticeRadius R k) := by
    apply ball_subset_outer_of_radius_dist
    have hi := i.center_dist_top
    nlinarith
  intro x hx hxs
  apply (hf x (hsub hx) hxs).trans
  have ht := mul_le_mul_of_nonneg_right hH hp.le
  have hu := mul_le_mul_of_nonneg_left ht hα
  simpa only [one_mul] using! hu

theorem HasFlatCell.beta_lt {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (A H α ε : ℝ)
    (hH : 0 < H) (hHA : H ≤ A) (hα : 0 ≤ α) (hsmall : 2 * α < ε * H)
    (hflat : HasFlatCell n μ R hR k z A α) :
    bilateralBeta n μ z (H * latticeRadius R k) < ε := by
  obtain ⟨S, hS, hf, hb⟩ := hflat
  have hr := latticeRadius_pos R hR k
  have hsub : ball (z : Ambient d) (H * latticeRadius R k) ⊆
      ball (z : Ambient d) (A * latticeRadius R k) :=
    ball_subset_ball (mul_le_mul_of_nonneg_right hHA hr.le)
  apply (bilateralBeta_le_planeError n μ z (H * latticeRadius R k)
    (mul_pos hH hr).le S hS).trans_lt
  have h1 := directedBallDeviation_le μ.support (S : Set (Ambient d)) z
    (H * latticeRadius R k) (α * latticeRadius R k) (mul_nonneg hα hr.le)
    (fun x hx hs => hf x (hsub hx) hs)
  have h2 := directedBallDeviation_le (S : Set (Ambient d)) μ.support z
    (H * latticeRadius R k) (α * latticeRadius R k) (mul_nonneg hα hr.le)
    (fun x hx hs => hb x (hsub hx) hs)
  apply (div_lt_iff₀ (mul_pos hH hr)).mpr
  nlinarith [mul_lt_mul_of_pos_right hsmall hr]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ExcessPropagationSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Filter Topology

theorem propagationScale_pos (j : ℕ) : 0 < propagationScale j := by
  unfold propagationScale
  positivity

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_DyadicPropagationRadii
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic descendant radii

The radius at depth `j` is the original radius divided by `2 ^ j`. Rescaling by
another dyadic power either returns to a shallower descendant or passes to a
larger original scale. Positivity and the support-diameter bound ensure that an
admissible dyadic horizon remains admissible for every descendant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem descendantRadius_pos (r : ℝ) (hr : 0 < r) (j : ℕ) : 0 < descendantRadius r j := by
  unfold descendantRadius
  positivity

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FlatSeedExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Support tubes and initial excess bounds

A support tube of width `η` around an affine `n`-plane bounds the normalized
squared excess on a ball of radius `R` by `G * (η / R) ^ 2` under global upper
growth. A positive tube threshold therefore seeds the excess estimates on a
finite dyadic horizon, with the same plane serving at every intermediate scale.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem squaredExcess_le_of_support_tube {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (R η : ℝ) (hR : 0 < R) (hη : 0 ≤ η)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (htube : ∀ x ∈ ball a R, x ∈ μ.support → infDist x (S : Set (Ambient d)) ≤ η) :
    squaredExcess n μ a R ≤ G * (η / R) ^ 2 := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  have : IsFiniteMeasure (μ.restrict (ball a R)) := isFiniteMeasure_restrict.mpr
    (ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a R).measure_lt_top))
  have hi := squared_infDist_integrableOn_ball μ a R S hS.1
  have hb : (∫ x in ball a R, infDist x (S : Set (Ambient d)) ^ 2 ∂μ) ≤
      η ^ 2 * μ.real (ball a R) := by
    calc
      _ ≤ ∫ _x in ball a R, η ^ 2 ∂μ := by
        apply integral_mono_ae hi (integrable_const _)
        filter_upwards [ae_restrict_mem (μ := μ) measurableSet_ball,
          ae_restrict_of_ae μ.support_mem_ae] with x hx hxs
        exact (sq_le_sq₀ infDist_nonneg hη).mpr (htube x hx hxs)
      _ = _ := by
        rw [integral_const]
        simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm]
  have hm : μ.real (ball a R) ≤ G * R ^ n :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (pow_nonneg hR.le n)) (hg.2 a R hR)
  calc
    _ ≤ quadraticPlaneError n μ a R S := squaredExcess_le_planeError n μ a R hR.le S hS
    _ ≤ (R ^ (n + 2))⁻¹ * (η ^ 2 * (G * R ^ n)) := by
      exact mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hm (sq_nonneg η)))
        (by positivity)
    _ = _ := by
      rw [pow_add]
      field_simp

theorem exists_positive_tube_threshold (G δ : ℝ) (hG : 0 ≤ G) (hδ : 0 < δ) :
    ∃ α : ℝ, 0 < α ∧ α ≤ δ ∧ G * α ^ 2 ≤ δ ^ 2 := by
  refine ⟨δ / (G + 1), div_pos hδ (by positivity), ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < G + 1)).mpr
    nlinarith
  · have hGsq : G ≤ (G + 1) ^ 2 := by nlinarith [sq_nonneg G]
    calc
      _ = (δ ^ 2 * G) / (G + 1) ^ 2 := by rw [div_pow]; ring
      _ ≤ δ ^ 2 := (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < G + 1))).mpr
        (mul_le_mul_of_nonneg_left hGsq (sq_nonneg δ))

theorem initial_excess_horizon_of_support_tube {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (r α δ b : ℝ) (hr : 0 < r) (hα : 0 ≤ α) (hδ : 0 ≤ δ) (hb : 1 ≤ b)
    (hsmall : G * α ^ 2 ≤ δ ^ 2) (K : ℕ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (htube : ∀ x ∈ ball a (r * (2 : ℝ) ^ K), x ∈ μ.support →
      infDist x (S : Set (Ambient d)) ≤ α * r) :
    ∀ l ≤ K, squaredExcess n μ a (r * (2 : ℝ) ^ l) ≤ (δ * b ^ l) ^ 2 := by
  intro l hl
  have hsub : ball a (r * (2 : ℝ) ^ l) ⊆ ball a (r * (2 : ℝ) ^ K) :=
    ball_subset_ball (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hl) hr.le)
  have ht := squaredExcess_le_of_support_tube n G μ hg a (r * (2 : ℝ) ^ l) (α * r)
    (by positivity) (mul_nonneg hα hr.le) S hS (fun x hx hxs => htube x (hsub hx) hxs)
  have hratio : α * r / (r * (2 : ℝ) ^ l) ≤ α := by
    apply (div_le_iff₀ (by positivity : 0 < r * (2 : ℝ) ^ l)).mpr
    have hp : 1 ≤ (2 : ℝ) ^ l := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg (mul_nonneg hα hr.le) (sub_nonneg.mpr hp)]
  have hweight : δ ≤ δ * b ^ l := le_mul_of_one_le_right hδ (one_le_pow₀ hb)
  calc
    _ ≤ G * (α * r / (r * (2 : ℝ) ^ l)) ^ 2 := ht
    _ ≤ G * α ^ 2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hratio 2) hg.1
    _ ≤ δ ^ 2 := hsmall
    _ ≤ _ := pow_le_pow_left₀ hδ hweight 2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FlatSeedChainPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Propagation from a flat seed

A thin support tube supplies the initial excess bounds for a dyadic chain.
Uniformly small scalar oscillation propagates those bounds and bilateral
flatness to its descendants. Conversely, a bad descendant scale provides a
mean-zero Lipschitz test with a large scalar Riesz pairing at an earlier scale.
The propagation parameters are chosen before the measure and the seed ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_uniform_flat_seed_chain_propagation {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (hC : 0 < C) (hG : 0 ≤ G) (b : ℝ) (hb1 : 1 < b) (hb2 : b ^ 2 < 2)
    (D : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (J₀ : ℕ) :
    ∃ J : ℕ, J₀ ≤ J ∧ ∃ α : ℝ, 0 < α ∧ α ≤ propagationScale J ∧
      ∀ μ : Measure (Ambient d), GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ s : ℝ, AdmissibleRadius μ s →
        ENNReal.ofReal (s ^ (p + 1) / C) ≤ μ (ball x s)) →
      ∀ a ∈ μ.support, ∀ r : ℝ, 0 < r →
      AdmissibleRadius μ (r * (2 : ℝ) ^ propagationHorizon J) →
      (∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane (p + 1) S ∧
        ∀ x ∈ ball a (r * (2 : ℝ) ^ propagationHorizon J), x ∈ μ.support →
          infDist x (S : Set (Ambient d)) ≤ α * r) →
      (∀ η, 0 < η → ∀ u : Ambient d → ℝ, MemLp u 2 μ →
        MemLp (truncated (p + 1) μ η u) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) →
      ∀ L : ℕ,
      (∀ j < L, ScalarOscillationBound (p + 1) μ a
        (descendantRadius r j * propagationTestRadius J)
        (descendantRadius r j ^ (p + 2) * propagationScale J ^ 3)) →
      ∀ j ≤ L,
        squaredExcess (p + 1) μ a (descendantRadius r j) ≤ propagationScale J ^ 2 ∧
        (0 < j → bilateralBeta (p + 1) μ a (descendantRadius r j) < ε) := by
  obtain ⟨J, hJ₀, hJ⟩ := exists_uniform_dyadic_chain_propagation hnd C G hC b hb1 hb2 D ε hε J₀
  obtain ⟨α, hα, hαδ, hsmall⟩ := exists_positive_tube_threshold G (propagationScale J) hG
    (propagationScale_pos J)
  refine ⟨J, hJ₀, α, hα, hαδ, ?_⟩
  intro μ hg hlower a ha r hr horizon htube hB L hosc
  obtain ⟨S, hS, hs⟩ := htube
  have hinit := initial_excess_horizon_of_support_tube (p + 1) G μ hg a r α (propagationScale J) b
    hr hα.le (propagationScale_pos J).le hb1.le hsmall (propagationHorizon J) S hS hs
  exact hJ μ hg hlower a ha r hr horizon hinit hB L hosc

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellDyadicScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Comparing lattice generations with dyadic descendants

One lattice generation contracts the radius by `64`, hence corresponds to six
dyadic halvings. Dividing a dyadic depth by six separates a whole lattice
generation from a bounded remainder, giving uniform comparisons of the two scales.
-/

namespace RieszRectifiability

noncomputable section

/-- Advancing `t` lattice generations is exactly `6 * t` dyadic halvings. -/
theorem latticeRadius_eq_descendantRadius (R : ℝ) (k t : ℕ) :
    latticeRadius R (k + t) = descendantRadius (latticeRadius R k) (6 * t) := by
  rw [latticeRadius_add]
  change latticeRadius R k * (1 / 64 : ℝ) ^ t = latticeRadius R k / (2 : ℝ) ^ (6 * t)
  norm_num [pow_mul, one_div_pow, div_eq_mul_inv]

/-- The remainder modulo six records the dyadic contraction within a lattice generation. -/
theorem descendantRadius_cell_remainder (R H : ℝ) (k j : ℕ) :
    descendantRadius (H * latticeRadius R k) j =
      H * latticeRadius R (k + j / 6) / (2 : ℝ) ^ (j % 6) := by
  have hj : j = 6 * (j / 6) + j % 6 := by omega
  have hp : (2 : ℝ) ^ j = (2 : ℝ) ^ (6 * (j / 6)) * (2 : ℝ) ^ (j % 6) := by
    rw [← pow_add, ← hj]
  rw [latticeRadius_eq_descendantRadius]
  simp only [descendantRadius, hp]
  field_simp

/-- Positive dyadic descendant radii lie between fixed multiples of the matching lattice scale. -/
theorem descendantRadius_cell_bounds (R H : ℝ) (hR : 0 < R) (hH : 0 < H) (k j : ℕ) :
    (H / 64) * latticeRadius R (k + j / 6) ≤ descendantRadius (H * latticeRadius R k) j ∧
      descendantRadius (H * latticeRadius R k) j ≤ H * latticeRadius R (k + j / 6) := by
  rw [descendantRadius_cell_remainder]
  have hr := latticeRadius_pos R hR (k + j / 6)
  have hp : 0 < (2 : ℝ) ^ (j % 6) := by positivity
  have hlo : 1 ≤ (2 : ℝ) ^ (j % 6) := one_le_pow₀ (by norm_num)
  have hhi : (2 : ℝ) ^ (j % 6) ≤ 64 := by
    have ht := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show j % 6 ≤ 6 by omega)
    norm_num at ht
    exact ht
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhi (mul_pos hH hr).le]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlo (mul_pos hH hr).le]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellOscillationTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transferring cell oscillation bounds

Localization independence transfers scalar Riesz oscillation bounds to a contained
ball. Comparing the centers and scales then turns a cell-centered bound into the
corresponding normalized bound on a nearby ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem ScalarOscillationBound.of_ball_subset {p d : ℕ}
    (μ : Measure (Ambient d)) (G : ℝ) (hg : GlobalUpperGrowth (p + 1) G μ)
    (a b : Ambient d) (r R v w : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hsub : ball a r ⊆ ball b R) (hvw : v ≤ w)
    (hosc : ScalarOscillationBound (p + 1) μ b R v) :
    ScalarOscillationBound (p + 1) μ a r w := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  intro e he φ hφ hs hzero
  have hsA : ∀ x, φ x ≠ 0 → dist x a ≤ r := fun x hx =>
    (hs (subset_tsupport _ hx)).le
  have hsB : ∀ x, φ x ≠ 0 → dist x b ≤ R := fun x hx =>
    (hsub (hs (subset_tsupport _ hx))).le
  have heq := rieszScalarPairing_localization_independent p G μ hg e φ 1 hφ
    a b r R (2 * r) (2 * R) hr.le hR.le (by positivity) (by positivity)
    le_rfl le_rfl hsA hsB hzero
  rw [heq]
  exact (hosc e he φ hφ (hs.trans hsub) hzero).trans hvw

theorem cell_oscillation_controls_nearby_ball {p d : ℕ}
    (μ : Measure (Ambient d)) (G : ℝ) (hg : GlobalUpperGrowth (p + 1) G μ)
    (a z : Ambient d) (s r H T δ : ℝ) (hs : 0 < s) (hr : 0 < r)
    (hH : 0 < H) (hT : 0 < T) (hδ : 0 ≤ δ)
    (hnear : dist a z ≤ 2 * r) (hupper : s ≤ H * r) (hlower : (H / 64) * r ≤ s)
    (hosc : ScalarOscillationBound (p + 1) μ z ((H * T + 2) * r)
      (((H / 64) ^ (p + 2) * δ ^ 3) * r ^ (p + 2))) :
    ScalarOscillationBound (p + 1) μ a (s * T) (s ^ (p + 2) * δ ^ 3) := by
  apply ScalarOscillationBound.of_ball_subset μ G hg a z (s * T) ((H * T + 2) * r)
    _ _ (mul_pos hs hT) (by positivity) _ _ hosc
  · apply ball_subset_outer_of_radius_dist
    nlinarith [mul_le_mul_of_nonneg_right hupper hT.le]
  · have hp := pow_le_pow_left₀ (show 0 ≤ (H / 64) * r by positivity) hlower (p + 2)
    have hm := mul_le_mul_of_nonneg_right hp (pow_nonneg hδ 3)
    simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using! hm

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FlatCellChainPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Flatness propagation along cell chains

A flat initial cell and oscillation bounds on its ancestors control bilateral beta at every
descendant center. Six binary steps correspond to one lattice depth; nearby-ball transfer
provides the intervening dyadic bounds required by flat-seed propagation.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_uniform_flat_cell_chain_propagation {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G H ε : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 ≤ G) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ α : ℝ, 0 < α ∧ 2 * α < ε * H ∧
      ∀ μ : Measure (Ambient d), GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r)) →
      (∀ η : ℝ, 0 < η → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated (p + 1) μ η f) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ ((H * latticeRadius R k) * (2 : ℝ) ^ propagationHorizon J) →
      HasFlatCell (p + 1) μ R hR k z (H * (2 : ℝ) ^ propagationHorizon J + 2) α →
      bilateralBeta (p + 1) μ z (H * latticeRadius R k) < ε ∧
      ∀ i : SupportCellDescendant μ R hR k z, 0 < i.depth →
      (∀ q : SupportCellDescendant μ R hR k z, q.depth < i.depth → i.center ∈ q.cell →
        ScalarOscillationBound (p + 1) μ q.center ((H * propagationTestRadius J + 2) * q.radius)
          (((H / 64) ^ (p + 2) * propagationScale J ^ 3) * q.radius ^ (p + 2))) →
      bilateralBeta (p + 1) μ i.center (H * i.radius) < ε := by
  obtain ⟨J, _, α₀, hα₀, _, hchain⟩ := exists_uniform_flat_seed_chain_propagation hnd C G hC hG
    (5 / 4) (by norm_num) (by norm_num) D ε hε 0
  have hHp : 0 < H := by linarith
  let α := min α₀ (ε * H / 4)
  have hα : 0 < α := lt_min hα₀ (by positivity)
  have hα₀le : α ≤ α₀ := min_le_left _ _
  have hsmall : 2 * α < ε * H := by
    have hh : α ≤ ε * H / 4 := min_le_right _ _
    nlinarith [mul_pos hε hHp]
  refine ⟨J, α, hα, hsmall, ?_⟩
  intro μ hg hlower hRiesz R hR k z horizon hflat
  have hpow : 1 ≤ (2 : ℝ) ^ propagationHorizon J := one_le_pow₀ (by norm_num)
  constructor
  · exact HasFlatCell.beta_lt μ R hR k z _ H α ε hHp (by nlinarith) hα.le hsmall hflat
  · intro i hi hosc
    have htube := HasFlatCell.tube_at_descendant_center μ R hR k z H α₀
      (propagationHorizon J) hH hα₀.le
      (HasFlatCell.mono μ R hR k z _ _ α α₀ le_rfl hα₀le hflat) i
    have hbinary (j : ℕ) (hj : j < 6 * i.depth) :
        ScalarOscillationBound (p + 1) μ i.center
          (descendantRadius (H * latticeRadius R k) j * propagationTestRadius J)
          (descendantRadius (H * latticeRadius R k) j ^ (p + 2) * propagationScale J ^ 3) := by
      obtain ⟨q, hq, _, hicell⟩ := i.exists_ancestor_at_depth (j / 6) (by omega)
      have hqbefore : q.depth < i.depth := by omega
      have hqr : q.radius = latticeRadius R (k + j / 6) := by
        simp only [SupportCellDescendant.radius, hq]
      have hbounds := descendantRadius_cell_bounds R H hR hHp k j
      rw [← hqr] at hbounds
      apply cell_oscillation_controls_nearby_ball μ G hg i.center q.center
        (descendantRadius (H * latticeRadius R k) j) q.radius H (propagationTestRadius J)
        (propagationScale J) (descendantRadius_pos _ (mul_pos hHp (latticeRadius_pos R hR k)) j)
        q.radius_pos hHp (by unfold propagationTestRadius; positivity)
        (propagationScale_pos J).le (q.dist_center_of_mem i.center hicell)
        hbounds.2 hbounds.1 (hosc q hqbefore hicell)
    have hgood := hchain μ hg hlower i.center i.center_mem_support (H * latticeRadius R k)
      (mul_pos hHp (latticeRadius_pos R hR k)) horizon htube hRiesz (6 * i.depth)
      hbinary (6 * i.depth) le_rfl
    have heq : descendantRadius (H * latticeRadius R k) (6 * i.depth) = H * i.radius := by
      change _ = H * latticeRadius R (k + i.depth)
      rw [latticeRadius_eq_descendantRadius]
      simp only [descendantRadius]
      ring
    rw [heq] at hgood
    exact hgood.2 (by omega)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FlatCellBadDescendantWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An oscillation witness above a nonflat descendant

Uniform flat-cell chain propagation forces a nonflat positive-depth descendant to have an
earlier ancestor where the scalar oscillation bound fails. The resulting bad descendant contains
the entire offending cell; its depth, testing radius, and oscillation threshold retain the
uniform propagation parameters chosen before the measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_uniform_flat_seed_bad_cell_witness {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G H ε : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 ≤ G) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ α : ℝ, 0 < α ∧ 2 * α < ε * H ∧
      ∀ μ : Measure (Ambient d), GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r)) →
      (∀ η : ℝ, 0 < η → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated (p + 1) μ η f) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ ((H * latticeRadius R k) * (2 : ℝ) ^ propagationHorizon J) →
      HasFlatCell (p + 1) μ R hR k z (H * (2 : ℝ) ^ propagationHorizon J + 2) α →
      ∀ i : SupportCellDescendant μ R hR k z, 0 < i.depth →
      ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius) →
      ∃ q : BadSupportDescendant (p + 1) μ R hR k z
        (H * propagationTestRadius J + 2) ((H / 64) ^ (p + 2) * propagationScale J ^ 3),
        q.val.depth < i.depth ∧ i.cell ⊆ q.val.cell := by
  classical
  obtain ⟨J, α, hα, hsmall, hprop⟩ := exists_uniform_flat_cell_chain_propagation hnd C G H ε D
    hC hG hH hε
  refine ⟨J, α, hα, hsmall, ?_⟩
  intro μ hg hlower hRiesz R hR k z horizon hflat i hi hbad
  have hnot : ¬ ∀ q : SupportCellDescendant μ R hR k z,
      q.depth < i.depth → i.center ∈ q.cell →
      ScalarOscillationBound (p + 1) μ q.center ((H * propagationTestRadius J + 2) * q.radius)
        (((H / 64) ^ (p + 2) * propagationScale J ^ 3) * q.radius ^ (p + 2)) := by
    intro hall
    exact (not_lt_of_ge hbad) ((hprop μ hg hlower hRiesz R hR k z horizon hflat).2 i hi hall)
  push Not at hnot
  obtain ⟨q, hqi, hc, hfail⟩ := hnot
  exact ⟨⟨q, hfail⟩, hqi, i.cell_subset_of_center_mem q hqi.le hc⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellChainComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem SupportCellDescendant.cell_nested_of_common_point {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i q : SupportCellDescendant μ R hR k z) (hq : q.depth ≤ i.depth)
    (x : Ambient d) (hi : x ∈ i.cell) (hqx : x ∈ q.cell) : i.cell ⊆ q.cell := by
  obtain ⟨j, hj, hsub, _⟩ := i.exists_ancestor_at_depth q.depth hq
  have heq := j.eq_of_common_point_same_depth q hj x (hsub hi) hqx
  simpa only [heq] using! hsub

theorem SupportCellDescendant.compose_radius {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z)
    (j : SupportCellDescendant μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩) :
    (i.compose j).radius = j.radius := by
  simp only [SupportCellDescendant.radius, SupportCellDescendant.compose, Nat.add_assoc]

theorem SupportCellDescendant.exists_relative_descendant {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i q : SupportCellDescendant μ R hR k z) (hi : i.depth ≤ q.depth)
    (hsub : q.cell ⊆ i.cell) :
    ∃ j : SupportCellDescendant μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩,
      j.depth = q.depth - i.depth ∧ j.center = q.center ∧ j.cell = q.cell ∧ j.radius = q.radius := by
  have hlevel : k + i.depth + (q.depth - i.depth) = k + q.depth := by omega
  let w : (supportLatticeNets μ R hR (k + i.depth + (q.depth - i.depth))).points :=
    ⟨q.center, by rw [hlevel]; exact q.mem_net⟩
  have hw : supportLatticeAncestor μ R hR (k + i.depth) (q.depth - i.depth) w =
      ⟨i.center, i.mem_net⟩ :=
    supportLatticeAncestor_eq_of_center_mem μ R hR (k + i.depth) (q.depth - i.depth)
      ⟨i.center, i.mem_net⟩ w (hsub q.center_mem_cell)
  let j : SupportCellDescendant μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ :=
    { depth := q.depth - i.depth, center := q.center, mem_net := w.property, ancestor := hw }
  refine ⟨j, rfl, rfl, ?_, ?_⟩
  · simp only [SupportCellDescendant.cell, j, cleanSupportCell, supportLatticeCell,
      supportLatticeCenter, hlevel]
  · simp only [SupportCellDescendant.radius, j, hlevel]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FlatSeedGlobalCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Charging nonflat descendants below a flat seed

The propagation horizon and positive flatness threshold are chosen uniformly before
the measure. A descendant with large bilateral beta below a flat seed then yields a
bad oscillation cell at an intermediate depth. Composition of relative descendants
places this witness in the original cell tree, preserving containment between the
nonflat descendant, its charged bad cell, and the flat seed.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_uniform_flat_seed_global_charge {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G H ε : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 ≤ G) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ α : ℝ, 0 < α ∧ 2 * α < ε * H ∧
      ∀ μ : Measure (Ambient d), GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r)) →
      (∀ η : ℝ, 0 < η → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated (p + 1) μ η f) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      ∀ S : SupportCellDescendant μ R hR k z,
      AdmissibleRadius μ ((H * S.radius) * (2 : ℝ) ^ propagationHorizon J) →
      HasFlatCell (p + 1) μ R hR (k + S.depth) ⟨S.center, S.mem_net⟩
        (H * (2 : ℝ) ^ propagationHorizon J + 2) α →
      ∀ Q : SupportCellDescendant μ R hR k z, S.depth < Q.depth → Q.cell ⊆ S.cell →
      ε ≤ bilateralBeta (p + 1) μ Q.center (H * Q.radius) →
      ∃ t : BadSupportDescendant (p + 1) μ R hR k z
        (H * propagationTestRadius J + 2) ((H / 64) ^ (p + 2) * propagationScale J ^ 3),
        S.depth ≤ t.val.depth ∧ t.val.depth < Q.depth ∧ Q.cell ⊆ t.val.cell ∧ t.val.cell ⊆ S.cell := by
  obtain ⟨J, α, hα, hsmall, hcharge⟩ := exists_uniform_flat_seed_bad_cell_witness hnd C G H ε D
    hC hG hH hε
  refine ⟨J, α, hα, hsmall, ?_⟩
  intro μ hg hlower hRiesz R hR k z S horizon hflat Q hSQ hQsub hbad
  obtain ⟨q, hqdepth, hqcenter, hqcell, hqradius⟩ := S.exists_relative_descendant Q hSQ.le hQsub
  have hqpos : 0 < q.depth := by omega
  have hqbad : ε ≤ bilateralBeta (p + 1) μ q.center (H * q.radius) := by
    rw [hqcenter, hqradius]
    exact hbad
  obtain ⟨t, htdepth, hsub⟩ := hcharge μ hg hlower hRiesz R hR (k + S.depth)
    ⟨S.center, S.mem_net⟩ horizon hflat q hqpos hqbad
  have hfail : ¬ ScalarOscillationBound (p + 1) μ (S.compose t.val).center
      ((H * propagationTestRadius J + 2) * (S.compose t.val).radius)
      (((H / 64) ^ (p + 2) * propagationScale J ^ 3) * (S.compose t.val).radius ^ (p + 2)) := by
    rw [S.compose_radius]
    exact t.property
  refine ⟨⟨S.compose t.val, hfail⟩, ?_, ?_, ?_, ?_⟩
  · simp only [SupportCellDescendant.compose_depth, Nat.le_add_right]
  · simp only [SupportCellDescendant.compose_depth]
    omega
  · rw [S.compose_cell, ← hqcell]
    exact hsub
  · rw [S.compose_cell]
    exact t.val.cell_subset_top

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_GlobalFlatSeedSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_global_flat_seed {n d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (i : SupportCellDescendant μ R hR k z) (I : ℕ) (A α : ℝ)
    (hflat : HasFlatDescendant n μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I A α) :
    ∃ S : SupportCellDescendant μ R hR k z,
      i.depth < S.depth ∧ S.depth ≤ i.depth + I ∧ S.cell ⊆ i.cell ∧
        A * S.radius ≤ i.radius / 8 ∧
        HasFlatCell n μ R hR (k + S.depth) ⟨S.center, S.mem_net⟩ A α := by
  obtain ⟨j, hjpos, hjI, hsize, hfit⟩ := hflat
  refine ⟨i.compose j, ?_, ?_, ?_, ?_, ?_⟩
  · rw [i.compose_depth]
    omega
  · rw [i.compose_depth]
    omega
  · rw [i.compose_cell]
    exact j.cell_subset_top
  · rw [i.compose_radius]
    exact hsize
  · simpa only [HasFlatCell, SupportCellDescendant.compose, Nat.add_assoc] using! hfit

theorem flat_seed_enlargement_admissible {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (i S : SupportCellDescendant μ R hR k z) (A H : ℝ) (hH : 0 < H) (hHA : H ≤ A)
    (hsize : A * S.radius ≤ i.radius / 8) : AdmissibleRadius μ (H * S.radius) := by
  have hi : AdmissibleRadius μ (i.radius / 8) := by
    simpa only [one_div_mul_eq_div] using! i.core_admissible hcore
  have hle := (mul_le_mul_of_nonneg_right hHA S.radius_pos.le).trans hsize
  exact ⟨mul_pos hH S.radius_pos, (ENNReal.ofReal_le_ofReal hle).trans hi.2⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FlatDescendantMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem SupportCellDescendant.top_radius_eq {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) :
    latticeRadius R k = (64 : ℝ) ^ i.depth * i.radius := by
  change _ = (64 : ℝ) ^ i.depth * latticeRadius R (k + i.depth)
  rw [latticeRadius_add]
  have hp : (64 : ℝ) ^ i.depth * (1 / 64 : ℝ) ^ i.depth = 1 := by
    rw [← mul_pow]
    norm_num
  change _ = (64 : ℝ) ^ i.depth * (latticeRadius R k * (1 / 64 : ℝ) ^ i.depth)
  rw [mul_left_comm, hp, mul_one]

theorem SupportCellDescendant.radius_lower_of_depth_le {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (I : ℕ) (hi : i.depth ≤ I) :
    latticeRadius R k ≤ (64 : ℝ) ^ I * i.radius := by
  rw [i.top_radius_eq]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) i.radius_pos.le

theorem flatDescendantMassConstant_pos (n : ℕ) (C G : ℝ) (I : ℕ) (hC : 0 < C) (hG : 0 < G) :
    0 < flatDescendantMassConstant n C G I := by
  unfold flatDescendantMassConstant
  positivity

theorem SupportCellDescendant.parent_mass_bound {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (i : SupportCellDescendant μ R hR k z) (I : ℕ) (hi : i.depth ≤ I) :
    μ.real (cleanSupportCell μ R hR k z) ≤ flatDescendantMassConstant n C G I * μ.real i.cell := by
  have hicore : AdmissibleRadius μ (latticeRadius R (k + i.depth) / 8) := by
    simpa only [one_div_mul_eq_div, SupportCellDescendant.radius] using! i.core_admissible hcore
  have hlow := (cleanSupportCell_real_measure_bounds μ C G hC hG hg hlower R hR
    (k + i.depth) hicore ⟨i.center, i.mem_net⟩).1
  have htop := (cleanSupportCell_real_measure_bounds μ C G hC hG hg hlower R hR k hcore z).2
  have hscale := i.radius_lower_of_depth_le I hi
  have hK := flatDescendantMassConstant_pos n C G I hC hG
  have hparent := latticeRadius_pos R hR k
  calc
    _ ≤ G * (3 * latticeRadius R k) ^ n := by simpa only [mul_pow, mul_assoc] using! htop
    _ ≤ G * (3 * ((64 : ℝ) ^ I * i.radius)) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) n) hG.le
    _ = flatDescendantMassConstant n C G I * ((i.radius / 8) ^ n / C) := by
      have heq : 3 * ((64 : ℝ) ^ I * i.radius) =
          (24 * (64 : ℝ) ^ I) * (i.radius / 8) := by ring
      rw [heq, mul_pow]
      unfold flatDescendantMassConstant
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow hK.le

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_RelativeCellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem SupportCellDescendant.relative_real_mass_bound {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (i S : SupportCellDescendant μ R hR k z) (I : ℕ)
    (hlo : i.depth ≤ S.depth) (hhi : S.depth ≤ i.depth + I) (hsub : S.cell ⊆ i.cell) :
    μ.real i.cell ≤ flatDescendantMassConstant n C G I * μ.real S.cell := by
  obtain ⟨j, hj, _, hcell, _⟩ := i.exists_relative_descendant S hlo hsub
  have hicore : AdmissibleRadius μ (latticeRadius R (k + i.depth) / 8) := by
    simpa only [one_div_mul_eq_div, SupportCellDescendant.radius] using! i.core_admissible hcore
  have hb := SupportCellDescendant.parent_mass_bound μ C G hC hG hg hlower R hR
    (k + i.depth) ⟨i.center, i.mem_net⟩ hicore j I (by omega)
  change μ.real i.cell ≤ flatDescendantMassConstant n C G I * μ.real j.cell at hb
  rwa [hcell] at hb

theorem SupportCellDescendant.relative_mass_bound {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (i S : SupportCellDescendant μ R hR k z) (I : ℕ)
    (hlo : i.depth ≤ S.depth) (hhi : S.depth ≤ i.depth + I) (hsub : S.cell ⊆ i.cell) :
    μ i.cell ≤ ENNReal.ofReal (flatDescendantMassConstant n C G I) * μ S.cell := by
  have hb := SupportCellDescendant.relative_real_mass_bound μ C G hC hG hg hlower
    R hR k z hcore i S I hlo hhi hsub
  have hi : μ i.cell ≠ ∞ := ((i.measure_upper G hg).trans_lt ENNReal.ofReal_lt_top).ne
  have hS : μ S.cell ≠ ∞ := ((S.measure_upper G hg).trans_lt ENNReal.ofReal_lt_top).ne
  have hM := flatDescendantMassConstant_pos n C G I hC hG
  have he := ENNReal.ofReal_le_ofReal hb
  change ENNReal.ofReal ((μ i.cell).toReal) ≤
    ENNReal.ofReal (flatDescendantMassConstant n C G I * (μ S.cell).toReal) at he
  rwa [ENNReal.ofReal_mul hM.le, ENNReal.ofReal_toReal hi, ENNReal.ofReal_toReal hS] at he

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_FiniteChargeSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

open scoped ENNReal

theorem exists_finite_pair_witnesses {ι τ : Type*} (F : Finset ι)
    (Rel : ι → ι → Prop) (Q : ι → ι → τ → Prop)
    (hex : ∀ i ∈ F, ∀ j ∈ F, Rel i j → ∃ t, Q i j t) :
    ∃ O : Finset τ, ∀ i ∈ F, ∀ j ∈ F, Rel i j → ∃ t ∈ O, Q i j t := by
  classical
  let P := (F.product F).filter (fun ij => Rel ij.1 ij.2)
  have hchoose (p : {ij // ij ∈ P}) : ∃ t, Q p.val.1 p.val.2 t := by
    have hm := Finset.mem_filter.mp p.property
    have hp := Finset.mem_product.mp hm.1
    exact hex p.val.1 hp.1 p.val.2 hp.2 hm.2
  let O := P.attach.image (fun p => (hchoose p).choose)
  refine ⟨O, ?_⟩
  intro i hi j hj hRel
  have hp : (i, j) ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hRel⟩
  let p : {ij // ij ∈ P} := ⟨(i, j), hp⟩
  exact ⟨(hchoose p).choose, Finset.mem_image.mpr ⟨p, Finset.mem_attach _ _, rfl⟩,
    (hchoose p).choose_spec⟩

theorem finite_subtype_sum_le_tsum {ι : Type*} (P : ι → Prop) (f : ι → ℝ≥0∞)
    (s : Finset ι) (hs : ∀ i ∈ s, P i) :
    ∑ i ∈ s, f i ≤ ∑' i : {i // P i}, f i.val := by
  classical
  let emb : {i // i ∈ s} ↪ {i // P i} :=
    ⟨fun i => ⟨i.val, hs i.val i.property⟩,
      fun i j hij => Subtype.ext (congrArg (fun t : {i // P i} => t.val) hij)⟩
  let t := s.attach.map emb
  have heq : ∑ i ∈ t, f i.val = ∑ i ∈ s, f i := by
    rw [Finset.sum_map]
    change (∑ i ∈ s.attach, f i.val) = ∑ i ∈ s, f i
    exact Finset.sum_attach s f
  exact heq.symm.le.trans (ENNReal.sum_le_tsum t)

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SeedChainCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

theorem nat_finset_card_le_of_bounded_interval (P : Finset ℕ) (p I : ℕ)
    (hP : ∀ r ∈ P, p ≤ r ∧ r ≤ p + I) : P.card ≤ I + 1 := by
  have hsub : P ⊆ Finset.Icc p (p + I) := fun r hr => Finset.mem_Icc.mpr (hP r hr)
  have hb := Finset.card_le_card hsub
  simpa only [Nat.card_Icc, Nat.add_assoc, Nat.add_sub_cancel_left] using! hb

theorem captured_seed_chain_count (P O : Finset ℕ) (seed : ℕ → ℕ) (I : ℕ)
    (hseed : ∀ p ∈ P, p ≤ seed p ∧ seed p ≤ p + I)
    (hgap : ∀ p ∈ P, ∀ q ∈ P, seed p < q →
      ∃ t ∈ O, seed p ≤ t ∧ t < q) :
    P.card ≤ (I + 1) * (1 + O.card) := by
  classical
  induction O using Finset.strongInductionOn generalizing P with | _ O ih
  by_cases hP : P.Nonempty
  · let p := P.min' hP
    have hp : p ∈ P := P.min'_mem hP
    have hpmin : ∀ r ∈ P, p ≤ r := fun r hr => P.min'_le r hr
    let Tail := P.filter (fun r => seed p < r)
    by_cases hTail : Tail.Nonempty
    · let q := Tail.min' hTail
      have hqmem : q ∈ Tail := Tail.min'_mem hTail
      have hqP : q ∈ P := (Finset.mem_filter.mp hqmem).1
      have hsq : seed p < q := (Finset.mem_filter.mp hqmem).2
      obtain ⟨t, htO, hst, htq⟩ := hgap p hp q hqP hsq
      let O' := O.filter (fun t => q ≤ t)
      have hstrict : O' ⊂ O := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.filter_subset _ _, ?_⟩
        intro heq
        have ht : t ∈ O' := heq.symm ▸ htO
        have hqt := (Finset.mem_filter.mp ht).2
        omega
      let P' := P.filter (fun r => q ≤ r)
      have hbound : (P.filter (fun r => r < q)).card ≤ I + 1 := by
        apply nat_finset_card_le_of_bounded_interval _ p I
        intro r hr
        obtain ⟨hrP, hrq⟩ := Finset.mem_filter.mp hr
        have hrs : r ≤ seed p := by
          by_contra hbad
          have hrTail : r ∈ Tail := Finset.mem_filter.mpr ⟨hrP, by omega⟩
          have hqr : q ≤ r := Tail.min'_le r hrTail
          omega
        exact ⟨hpmin r hrP, hrs.trans (hseed p hp).2⟩
      have hrec : P'.card ≤ (I + 1) * (1 + O'.card) := by
        apply ih O' hstrict P'
        · intro r hr
          exact hseed r (Finset.mem_filter.mp hr).1
        · intro r hr s hs hrs
          obtain ⟨u, huO, hru, hus⟩ := hgap r (Finset.mem_filter.mp hr).1
            s (Finset.mem_filter.mp hs).1 hrs
          refine ⟨u, Finset.mem_filter.mpr ⟨huO, ?_⟩, hru, hus⟩
          exact (Finset.mem_filter.mp hr).2.trans ((hseed r (Finset.mem_filter.mp hr).1).1.trans hru)
      have hsplit : (P.filter (fun r => r < q)).card + P'.card = P.card := by
        simpa only [Nat.not_lt] using!
          Finset.card_filter_add_card_filter_not (s := P) (fun r => r < q)
      have hOcard : O'.card + 1 ≤ O.card := Finset.card_lt_card hstrict
      calc
        P.card = (P.filter (fun r => r < q)).card + P'.card := hsplit.symm
        _ ≤ (I + 1) + (I + 1) * (1 + O'.card) := Nat.add_le_add hbound hrec
        _ = (I + 1) * (1 + (O'.card + 1)) := by ring
        _ ≤ (I + 1) * (1 + O.card) := Nat.mul_le_mul_left _ (Nat.add_le_add_left hOcard 1)
    · have hbound : P.card ≤ I + 1 := by
        apply nat_finset_card_le_of_bounded_interval P p I
        intro r hr
        have hrs : r ≤ seed p := by
          by_contra hbad
          exact hTail ⟨r, Finset.mem_filter.mpr ⟨hr, by omega⟩⟩
        exact ⟨hpmin r hr, hrs.trans (hseed p hp).2⟩
      calc
        P.card ≤ I + 1 := hbound
        _ ≤ (I + 1) * (1 + O.card) := by nlinarith
  · have heq : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    simp only [heq, Finset.card_empty, Nat.zero_le]

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_IndexedSeedChainCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Counting indexed captured seed chains

Injective levels reduce a finite indexed family to a chain of natural-number levels.
Bounded seed offsets and the marked gaps then control the size of the original family.
-/

namespace RieszRectifiability

theorem indexed_captured_seed_chain_count {ι : Type*} (s : Finset ι) (O : Finset ℕ)
    (level seed : ι → ℕ) (I : ℕ) (hinj : Set.InjOn level s)
    (hseed : ∀ i ∈ s, level i ≤ seed i ∧ seed i ≤ level i + I)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, seed i < level j →
      ∃ t ∈ O, seed i ≤ t ∧ t < level j) :
    s.card ≤ (I + 1) * (1 + O.card) := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hs
    let : Nonempty {i // i ∈ s} := ⟨⟨i₀, hi₀⟩⟩
    let f : {i // i ∈ s} → ℕ := fun i => level i.val
    have hf : Function.Injective f := by
      intro i j hij
      exact Subtype.ext (hinj i.property j.property hij)
    let g : ℕ → {i // i ∈ s} := Function.invFun f
    have hleft (i : ι) (hi : i ∈ s) : g (level i) = ⟨i, hi⟩ :=
      Function.leftInverse_invFun hf ⟨i, hi⟩
    have hb := captured_seed_chain_count (s.image level) O (fun l => seed (g l).val) I
      (by
        intro l hl
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
        simpa only [hleft i hi] using! hseed i hi)
      (by
        intro l hl m hm hlt
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
        simp only [hleft i hi] at hlt ⊢
        exact hgap i hi j hj hlt)
    rw [Finset.card_image_iff.mpr hinj] at hb
    exact hb
  · have heq : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [heq, Finset.card_empty, Nat.zero_le]

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SeedMultiplicityIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrating finite multiplicity bounds

Finite sums of indicator functions count the sets containing a point. Integrating
these identities converts pointwise multiplicity bounds into estimates for sums
of measures, including bounds expressed directly using finite cardinalities.
-/

namespace RieszRectifiability

open MeasureTheory Set
open scoped ENNReal

theorem finite_indicator_one_sum_eq_card {ι X : Type*} (s : Finset ι) (A : ι → Set X) (x : X)
    [∀ i, Decidable (x ∈ A i)] :
    ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x =
      ((s.filter (fun i => x ∈ A i)).card : ℝ≥0∞) := by
  classical
  calc
    _ = ∑ _i ∈ s.filter (fun i => x ∈ A i), (1 : ℝ≥0∞) := by
      rw [Finset.sum_filter]
      simp only [Set.indicator_apply]
    _ = _ := by simp

theorem lintegral_finite_indicator_multiplicity {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (A : ι → Set X) (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    (∫⁻ x, ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) =
      ∑ i ∈ s, μ (A i) := by
  rw [lintegral_finsetSum s (fun i hi => measurable_const.indicator (hA i hi))]
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_indicator_one (hA i hi)

theorem measure_sum_le_of_indicator_multiplicity {ι κ X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (t : Finset κ) (A : ι → Set X) (B : κ → Set X)
    (T : Set X) (N : ℕ) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hB : ∀ j ∈ t, MeasurableSet (B j)) (hT : MeasurableSet T)
    (hpoint : ∀ x, (∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤
      (N : ℝ≥0∞) * (T.indicator (fun _ => 1) x +
        ∑ j ∈ t, (B j).indicator (fun _ => 1) x)) :
    ∑ i ∈ s, μ (A i) ≤ (N : ℝ≥0∞) * (μ T + ∑ j ∈ t, μ (B j)) := by
  rw [← lintegral_finite_indicator_multiplicity μ s A hA]
  calc
    _ ≤ ∫⁻ x, (N : ℝ≥0∞) * (T.indicator (fun _ => 1) x +
        ∑ j ∈ t, (B j).indicator (fun _ => 1) x) ∂μ := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left (measurable_const.indicator hT)]
      have hTone : (∫⁻ x, T.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) = μ T :=
        lintegral_indicator_one hT
      rw [hTone, lintegral_finite_indicator_multiplicity μ t B hB]

theorem measure_sum_le_of_count_multiplicity {ι κ X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (t : Finset κ) (A : ι → Set X) (B : κ → Set X)
    (T : Set X) (N : ℕ) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hB : ∀ j ∈ t, MeasurableSet (B j)) (hT : MeasurableSet T)
    [∀ x : X, Decidable (x ∈ T)] [∀ i x, Decidable (x ∈ A i)] [∀ j x, Decidable (x ∈ B j)]
    (hpoint : ∀ x, (s.filter (fun i => x ∈ A i)).card ≤
      N * ((if x ∈ T then 1 else 0) + (t.filter (fun j => x ∈ B j)).card)) :
    ∑ i ∈ s, μ (A i) ≤ (N : ℝ≥0∞) * (μ T + ∑ j ∈ t, μ (B j)) := by
  apply measure_sum_le_of_indicator_multiplicity μ s t A B T N hA hB hT
  intro x
  rw [finite_indicator_one_sum_eq_card, finite_indicator_one_sum_eq_card]
  have hb := hpoint x
  by_cases hx : x ∈ T
  · simp only [ite_eq_left hx] at hb
    simp only [Set.indicator_of_mem hx]
    exact_mod_cast hb
  · simp only [ite_eq_right hx] at hb
    simp only [Set.indicator_of_notMem hx]
    exact_mod_cast hb

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CapturedCellSeedMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Depth gaps between captured cells are charged to intervening cells. The resulting pointwise
seed-multiplicity bound integrates to a mass estimate for the finite captured family.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem captured_cell_seed_mass_bound {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (F O : Finset (SupportCellDescendant μ R hR k z))
    (seed : SupportCellDescendant μ R hR k z → SupportCellDescendant μ R hR k z) (I : ℕ)
    (hseed : ∀ i ∈ F, i.depth ≤ (seed i).depth ∧ (seed i).depth ≤ i.depth + I ∧
      (seed i).cell ⊆ i.cell)
    (hgap : ∀ i ∈ F, ∀ j ∈ F, (seed i).depth < j.depth → j.cell ⊆ (seed i).cell →
      ∃ t ∈ O, (seed i).depth ≤ t.depth ∧ t.depth < j.depth ∧ j.cell ⊆ t.cell) :
    ∑ i ∈ F, μ (seed i).cell ≤ ((I + 1 : ℕ) : ℝ≥0∞) *
      (μ (cleanSupportCell μ R hR k z) + ∑ t ∈ O, μ t.cell) := by
  classical
  apply measure_sum_le_of_count_multiplicity μ F O (fun i => (seed i).cell) (fun t => t.cell)
    (cleanSupportCell μ R hR k z) (I + 1)
    (fun i _ => cleanSupportCell_measurable μ R hR (k + (seed i).depth)
      ⟨(seed i).center, (seed i).mem_net⟩)
    (fun t _ => cleanSupportCell_measurable μ R hR (k + t.depth) ⟨t.center, t.mem_net⟩)
    (cleanSupportCell_measurable μ R hR k z)
  intro x
  by_cases hx : x ∈ cleanSupportCell μ R hR k z
  · let Pcap := F.filter (fun i => x ∈ (seed i).cell)
    let Ocap := O.filter (fun t => x ∈ t.cell)
    have hmem (i : SupportCellDescendant μ R hR k z) (hi : i ∈ Pcap) :
        i ∈ F ∧ x ∈ (seed i).cell := Finset.mem_filter.mp hi
    have hiparent (i : SupportCellDescendant μ R hR k z) (hi : i ∈ Pcap) : x ∈ i.cell :=
      (hseed i (hmem i hi).1).2.2 (hmem i hi).2
    have hinj : Set.InjOn (fun i : SupportCellDescendant μ R hR k z => i.depth) Pcap := by
      intro i hi j hj hij
      exact i.eq_of_common_point_same_depth j hij x (hiparent i hi) (hiparent j hj)
    have hb := indexed_captured_seed_chain_count Pcap (Ocap.image (fun t => t.depth))
      (fun i => i.depth) (fun i => (seed i).depth) I hinj
      (fun i hi => ⟨(hseed i (hmem i hi).1).1, (hseed i (hmem i hi).1).2.1⟩)
      (by
        intro i hi j hj hdepth
        have hsub := j.cell_nested_of_common_point (seed i) hdepth.le x
          (hiparent j hj) (hmem i hi).2
        obtain ⟨t, ht, hlow, hhigh, hcontain⟩ := hgap i (hmem i hi).1 j (hmem j hj).1 hdepth hsub
        refine ⟨t.depth, Finset.mem_image.mpr ⟨t, ?_, rfl⟩, hlow, hhigh⟩
        exact Finset.mem_filter.mpr ⟨ht, hcontain (hiparent j hj)⟩)
    have hcard : (Ocap.image (fun t => t.depth)).card ≤ Ocap.card := Finset.card_image_le
    have hbound := hb.trans (Nat.mul_le_mul_left (I + 1) (Nat.add_le_add_left hcard 1))
    simpa only [ite_eq_left hx] using! hbound
  · have heq : F.filter (fun i => x ∈ (seed i).cell) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hm := Finset.mem_filter.mp hi
      exact hx (i.cell_subset_top ((hseed i hm.1).2.2 hm.2))
    simp only [heq, Finset.card_empty, Nat.zero_le]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_FiniteSeedPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem finite_parent_mass_of_seed_charges {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (F : Finset (SupportCellDescendant μ R hR k z))
    (seed : SupportCellDescendant μ R hR k z → SupportCellDescendant μ R hR k z)
    (Osc : SupportCellDescendant μ R hR k z → Prop) (I : ℕ) (M K : ℝ≥0∞)
    (hseed : ∀ i ∈ F, i.depth ≤ (seed i).depth ∧ (seed i).depth ≤ i.depth + I ∧
      (seed i).cell ⊆ i.cell)
    (hmass : ∀ i ∈ F, μ i.cell ≤ M * μ (seed i).cell)
    (hgap : ∀ i ∈ F, ∀ j ∈ F, (seed i).depth < j.depth → j.cell ⊆ (seed i).cell →
      ∃ t : {t // Osc t}, (seed i).depth ≤ t.val.depth ∧ t.val.depth < j.depth ∧ j.cell ⊆ t.val.cell)
    (hcarleson : ∑' t : {t // Osc t}, μ t.val.cell ≤ K * μ (cleanSupportCell μ R hR k z)) :
    ∑ i ∈ F, μ i.cell ≤ (M * ((I + 1 : ℕ) : ℝ≥0∞) * (1 + K)) *
      μ (cleanSupportCell μ R hR k z) := by
  classical
  obtain ⟨O, hO⟩ := exists_finite_pair_witnesses F
    (fun i j => (seed i).depth < j.depth ∧ j.cell ⊆ (seed i).cell)
    (fun i j (t : {t // Osc t}) =>
      (seed i).depth ≤ t.val.depth ∧ t.val.depth < j.depth ∧ j.cell ⊆ t.val.cell)
    (fun i hi j hj hrel => hgap i hi j hj hrel.1 hrel.2)
  let emb : {t // Osc t} ↪ SupportCellDescendant μ R hR k z := ⟨Subtype.val, Subtype.val_injective⟩
  have hbound := captured_cell_seed_mass_bound μ R hR k z F (O.map emb) seed I hseed (by
    intro i hi j hj hdepth hsub
    obtain ⟨t, ht, hlow, hhigh, hcontain⟩ := hO i hi j hj ⟨hdepth, hsub⟩
    exact ⟨t.val, Finset.mem_map.mpr ⟨t, ht, rfl⟩, hlow, hhigh, hcontain⟩)
  have hOmass : ∑ t ∈ O.map emb, μ t.cell ≤ K * μ (cleanSupportCell μ R hR k z) := by
    rw [Finset.sum_map]
    exact (ENNReal.sum_le_tsum O).trans hcarleson
  calc
    _ ≤ ∑ i ∈ F, M * μ (seed i).cell := Finset.sum_le_sum hmass
    _ = M * ∑ i ∈ F, μ (seed i).cell := (Finset.mul_sum ..).symm
    _ ≤ M * (((I + 1 : ℕ) : ℝ≥0∞) *
        (μ (cleanSupportCell μ R hR k z) + ∑ t ∈ O.map emb, μ t.cell)) :=
      mul_le_mul_of_nonneg_left hbound (zero_le)
    _ ≤ M * (((I + 1 : ℕ) : ℝ≥0∞) *
        (μ (cleanSupportCell μ R hR k z) + K * μ (cleanSupportCell μ R hR k z))) := by
      gcongr
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_UniformBetaPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform Carleson packing of cells with large bilateral beta

The packing constant is chosen before the measure. Cells without a flat
descendant are bounded separately; the remaining cells are charged through
flat seeds to descendants with large scalar oscillation.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem exists_uniform_bad_beta_carleson_constant {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G H ε : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure (Ambient d), GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r)) →
      (∀ η : ℝ, 0 < η → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated (p + 1) μ η f) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∀ F : Finset (SupportCellDescendant μ R hR k z),
      (∀ i ∈ F, ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)) →
      ∑ i ∈ F, μ i.cell ≤ ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z) := by
  classical
  let : NeZero d := ⟨by omega⟩
  obtain ⟨J, α, hα, _, hcharge⟩ := exists_uniform_flat_seed_global_charge hnd C G H ε D
    hC hG.le hH hε
  let A := H * (2 : ℝ) ^ propagationHorizon J + 2
  let Jo := H * propagationTestRadius J + 2
  let v := (H / 64) ^ (p + 2) * propagationScale J ^ 3
  have hHp : 0 < H := by linarith
  have hA : 1 ≤ A := by
    have ht : 0 ≤ H * (2 : ℝ) ^ propagationHorizon J := by positivity
    dsimp [A]
    linarith
  have hJo : 0 < Jo := by dsimp [Jo, propagationTestRadius] <;> positivity
  have hv : 0 < v := by have hδ := propagationScale_pos J; dsimp [v] <;> positivity
  obtain ⟨I, hI, Kc, hKc, hNoFlat⟩ := exists_uniform_no_flat_descendant_total_mass
    (by omega : 1 ≤ p + 1) hnd C G A α D hC hG hA hα
  obtain ⟨Ko, hKo, hOsc⟩ := exists_uniform_bad_descendant_total_mass p d C G Jo v D hC hG hJo hv
  let M := flatDescendantMassConstant (p + 1) C G I
  have hM : 0 < M := flatDescendantMassConstant_pos (p + 1) C G I hC hG
  let Kg := M * ((I : ℝ) + 1) * (1 + Ko)
  have hKg : 0 < Kg := by dsimp [Kg] <;> positivity
  have hcoeff : ENNReal.ofReal Kg = ENNReal.ofReal M * ((I + 1 : ℕ) : ℝ≥0∞) *
      (1 + ENNReal.ofReal Ko) := by
    dsimp [Kg]
    rw [ENNReal.ofReal_mul (mul_nonneg hM.le (by positivity)), ENNReal.ofReal_mul hM.le,
      ENNReal.ofReal_add zero_le_one hKo.le, ENNReal.ofReal_one]
    norm_num [ENNReal.ofReal_add]
  refine ⟨Kc + Kg, add_pos hKc hKg, ?_⟩
  intro μ hg hlower hRiesz R hR k z hcore F hbad
  let P (i : SupportCellDescendant μ R hR k z) : Prop :=
    HasFlatDescendant (p + 1) μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I A α
  let Good := F.filter P
  let Ex := F.filter (fun i => ¬ P i)
  have hEx : ∑ i ∈ Ex, μ i.cell ≤ ENNReal.ofReal Kc * μ (cleanSupportCell μ R hR k z) := by
    exact (finite_subtype_sum_le_tsum (fun i => ¬ P i) (fun i => μ i.cell) Ex
      (fun i hi => (Finset.mem_filter.mp hi).2)).trans (hNoFlat μ hg hlower hRiesz R hR k z hcore)
  have hex (i : SupportCellDescendant μ R hR k z) (hi : i ∈ Good) :
      ∃ S : SupportCellDescendant μ R hR k z,
        i.depth < S.depth ∧ S.depth ≤ i.depth + I ∧ S.cell ⊆ i.cell ∧
          A * S.radius ≤ i.radius / 8 ∧
          HasFlatCell (p + 1) μ R hR (k + S.depth) ⟨S.center, S.mem_net⟩ A α :=
    exists_global_flat_seed μ R hR k z i I A α (Finset.mem_filter.mp hi).2
  let seed (i : SupportCellDescendant μ R hR k z) := if hi : i ∈ Good then (hex i hi).choose else i
  have hs (i : SupportCellDescendant μ R hR k z) (hi : i ∈ Good) :
      i.depth < (seed i).depth ∧ (seed i).depth ≤ i.depth + I ∧ (seed i).cell ⊆ i.cell ∧
        A * (seed i).radius ≤ i.radius / 8 ∧
        HasFlatCell (p + 1) μ R hR (k + (seed i).depth) ⟨(seed i).center, (seed i).mem_net⟩ A α := by
    have heq : seed i = (hex i hi).choose := dite_eq_left hi
    rw [heq]
    exact (hex i hi).choose_spec
  let Osc (i : SupportCellDescendant μ R hR k z) : Prop :=
    ¬ ScalarOscillationBound (p + 1) μ i.center (Jo * i.radius) (v * i.radius ^ (p + 2))
  have hGood : ∑ i ∈ Good, μ i.cell ≤ ENNReal.ofReal Kg * μ (cleanSupportCell μ R hR k z) := by
    rw [hcoeff]
    apply finite_parent_mass_of_seed_charges μ R hR k z Good seed Osc I (ENNReal.ofReal M) (ENNReal.ofReal Ko)
    · intro i hi
      exact ⟨(hs i hi).1.le, (hs i hi).2.1, (hs i hi).2.2.1⟩
    · intro i hi
      exact SupportCellDescendant.relative_mass_bound μ C G hC hG hg hlower R hR k z hcore
        i (seed i) I (hs i hi).1.le (hs i hi).2.1 (hs i hi).2.2.1
    · intro i hi j hj hdepth hsub
      have hHpow : 0 < H * (2 : ℝ) ^ propagationHorizon J := by positivity
      have hh := flat_seed_enlargement_admissible μ R hR k z hcore i (seed i) A
        (H * (2 : ℝ) ^ propagationHorizon J) hHpow (by dsimp [A] <;> linarith) (hs i hi).2.2.2.1
      have horizon : AdmissibleRadius μ ((H * (seed i).radius) * (2 : ℝ) ^ propagationHorizon J) := by
        convert! hh using 1
        all_goals try with_reducible_and_instances rfl
        ring
      obtain ⟨t, hlow, hhigh, hcontain, _⟩ := hcharge μ hg hlower hRiesz R hR k z (seed i)
        horizon (hs i hi).2.2.2.2 j hdepth hsub (hbad j (Finset.mem_filter.mp hj).1)
      exact ⟨t, hlow, hhigh, hcontain⟩
    · exact hOsc μ hg hlower hRiesz R hR k z hcore
  have hsplit : (∑ i ∈ Good, μ i.cell) + (∑ i ∈ Ex, μ i.cell) = ∑ i ∈ F, μ i.cell :=
    Finset.sum_filter_add_sum_filter_not F P (fun i => μ i.cell)
  calc
    _ = (∑ i ∈ Ex, μ i.cell) + (∑ i ∈ Good, μ i.cell) := by rw [← hsplit, add_comm]
    _ ≤ ENNReal.ofReal Kc * μ (cleanSupportCell μ R hR k z) +
        ENNReal.ofReal Kg * μ (cleanSupportCell μ R hR k z) := add_le_add hEx hGood
    _ = _ := by rw [← add_mul, ENNReal.ofReal_add hKc.le hKg.le]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BetaDescendantTotalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Total mass of bad-beta descendants

Bad-beta descendants are the support-cell descendants whose enlarged-ball
bilateral beta number exceeds the threshold. Taking the supremum over finite
subsets upgrades the uniform finite Carleson estimate to their full `ENNReal`
mass sum, with the constant still chosen before the measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem exists_uniform_bad_beta_total_mass {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G H ε : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure (Ambient d), GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r)) →
      (∀ η : ℝ, 0 < η → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated (p + 1) μ η f) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∑' i : BadBetaDescendant (p + 1) μ R hR k z H ε,
        μ i.val.cell ≤ ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z) := by
  classical
  obtain ⟨K, hK, hpack⟩ := exists_uniform_bad_beta_carleson_constant hnd C G H ε D hC hG hH hε
  refine ⟨K, hK, ?_⟩
  intro μ hg hlower hRiesz R hR k z hcore
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  let emb : BadBetaDescendant (p + 1) μ R hR k z H ε ↪ SupportCellDescendant μ R hR k z :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hs : ∀ i ∈ s.map emb, ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius) := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact j.property
  have hb := hpack μ hg hlower hRiesz R hR k z hcore (s.map emb) hs
  simpa only [Finset.sum_map] using! hb

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SupportDescendantCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Countability of support-cell descendants

Every descendant is determined by its depth and its center in the corresponding
support lattice net. Encoding these data in a countable dependent sum proves
countability of the full descendant family, not only of each generation.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem supportCellDescendant_countable {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    Countable (SupportCellDescendant μ R hR k z) := by
  let (t : ℕ) : Countable (supportLatticeNets μ R hR (k + t)).points :=
    (supportLatticeNets_countable μ R hR (k + t)).to_subtype
  let f (i : SupportCellDescendant μ R hR k z) :
      Σ t : ℕ, (supportLatticeNets μ R hR (k + t)).points :=
    ⟨i.depth, ⟨i.center, i.mem_net⟩⟩
  apply Function.Injective.countable (f := f)
  intro i j hij
  rcases i with ⟨ti, xi, hxi, hai⟩
  rcases j with ⟨tj, xj, hxj, haj⟩
  have ht : ti = tj := congrArg Sigma.fst hij
  subst tj
  have hc : (⟨xi, hxi⟩ : (supportLatticeNets μ R hR (k + ti)).points) = ⟨xj, hxj⟩ :=
    eq_of_heq (Sigma.mk.inj_iff.mp hij).2
  have hx : xi = xj := congrArg Subtype.val hc
  subst xj
  rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_PointCellChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_unique_support_descendant_at_point {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (x : Ambient d)
    (hx : x ∈ cleanSupportCell μ R hR k z) (t : ℕ) :
    ∃! i : SupportCellDescendant μ R hR k z, i.depth = t ∧ x ∈ i.cell := by
  rw [cleanSupportCell_eq_iUnion_descendants μ R hR k t z] at hx
  obtain ⟨w, hw⟩ := mem_iUnion.mp hx
  obtain ⟨hanc, hxw⟩ := mem_iUnion.mp hw
  let i : SupportCellDescendant μ R hR k z :=
    { depth := t, center := w, mem_net := w.property, ancestor := hanc }
  refine ⟨i, ⟨rfl, hxw⟩, ?_⟩
  intro j hj
  exact j.eq_of_common_point_same_depth i hj.1 x hj.2 hxw

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ImmediateChildPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem cleanSupportCell_eq_immediate_children {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    cleanSupportCell μ R hR k z = ⋃ i : supportImmediateChildren μ R hR k z, i.val.cell := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, _⟩ := exists_unique_support_descendant_at_point μ R hR k z x hx 1
    exact mem_iUnion.mpr ⟨⟨i, (mem_supportImmediateChildren μ R hR k z i).mpr hi.1⟩, hi.2⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact i.val.cell_subset_top hi

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellBadCountBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem cellBadCountBound_zero_forbids_bad_descendant
    {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
    {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q i : SupportCellDescendant μ R hR k z) (hdepth : q.depth ≤ i.depth)
    (hsub : i.cell ⊆ q.cell) (x : Ambient d) (hx : x ∈ i.cell)
    (hcount : cellBadCountBound Bad q 0 x) : ¬ Bad i := by
  classical
  intro hbad
  have h := hcount {i} (by
    intro j hj
    have heq : j = i := Finset.mem_singleton.mp hj
    subst j
    exact ⟨hbad, hdepth, hsub, hx⟩)
  norm_num at h

theorem cellBadCountBound_descend_past_bad
    {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
    {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q i w : SupportCellDescendant μ R hR k z)
    (hqi : q.depth ≤ i.depth) (hiq : i.cell ⊆ q.cell) (hbad : Bad i)
    (hiw : i.depth < w.depth) (hwi : w.cell ⊆ i.cell)
    (N : ℕ) (x : Ambient d) (hx : x ∈ w.cell)
    (hcount : cellBadCountBound Bad q (N + 1) x) : cellBadCountBound Bad w N x := by
  classical
  intro F hF
  have hnot : i ∉ F := by
    intro hi
    have h := (hF i hi).2.1
    omega
  have h := hcount (insert i F) (by
    intro j hj
    rcases Finset.mem_insert.mp hj with heq | hjF
    · subst j
      exact ⟨hbad, hqi, hiq, hwi hx⟩
    · have hj := hF j hjF
      exact ⟨hj.1, hqi.trans (hiw.le.trans hj.2.1),
        hj.2.2.1.trans (hwi.trans hiq), hj.2.2.2⟩)
  rw [Finset.card_insert_of_notMem hnot] at h
  omega

theorem cellBadCountBound_of_subtype_incidence_bound
    {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
    {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (N : ℕ) (x : Ambient d)
    (hcount : ∀ F : Finset {i : SupportCellDescendant μ R hR k z // Bad i},
      (∀ i ∈ F, x ∈ i.val.cell) → F.card ≤ N) : cellBadCountBound Bad q N x := by
  classical
  intro F hF
  let e : F ↪ {i : SupportCellDescendant μ R hR k z // Bad i} :=
    ⟨fun i => ⟨i.val, (hF i.val i.property).1⟩,
      fun i j h => by
        apply Subtype.ext
        exact congrArg (fun a : {i : SupportCellDescendant μ R hR k z // Bad i} => a.val) h⟩
  have h := hcount (F.attach.map e) (by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact (hF j.val j.property).2.2.2)
  simpa only [Finset.card_map, Finset.card_attach] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CountableCellMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Countable cell multiplicity

The sum of cell indicators measures pointwise overlap. Its integral is the total
cell mass, giving tail bounds, almost-everywhere finite incidence, and lower
bounds for the mass where the multiplicity is controlled.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped ENNReal

theorem cellMultiplicity_measurable {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (cellMultiplicity A) :=
  Measurable.tsum (fun i => measurable_const.indicator (hA i))

theorem lintegral_cellMultiplicity {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (μ : Measure X) (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    (∫⁻ x, cellMultiplicity A x ∂μ) = ∑' i, μ (A i) := by
  unfold cellMultiplicity
  rw [lintegral_tsum
    (fun i => (measurable_const.indicator (hA i)).aemeasurable)]
  exact tsum_congr (fun i => lintegral_indicator_one (hA i))

theorem cellMultiplicity_tail_bound {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (μ : Measure X) (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i))
    (B t : ℝ≥0∞) (hB : ∑' i, μ (A i) ≤ B) (ht : t ≠ 0) (htt : t ≠ ∞) :
    μ {x | t ≤ cellMultiplicity A x} ≤ B / t := by
  have h := meas_ge_le_lintegral_div (μ := μ)
    (cellMultiplicity_measurable A hA).aemeasurable ht htt
  rw [lintegral_cellMultiplicity μ A hA] at h
  exact h.trans (ENNReal.div_le_div_right hB t)

theorem ae_finite_cell_incidence {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (μ : Measure X) (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hfinite : ∑' i, μ (A i) ≠ ∞) :
    ∀ᵐ x ∂μ, {i | x ∈ A i}.Finite := by
  classical
  have hint : (∫⁻ x, cellMultiplicity A x ∂μ) ≠ ∞ := by
    rwa [lintegral_cellMultiplicity μ A hA]
  filter_upwards [ae_lt_top (cellMultiplicity_measurable A hA) hint] with x hx
  have hf := ENNReal.finite_const_le_of_tsum_ne_top hx.ne (ε := 1) one_ne_zero
  apply hf.subset
  intro i hi
  change x ∈ A i at hi
  change 1 ≤ (A i).indicator (fun _ => (1 : ℝ≥0∞)) x
  rw [Set.indicator_of_mem hi]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_BadBetaStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Stopping estimates from bad-beta multiplicity

Bad-beta descendants form a countable family of measurable cells. Their total-mass
packing bound controls the tail of the cell multiplicity and gives almost-everywhere
finite incidence. At the threshold twice the packing constant, at least half the
root-cell mass remains in the low-multiplicity region.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem badBetaDescendant_countable {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (H ε : ℝ) : Countable (BadBetaDescendant n μ R hR k z H ε) := by
  let := supportCellDescendant_countable μ R hR k z
  unfold BadBetaDescendant
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem badBetaMultiplicity_measurable {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (H ε : ℝ) : Measurable (badBetaMultiplicity n μ R hR k z H ε) := by
  let := badBetaDescendant_countable n μ R hR k z H ε
  exact cellMultiplicity_measurable (fun i : BadBetaDescendant n μ R hR k z H ε => i.val.cell)
    (fun i => cleanSupportCell_measurable
    μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_CellRestartPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem finite_restart_roots_mass_le {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Bad : SupportCellDescendant μ R hR k z → Prop) (K : ℝ≥0∞)
    (hpack : ∑' q : {q // Bad q}, μ q.val.cell ≤ K * μ (cleanSupportCell μ R hR k z))
    (F : Finset (SupportCellDescendant μ R hR k z))
    (hF : ∀ i ∈ F, cellRestartsAfter Bad i) :
    ∑ i ∈ F, μ i.cell ≤ (1 + K) * μ (cleanSupportCell μ R hR k z) := by
  have h := finite_parent_mass_of_seed_charges μ R hR k z F id Bad 0 1 K
    (fun i _ => ⟨le_rfl, by simp, Subset.rfl⟩)
    (fun i _ => by simp)
    (by
      intro i _ j hj hdepth _
      change i.depth < j.depth at hdepth
      rcases hF j hj with hzero | ⟨q, hbad, hqdepth, hsub⟩
      · omega
      · refine ⟨⟨q, hbad⟩, ?_, ?_, hsub⟩
        · change i.depth ≤ q.depth
          omega
        · change q.depth < j.depth
          omega)
    hpack
  simpa only [Nat.zero_add, Nat.cast_one, one_mul] using! h

theorem restart_roots_total_mass_le {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Bad : SupportCellDescendant μ R hR k z → Prop) (K : ℝ≥0∞)
    (hpack : ∑' q : {q // Bad q}, μ q.val.cell ≤ K * μ (cleanSupportCell μ R hR k z)) :
    ∑' i : {i // cellRestartsAfter Bad i}, μ i.val.cell ≤
      (1 + K) * μ (cleanSupportCell μ R hR k z) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  let e : {i // cellRestartsAfter Bad i} ↪ SupportCellDescendant μ R hR k z :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hF : ∀ i ∈ F.map e, cellRestartsAfter Bad i := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact j.property
  have h := finite_restart_roots_mass_le μ R hR k z Bad K hpack (F.map e) hF
  simpa only [Finset.sum_map] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_RestartCoverageInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restart coverage with a finite bad-cell budget

The iterated chart constant records the cost of assembling child charts. Induction
on the bad-cell budget covers points outside the restart remainders, since passing
a bad descendant reduces the remaining budget. Countable subadditivity then bounds
the uncovered mass by the original deficit and the sum of all remainder masses.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
  (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
  (Bad : SupportCellDescendant μ R hR k z → Prop)

variable (remainder parent : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d)) (next : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q})
  (step : ℝ≥0 → ℝ≥0)
  (hnext : ∀ q w, w ∈ next q → ∃ i : SupportCellDescendant μ R hR k z,
    q.val.depth ≤ i.depth ∧ i.cell ⊆ q.val.cell ∧ Bad i ∧
      i.depth < w.val.depth ∧ w.val.cell ⊆ i.cell)
  (hpartition : ∀ q, q.val.cell \ remainder q ⊆ parent q ∪
    ⋃ w : next q, w.val.val.cell)
  (hassemble : ∀ (q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}) (M : ℝ≥0)
    (child : ∀ w : next q, ball (0 : Ambient n) w.val.val.radius → Ambient d),
    (∀ w, LipschitzWith M (child w)) →
    (∀ w, Set.range (child w) ⊆ closedBall w.val.val.center (2 * w.val.val.radius)) →
    ∃ g : ball (0 : Ambient n) q.val.radius → Ambient d,
      LipschitzWith (step M) g ∧ Set.range g ⊆ closedBall q.val.center (2 * q.val.radius) ∧
      parent q ⊆ Set.range g ∧
      ∀ w, w.val.val.cell ∩ Set.range (child w) ⊆ Set.range g)

include hnext hpartition hassemble

theorem exists_restart_chart_of_bad_budget (b : ℕ) (q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}) :
    ∃ g : ball (0 : Ambient n) q.val.radius → Ambient d,
      LipschitzWith (badBudgetChartConstant step b) g ∧
      Set.range g ⊆ closedBall q.val.center (2 * q.val.radius) ∧
      ∀ x ∈ q.val.cell, cellBadCountBound Bad q.val b x →
        x ∉ ⋃ r : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}, remainder r → x ∈ Set.range g := by
  classical
  induction b generalizing q with
  | zero =>
    let child : ∀ w : next q, ball (0 : Ambient n) w.val.val.radius → Ambient d :=
      fun w _ => w.val.val.center
    have hlip (w : next q) : LipschitzWith 1 (child w) :=
      (LipschitzWith.const w.val.val.center).weaken (by norm_num)
    have himage (w : next q) : Set.range (child w) ⊆
        closedBall w.val.val.center (2 * w.val.val.radius) := by
      rintro y ⟨u, rfl⟩
      exact mem_closedBall_self (by positivity [w.val.val.radius_pos])
    obtain ⟨g, hg, hgrange, hparent, _⟩ := hassemble q 1 child hlip himage
    refine ⟨g, hg, hgrange, ?_⟩
    intro x hx hcount hnot
    have hr : x ∉ remainder q := fun hr => hnot (mem_iUnion.mpr ⟨q, hr⟩)
    have hpart : x ∈ parent q ∨ x ∈ ⋃ w : next q, w.val.val.cell :=
      hpartition q ⟨hx, hr⟩
    apply hpart.elim
    · intro hp
      exact hparent hp
    · intro hw
      obtain ⟨w, hxw⟩ := mem_iUnion.mp hw
      obtain ⟨i, hqi, hiq, hbad, _, hwi⟩ := hnext q w.val w.property
      exact False.elim ((cellBadCountBound_zero_forbids_bad_descendant
        Bad q.val i hqi hiq x (hwi hxw) hcount) hbad)
  | succ b ih =>
    have hc (w : next q) := ih w.val
    choose child hchildLip hchildRange hchildCover using hc
    obtain ⟨g, hg, hgrange, hparent, hchildren⟩ := hassemble q
      (badBudgetChartConstant step b) child hchildLip hchildRange
    refine ⟨g, hg, hgrange, ?_⟩
    intro x hx hcount hnot
    have hr : x ∉ remainder q := fun hr => hnot (mem_iUnion.mpr ⟨q, hr⟩)
    have hpart : x ∈ parent q ∨ x ∈ ⋃ w : next q, w.val.val.cell :=
      hpartition q ⟨hx, hr⟩
    apply hpart.elim
    · intro hp
      exact hparent hp
    · intro hw
      obtain ⟨w, hxw⟩ := mem_iUnion.mp hw
      obtain ⟨i, hqi, hiq, hbad, hiw, hwi⟩ := hnext q w.val w.property
      have hcount' := cellBadCountBound_descend_past_bad
        Bad q.val i w.val.val hqi hiq hbad hiw hwi b x hxw hcount
      exact hchildren w ⟨hxw, hchildCover w x hxw hcount' hnot⟩

theorem exists_restart_chart_with_original_mass_deficit (b : ℕ) (q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q})
    (A : Set (Ambient d))
    (hcount : ∀ x ∈ q.val.cell ∩ A, cellBadCountBound Bad q.val b x) :
    ∃ g : ball (0 : Ambient n) q.val.radius → Ambient d,
      LipschitzWith (badBudgetChartConstant step b) g ∧
      Set.range g ⊆ closedBall q.val.center (2 * q.val.radius) ∧
      (q.val.cell ∩ A) \ (⋃ r : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}, remainder r) ⊆ Set.range g ∧
      μ (q.val.cell \ Set.range g) ≤ μ (q.val.cell \ A) + ∑' r : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}, μ (remainder r) := by
  let := supportCellDescendant_countable μ R hR k z
  obtain ⟨g, hg, hgrange, hcover⟩ := exists_restart_chart_of_bad_budget
    μ R hR k z Bad remainder parent next step hnext hpartition hassemble b q
  have hcovered : (q.val.cell ∩ A) \ (⋃ r : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}, remainder r) ⊆ Set.range g := by
    intro x hx
    exact hcover x hx.1.1 (hcount x hx.1) hx.2
  have hsub : q.val.cell \ Set.range g ⊆ (q.val.cell \ A) ∪ ⋃ r : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}, remainder r := by
    intro x hx
    by_cases ha : x ∈ A
    · right
      by_contra hn
      exact hx.2 (hcovered ⟨⟨hx.1, ha⟩, hn⟩)
    · exact Or.inl ⟨hx.1, ha⟩
  refine ⟨g, hg, hgrange, hcovered, ?_⟩
  exact ((measure_mono (μ := μ) hsub).trans (measure_union_le _ _)).trans
    (add_le_add le_rfl (measure_iUnion_le _))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_RestartLossBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Summing relative losses over restarts

A packing bound for restart-cell masses turns a uniform relative loss bound into a total
budget. Choosing the relative tolerance as the requested budget divided by the positive
packing constant yields the original AD/Riesz restart estimate.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem relative_losses_sum_le_packed_mass {ι : Type*}
    (mass loss : ι → ℝ≥0∞) (δ K T : ℝ≥0∞)
    (hloss : ∀ i, loss i ≤ δ * mass i) (hpack : ∑' i, mass i ≤ K * T) :
    (∑' i, loss i) ≤ (δ * K) * T := by
  calc
    _ ≤ ∑' i, δ * mass i := ENNReal.tsum_le_tsum hloss
    _ = δ * ∑' i, mass i := ENNReal.tsum_mul_left
    _ ≤ δ * (K * T) := mul_le_mul_right hpack δ
    _ = _ := (mul_assoc _ _ _).symm

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_SelectedRestartTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
  {k : ℕ} {z : (supportLatticeNets μ R hR k).points}

theorem selected_restart_next_consumes_bad_cell
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d))
    (w : {w : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad w})
    (hw : w ∈ selectedRestartNext Bad q E) :
    ∃ i : SupportCellDescendant μ R hR k z,
      q.depth ≤ i.depth ∧ i.cell ⊆ q.cell ∧ Bad i ∧
        i.depth < w.val.depth ∧ w.val.cell ⊆ i.cell := by
  obtain ⟨i, j, hw⟩ := hw
  have hbad : Bad (q.compose i.val) := not_not.mp i.property.1.1
  have hj := (mem_supportImmediateChildren μ R hR _ _ j.val).mp j.property
  refine ⟨q.compose i.val, ?_, ?_, hbad, ?_, ?_⟩
  · rw [SupportCellDescendant.compose_depth]
    omega
  · rw [SupportCellDescendant.compose_cell]
    exact i.val.cell_subset_top
  · rw [hw, SupportCellDescendant.compose_depth, SupportCellDescendant.compose_depth,
      SupportCellDescendant.compose_depth, hj]
    omega
  · rw [hw, SupportCellDescendant.compose_cell, SupportCellDescendant.compose_cell,
      SupportCellDescendant.compose_cell]
    exact j.val.cell_subset_top

theorem selected_restart_partition
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) :
    q.cell \ selectedRestartRemainder Bad q E ⊆ selectedRestartParent Bad q E ∪
      ⋃ w : selectedRestartNext Bad q E, w.val.val.cell := by
  classical
  intro x hx
  have hret : x ∈ selectedRestartParent Bad q E ∪
      ⋃ i : relativeSelectedRestartStops Bad q E, i.val.cell := by
    by_contra hn
    exact hx.2 ⟨hx.1, hn⟩
  rcases hret with hp | hi
  · exact Or.inl hp
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hi
    have hxj : x ∈ ⋃ j : supportImmediateChildren μ R hR
        (k + q.depth + i.val.depth) ⟨i.val.center, i.val.mem_net⟩, j.val.cell :=
      cleanSupportCell_eq_immediate_children μ R hR _ _ ▸ hxi
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxj
    let w : {w : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad w} :=
      ⟨q.compose (i.val.compose j.val), selected_restart_child_is_restart Bad q E i j⟩
    have hw : w ∈ selectedRestartNext Bad q E := ⟨i, j, rfl⟩
    refine Or.inr (mem_iUnion.mpr ⟨⟨w, hw⟩, ?_⟩)
    change x ∈ (q.compose (i.val.compose j.val)).cell
    simpa only [SupportCellDescendant.compose_cell] using! hxj

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Uniformity_RestartBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform budgets for bad cells and restarts

The class-uniform bad-beta packing constant controls multiplicity tails and the
total mass of restart roots. A relative loss tolerance and a finite bad-depth
budget are chosen before the measure, using only the fixed geometric and Riesz
bounds. Splitting the desired deficit into two halves pays separately for the
discarded high-multiplicity set and the remainders of selected restart regions.
These budgets feed the recursive chart assembly without changing its image or
Lipschitz conclusions.
-/

namespace RieszRectifiability
noncomputable section
open MeasureTheory Metric Set Topology
open scoped NNReal ENNReal

theorem quantitative_bad_beta_total_mass {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G)
    (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (μ : Measure (Ambient d)) [μ.Regular],
      ADRegularWithConstant (p + 1) C μ → GlobalUpperGrowth (p + 1) G μ →
      RieszL2BoundedWithConstant (p + 1) D μ →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∑' i : BadBetaDescendant (p + 1) μ R hR k z H ε,
        μ i.val.cell ≤ ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨K, hK, hpack⟩ := exists_uniform_bad_beta_total_mass hnd C G H ε D
    (zero_lt_one.trans_le hC) hG hH hε
  refine ⟨K, hK, ?_⟩
  intro μ _hreg hAD hg hRiesz
  exact hpack μ hg (fun x hx r hr => (hAD.2 x hx r hr).1) hRiesz

theorem quantitative_bad_beta_stopping {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
      GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      (∀ t : ℝ≥0∞, t ≠ 0 → t ≠ ∞ →
        μ {x | t ≤ badBetaMultiplicity (p + 1) μ R hR k z H ε x} ≤
          (ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z)) / t) ∧
      (∀ᵐ x ∂μ, {i : BadBetaDescendant (p + 1) μ R hR k z H ε | x ∈ i.val.cell}.Finite) := by
  obtain ⟨K, hK, hpack⟩ := quantitative_bad_beta_total_mass hnd C G D hC hG H ε hH hε
  refine ⟨K, hK, ?_⟩
  intro μ _hreg hAD hg hRiesz R hR k z hcore
  have hpack := hpack μ hAD hg hRiesz
  let := badBetaDescendant_countable (p + 1) μ R hR k z H ε
  let A (i : BadBetaDescendant (p + 1) μ R hR k z H ε) := i.val.cell
  have hA : ∀ i, MeasurableSet (A i) := fun i => cleanSupportCell_measurable
    μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩
  have hp := hpack R hR k z hcore
  constructor
  · intro t ht htt
    exact cellMultiplicity_tail_bound μ A hA _ t hp ht htt
  · have htop : μ (cleanSupportCell μ R hR k z) < ∞ :=
      (measure_mono (show cleanSupportCell μ R hR k z ⊆ supportLatticeCell μ R hR k z
        from fun _ hx => hx.1)).trans_lt (supportLatticeCell_compact μ R hR k z).measure_lt_top
    apply ae_finite_cell_incidence μ A hA
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop.ne) hp

theorem quantitative_bad_beta_restart_mass {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
      GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∑' i : {i : SupportCellDescendant μ R hR k z // cellRestartsAfter
        (fun q => ε ≤ bilateralBeta (p + 1) μ q.center (H * q.radius)) i},
        μ i.val.cell ≤ ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨K, hK, hpack⟩ := quantitative_bad_beta_total_mass hnd C G D hC hG H ε hH hε
  refine ⟨1 + K, by linarith, ?_⟩
  intro μ _hreg hAD hg hRiesz R hR k z hcore
  have hpack := hpack μ hAD hg hRiesz
  have h := restart_roots_total_mass_le μ R hR k z
    (fun q => ε ≤ bilateralBeta (p + 1) μ q.center (H * q.radius))
    (ENNReal.ofReal K) (hpack R hR k z hcore)
  simpa only [ENNReal.ofReal_add zero_le_one hK.le, ENNReal.ofReal_one] using! h

theorem quantitative_restart_loss_budget {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
      GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∀ loss : {i : SupportCellDescendant μ R hR k z // cellRestartsAfter
        (fun q => ε ≤ bilateralBeta (p + 1) μ q.center (H * q.radius)) i} → ℝ≥0∞,
        (∀ i, loss i ≤ ENNReal.ofReal δ * μ i.val.cell) →
        (∑' i, loss i) ≤ ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨K, hK, hpack⟩ := quantitative_bad_beta_restart_mass hnd C G D hC hG H ε hH hε
  refine ⟨ζ / K, div_pos hζ hK, ?_⟩
  intro μ _hreg hAD hg hRiesz R hR k z hcore loss hloss
  have hpack := hpack μ hAD hg hRiesz
  have h := relative_losses_sum_le_packed_mass (fun i => μ i.val.cell) loss
    (ENNReal.ofReal (ζ / K)) (ENNReal.ofReal K) (μ (cleanSupportCell μ R hR k z))
    hloss (hpack R hR k z hcore)
  have heq : ENNReal.ofReal (ζ / K) * ENNReal.ofReal K = ENNReal.ofReal ζ := by
    rw [← ENNReal.ofReal_mul (div_nonneg hζ.le hK.le), div_mul_cancel₀ ζ hK.ne']
  rwa [heq] at h

theorem quantitative_bad_depth_loss_budget {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
      GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      μ {x | (N : ℝ≥0∞) ≤ badBetaMultiplicity (p + 1) μ R hR k z H ε x} ≤
        ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨K, hK, hstop⟩ := quantitative_bad_beta_stopping hnd C G D hC hG H ε hH hε
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (K / ζ))
  have hN1 : 1 ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hNratio : K / ζ ≤ (N : ℝ) := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by exact_mod_cast lt_of_lt_of_le zero_lt_one hN1
  have hNrpos : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hratio : K / (N : ℝ) ≤ ζ := by
    apply (div_le_iff₀ hNrpos).mpr
    have h := (div_le_iff₀ hζ).mp hNratio
    nlinarith
  have hcoef : ENNReal.ofReal K / (N : ℝ≥0∞) ≤ ENNReal.ofReal ζ := by
    have h := ENNReal.ofReal_le_ofReal hratio
    simpa only [ENNReal.ofReal_div_of_pos hNrpos, ENNReal.ofReal_natCast] using! h
  refine ⟨N, hNpos, ?_⟩
  intro μ _hreg hAD hg hRiesz R hR k z hcore
  have hstop := hstop μ hAD hg hRiesz
  have ht := (hstop R hR k z hcore).1 (N : ℝ≥0∞) (by exact_mod_cast hNpos.ne') (by simp)
  calc
    _ ≤ (ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z)) / (N : ℝ≥0∞) := ht
    _ = (ENNReal.ofReal K / (N : ℝ≥0∞)) * μ (cleanSupportCell μ R hR k z) := by
      simp only [div_eq_mul_inv, mul_right_comm]
    _ ≤ _ := mul_le_mul_left hcoef _

theorem quantitative_cell_bad_count_budget {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
      GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∃ A : Set (Ambient d), MeasurableSet A ∧ A ⊆ cleanSupportCell μ R hR k z ∧
        μ (cleanSupportCell μ R hR k z \ A) ≤ ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) ∧
        ∀ x ∈ A, ∀ q : SupportCellDescendant μ R hR k z,
          cellBadCountBound (fun i => ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)) q N x := by
  classical
  obtain ⟨N, hN, htail⟩ := quantitative_bad_depth_loss_budget hnd C G D hC hG H ε hH hε ζ hζ
  refine ⟨N, hN, ?_⟩
  intro μ _hreg hAD hg hRiesz R hR k z hcore
  have htail := htail μ hAD hg hRiesz
  let A := {x ∈ cleanSupportCell μ R hR k z |
    badBetaMultiplicity (p + 1) μ R hR k z H ε x < (N : ℝ≥0∞)}
  have hAmeas : MeasurableSet A := (cleanSupportCell_measurable μ R hR k z).inter
    (measurableSet_lt (badBetaMultiplicity_measurable (p + 1) μ R hR k z H ε) measurable_const)
  have hsub : cleanSupportCell μ R hR k z \ A ⊆
      {x | (N : ℝ≥0∞) ≤ badBetaMultiplicity (p + 1) μ R hR k z H ε x} := by
    intro x hx
    by_contra hn
    exact hx.2 ⟨hx.1, lt_of_not_ge hn⟩
  refine ⟨A, hAmeas, fun _ hx => hx.1, (measure_mono hsub).trans (htail R hR k z hcore), ?_⟩
  intro x hx q
  apply cellBadCountBound_of_subtype_incidence_bound _ q N x
  intro F hF
  have hcount : (F.card : ℝ≥0∞) ≤ badBetaMultiplicity (p + 1) μ R hR k z H ε x := by
    calc
      _ = ∑ i ∈ F, i.val.cell.indicator (fun _ => (1 : ℝ≥0∞)) x := by
        symm
        calc
          _ = ∑ _i ∈ F, (1 : ℝ≥0∞) :=
            Finset.sum_congr rfl (fun i hi => Set.indicator_of_mem (hF i hi) _)
          _ = _ := by simp
      _ ≤ _ := ENNReal.sum_le_tsum F
  exact_mod_cast hcount.trans hx.2.le

theorem quantitative_selected_restart_uniform_deficit_oai {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ b : ℕ, 0 < b ∧
      ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
      GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ → ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
        AdmissibleRadius μ (latticeRadius R k / 8) →
        let Bad := fun i : SupportCellDescendant μ R hR k z =>
          ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)
        ∀ (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
          (step : ℝ≥0 → ℝ≥0),
          HasSelectedRestartAssembly (p + 1) Bad E step →
          (∀ q, μ (selectedRestartRemainder Bad q.val (E q)) ≤ ENNReal.ofReal δ * μ q.val.cell) →
          ∃ g : ball (0 : Ambient (p + 1)) (latticeRadius R k) → Ambient d,
            LipschitzWith (badBudgetChartConstant step b) g ∧
            Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
            μ (cleanSupportCell μ R hR k z \ Set.range g) ≤
              ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨δ, hδ, hregions⟩ := quantitative_restart_loss_budget hnd C G D hC hG H ε hH hε
    (ζ / 2) (half_pos hζ)
  obtain ⟨b, hb, hcounts⟩ := quantitative_cell_bad_count_budget hnd C G D hC hG H ε hH hε
    (ζ / 2) (half_pos hζ)
  refine ⟨δ, hδ, b, hb, ?_⟩
  intro μ _hreg hAD hg hRiesz R hR k z hcore
  have hregions := hregions μ hAD hg hRiesz
  have hcounts := hcounts μ hAD hg hRiesz
  dsimp only
  intro E step hassemble hloss
  let Bad := fun i : SupportCellDescendant μ R hR k z =>
    ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)
  let q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} :=
    ⟨supportCellRoot μ R hR k z, Or.inl rfl⟩
  obtain ⟨A, _, _, hAmass, hAcount⟩ := hcounts R hR k z hcore
  obtain ⟨g, hg, hgrange, _, hdeficit⟩ := exists_restart_chart_with_original_mass_deficit
    μ R hR k z Bad
    (fun r => selectedRestartRemainder Bad r.val (E r))
    (fun r => selectedRestartParent Bad r.val (E r))
    (fun r => selectedRestartNext Bad r.val (E r)) step
    (fun r w hw => selected_restart_next_consumes_bad_cell Bad r.val (E r) w hw)
    (fun r => selected_restart_partition Bad r.val (E r)) hassemble b q A
    (fun x hx => hAcount x hx.2 q.val)
  have hsum := hregions R hR k z hcore
    (fun r => μ (selectedRestartRemainder Bad r.val (E r))) hloss
  have hbound := hdeficit.trans (add_le_add hAmass hsum)
  have heq : ENNReal.ofReal (ζ / 2) + ENNReal.ofReal (ζ / 2) = ENNReal.ofReal ζ := by
    rw [← ENNReal.ofReal_add (half_pos hζ).le (half_pos hζ).le, add_halves]
  refine ⟨g, hg, hgrange, ?_⟩
  simpa only [← add_mul, heq] using! hbound

end
end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.quantitative_selected_restart_uniform_deficit_oai := @OAI.RieszRectifiability.quantitative_selected_restart_uniform_deficit_oai
