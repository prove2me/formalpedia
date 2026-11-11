-- Prove2me | solution 1 for OAI.RieszRectifiability.exists_dyadic_source_excess_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:27.405285+00:00
-- url     : https://prove2.me/submissions/8fe508a0-ebd1-4f0b-8663-93111ce77f3f

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000
import Definitions.Def_OAIQ231Rr001
import Theorems.Thm_OAI_RieszRectifiability_exists_common_height_with_fractional_equation
import Theorems.Thm_OAI_RieszRectifiability_exists_dyadic_flat_measure_limit_with_energy
import Theorems.Thm_OAI_RieszRectifiability_normal_frame_source_data_on_ball
import Theorems.Thm_OAI_RieszRectifiability_represented_fractional_height_ae_affine

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_AffineGraphPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Function Metric

theorem affineGraphLinear_leftInverse {n q d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ)
    (horth : ∀ y, L.toContinuousLinearMap.adjoint (N y) = 0) :
    LeftInverse L.toContinuousLinearMap.adjoint (affineGraphLinear L N A δ) := by
  intro t
  have hL : L.toContinuousLinearMap.adjoint (L t) = t :=
    DFunLike.congr_fun L.adjoint_comp_self t
  change L.toContinuousLinearMap.adjoint (L t + δ • N (A t)) = t
  rw [map_add, map_smul, hL, horth, smul_zero, add_zero]

theorem affineGraphPlane_direction_finrank {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (b : Ambient q) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ)
    (horth : ∀ y, L.toContinuousLinearMap.adjoint (N y) = 0) :
    Module.finrank ℝ (affineGraphPlane a L N b A δ).direction = n := by
  rw [affineGraphPlane, AffineSubspace.direction_mk']
  rw [LinearMap.finrank_range_of_inj
    (affineGraphLinear_leftInverse L N A δ horth).injective]
  exact finrank_euclideanSpace_fin

theorem affineGraphPoint_mem {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (b : Ambient q) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ) (t : Ambient n) :
    a + L t + δ • N (b + A t) ∈ affineGraphPlane a L N b A δ := by
  rw [affineGraphPlane, AffineSubspace.mem_mk']
  refine ⟨t, ?_⟩
  change L t + δ • N (A t) = a + L t + δ • N (b + A t) - (a + δ • N b)
  rw [map_add, smul_add]
  abel

theorem affineGraphPlane_infDist_le {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (b : Ambient q) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ)
    (x : Ambient d) (t : Ambient n) (s : Ambient q) (hx : x - a = L t + N s) :
    infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) ≤ ‖s - δ • (b + A t)‖ := by
  have hdist : dist x (a + L t + δ • N (b + A t)) = ‖s - δ • (b + A t)‖ := by
    rw [dist_eq_norm]
    have hdiff : x - (a + L t + δ • N (b + A t)) = N (s - δ • (b + A t)) := by
      rw [map_sub, map_smul]
      have heq : x = a + L t + N s := by rw [add_assoc, ← hx]; abel
      rw [heq]
      abel
    rw [hdiff, N.norm_map]
  exact (infDist_le_dist_of_mem (affineGraphPoint_mem a L N b A δ t)).trans_eq hdist

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_AffineGraphExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Topology

theorem affineGraphPlane_normalized_distance_sq_le {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (b : Ambient q) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ) (hδ : 0 < δ)
    (x : Ambient d) (t : Ambient n) (w : Ambient q) (hx : x - a = L t + δ • N w) :
    (infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) / δ) ^ 2 ≤
      ‖w - (b + A t)‖ ^ 2 := by
  have hraw := affineGraphPlane_infDist_le a L N b A δ x t (δ • w)
    (by simpa only [map_smul] using! hx)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hδ] at hraw
  have hb : infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) / δ ≤
      ‖w - (b + A t)‖ :=
    (div_le_iff₀ hδ).mpr (by simpa only [mul_comm] using! hraw)
  exact (sq_le_sq₀ (div_nonneg infDist_nonneg hδ.le) (norm_nonneg _)).mpr hb

theorem affineGraphPlane_integral_normalized_distance_sq_le {n q d : ℕ}
    (μ : Measure (Ambient d)) (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (b : Ambient q) (A : Ambient n →L[ℝ] Ambient q) (δ : ℝ) (hδ : 0 < δ)
    (t : Ambient d → Ambient n) (w : Ambient d → Ambient q)
    (hx : ∀ᵐ x ∂μ, x - a = L (t x) + δ • N (w x))
    (hi : Integrable (fun x => ‖w x - (b + A (t x))‖ ^ 2) μ) :
    Integrable (fun x =>
      (infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) / δ) ^ 2) μ ∧
    (∫ x, (infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) / δ) ^ 2 ∂μ) ≤
      ∫ x, ‖w x - (b + A (t x))‖ ^ 2 ∂μ := by
  have hb : ∀ᵐ x ∂μ,
      (infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) / δ) ^ 2 ≤
        ‖w x - (b + A (t x))‖ ^ 2 := by
    filter_upwards [hx] with x hx
    exact affineGraphPlane_normalized_distance_sq_le a L N b A δ hδ x (t x) (w x) hx
  have hm : AEStronglyMeasurable (fun x =>
      (infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) / δ) ^ 2) μ :=
    (((continuous_infDist_pt _).div_const δ).pow 2).aestronglyMeasurable
  have hi' := hi.mono' hm (hb.mono fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg
      (infDist x (affineGraphPlane a L N b A δ : Set (Ambient d)) / δ))]
    exact hx)
  exact ⟨hi', integral_mono_ae hi' hi hb⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_AffinePlaneCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Affine plane coordinates

A linear isometric embedding determines an affine plane parametrization and an
adjoint coordinate map. These maps are Lipschitz and recover every parameter on
the plane; their composition also gives a Lipschitz distance-to-plane function.
-/

namespace RieszRectifiability

noncomputable section

open Function WithLp
open scoped NNReal ENNReal

theorem affinePlaneSection_lipschitz {n d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    LipschitzWith ((Fintype.card (Fin n) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal)
      (affinePlaneSection a L) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [affinePlaneSection, dist_add_left, L.dist_map]
  exact (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)).dist_le_mul x y

theorem affinePlaneCoordinates_lipschitz {n d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    LipschitzWith ‖L.toContinuousLinearMap.adjoint‖₊ (affinePlaneCoordinates a L) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => ℝ)).dist_le_mul
    (L.toContinuousLinearMap.adjoint (x - a)) (L.toContinuousLinearMap.adjoint (y - a))
  simp only [NNReal.coe_one, one_mul] at h
  exact h.trans (by simpa only [dist_sub_right] using!
    L.toContinuousLinearMap.adjoint.lipschitz.dist_le_mul (x - a) (y - a))

theorem affinePlaneCoordinates_leftInverse {n d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    LeftInverse (affinePlaneCoordinates a L) (affinePlaneSection a L) := by
  intro u
  have h : L.toContinuousLinearMap.adjoint (L (toLp 2 u)) = toLp 2 u := by
    exact DFunLike.congr_fun L.adjoint_comp_self (toLp 2 u)
  change ofLp (L.toContinuousLinearMap.adjoint ((a + L (toLp 2 u)) - a)) = u
  rw [add_sub_cancel_left, h]

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

theorem coordinatePlaneMeasure_finite_on_compacts {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (he : Measurable e) (Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e) :
    IsFiniteMeasureOnCompacts (coordinatePlaneMeasure e) :=
  (coordinatePlaneMeasure_upper_growth e π he Q hπ hleft).finite_on_compacts

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_MomentRepair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem integral_squared_difference (μ : Measure X) (w v : X → ℝ)
    (hww : Integrable (fun x => w x ^ 2) μ)
    (hwv : Integrable (fun x => w x * v x) μ)
    (hvv : Integrable (fun x => v x ^ 2) μ) :
    (∫ x, (w x - v x) ^ 2 ∂μ) =
      (∫ x, w x ^ 2 ∂μ) - 2 * (∫ x, w x * v x ∂μ) + (∫ x, v x ^ 2 ∂μ) := by
  have h : (fun x => (w x - v x) ^ 2) =
      (fun x => w x ^ 2 - 2 * (w x * v x) + v x ^ 2) := by
    funext x
    ring
  have hadd := integral_add (hww.sub (hwv.const_mul 2)) hvv
  have hsub := integral_sub hww (hwv.const_mul 2)
  simp only [Pi.sub_apply] at hadd hsub
  rw [h, hadd, hsub, integral_const_mul]

theorem squared_error_tendsto_zero_of_moments
    (μ : ℕ → Measure X) (w : ℕ → X → ℝ) (v : X → ℝ) (a : ℝ)
    (hww : ∀ j, Integrable (fun x => w j x ^ 2) (μ j))
    (hwv : ∀ j, Integrable (fun x => w j x * v x) (μ j))
    (hvv : ∀ j, Integrable (fun x => v x ^ 2) (μ j))
    (lim_ww : Tendsto (fun j => ∫ x, w j x ^ 2 ∂μ j) atTop (𝓝 a))
    (lim_wv : Tendsto (fun j => ∫ x, w j x * v x ∂μ j) atTop (𝓝 a))
    (lim_vv : Tendsto (fun j => ∫ x, v x ^ 2 ∂μ j) atTop (𝓝 a)) :
    Tendsto (fun j => ∫ x, (w j x - v x) ^ 2 ∂μ j) atTop (𝓝 0) := by
  have hfun : (fun j => ∫ x, (w j x - v x) ^ 2 ∂μ j) =
      (fun j => (∫ x, w j x ^ 2 ∂μ j) -
        2 * (∫ x, w j x * v x ∂μ j) + (∫ x, v x ^ 2 ∂μ j)) := by
    funext j
    exact integral_squared_difference (μ j) (w j) v (hww j) (hwv j) (hvv j)
  rw [hfun]
  have h := (lim_ww.sub (lim_wv.const_mul 2)).add lim_vv
  simpa only [show a - 2 * a + a = 0 by ring] using! h

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

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_AmbientAffineHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ambient extensions of affine plane heights

The adjoint of a linear isometric embedding extends an affine height from plane
coordinates to the ambient space. Its operator norms give a Lipschitz bound,
and the pullback identity transfers almost-everywhere affine agreement to the
coordinate plane measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal

theorem ambientAffineHeight_lipschitz {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (c : ℝ) (M : Ambient n →L[ℝ] ℝ) :
    LipschitzWith (‖M‖₊ * ‖L.toContinuousLinearMap.adjoint‖₊) (ambientAffineHeight a L c M) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [ambientAffineHeight, dist_add_left, NNReal.coe_mul, coe_nnnorm]
  calc
    _ ≤ ‖M‖ * dist (L.toContinuousLinearMap.adjoint (x - a))
        (L.toContinuousLinearMap.adjoint (y - a)) := M.lipschitz.dist_le_mul _ _
    _ ≤ ‖M‖ * (‖L.toContinuousLinearMap.adjoint‖ * dist (x - a) (y - a)) :=
      mul_le_mul_of_nonneg_left (L.toContinuousLinearMap.adjoint.lipschitz.dist_le_mul _ _)
        (norm_nonneg _)
    _ = _ := by rw [dist_sub_right]; ring

theorem ambientAffineHeight_pullback {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (c : ℝ) (M : Ambient n →L[ℝ] ℝ) (x : Ambient n) :
    ambientAffineHeight a L c M (a + L x) = c + M x := by
  have h : L.toContinuousLinearMap.adjoint (L x) = x :=
    DFunLike.congr_fun L.adjoint_comp_self x
  simp only [ambientAffineHeight, add_sub_cancel_left, h]

theorem height_ae_eq_ambient_affine {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ) (hfm : Measurable f)
    (c : ℝ) (M : Ambient n →L[ℝ] ℝ)
    (hf : ∀ᵐ x, f (a + L x) = c + M x) :
    f =ᵐ[coordinatePlaneMeasure (affinePlaneSection a L)] ambientAffineHeight a L c M := by
  rw [coordinatePlaneMeasure_affine_eq_map]
  have he : Measurable (fun x : Ambient n => a + L x) := by fun_prop
  have hm : MeasurableSet {x | f x = ambientAffineHeight a L c M x} :=
    measurableSet_eq_fun hfm (ambientAffineHeight_lipschitz a L c M).continuous.measurable
  apply (ae_map_iff he.aemeasurable hm).mpr
  filter_upwards [hf] with x hx
  simpa only [ambientAffineHeight_pullback] using! hx

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_AssembledAffineHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Assembling affine height coordinates

Coordinatewise continuous linear maps assemble into a Euclidean-valued map. Their affine
extensions give an ambient vector-valued affine map, whose Lipschitz constant is bounded by the
operator norm of its linear part.
-/

namespace RieszRectifiability

noncomputable section

open WithLp
open scoped NNReal

theorem exists_ambient_vector_affine {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (c : Fin q → ℝ) (M : Fin q → Ambient n →L[ℝ] ℝ) :
    ∃ b : Ambient q, ∃ B : Ambient d →L[ℝ] Ambient q, ∀ x i,
      (b + B x) i = ambientAffineHeight a L (c i) (M i) x := by
  refine ⟨toLp 2 c - assembleCoordinateLinear M (L.toContinuousLinearMap.adjoint a),
    (assembleCoordinateLinear M).comp L.toContinuousLinearMap.adjoint, ?_⟩
  intro x i
  change c i - M i (L.toContinuousLinearMap.adjoint a) +
    M i (L.toContinuousLinearMap.adjoint x) =
      c i + M i (L.toContinuousLinearMap.adjoint (x - a))
  rw [map_sub, map_sub]
  ring

theorem vectorAffine_lipschitz {d q : ℕ} (b : Ambient q) (B : Ambient d →L[ℝ] Ambient q) :
    LipschitzWith ‖B‖₊ (fun x => b + B x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_add_left, coe_nnnorm] using! B.lipschitz.dist_le_mul x y

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

theorem exhaustionBox_dist_zero_le {ι : Type*} [Fintype ι] (H : ℕ) (u : ι → ℝ)
    (hu : u ∈ exhaustionBox ι H) : dist u 0 ≤ (H : ℝ) + 1 := by
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ H + 1)).mpr
  intro i
  have hi := hu i
  change -((H : ℝ) + 1) < u i ∧ u i ≤ (H : ℝ) + 1 at hi
  simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using! abs_le.mpr ⟨hi.1.le, hi.2⟩

theorem mem_exhaustionBox_Ioo_of_norm_lt {ι : Type*} [Fintype ι]
    (H : ℕ) (u : ι → ℝ) (hu : ‖u‖ < (H : ℝ) + 1) : u ∈ Box.Ioo (exhaustionBox ι H) := by
  intro i _
  change -((H : ℝ) + 1) < u i ∧ u i < (H : ℝ) + 1
  apply abs_lt.mp
  exact (show |u i| ≤ ‖u‖ by simpa only [Real.norm_eq_abs] using! norm_le_pi_norm u i).trans_lt hu

theorem planeBoxOuterRadius_pos (K : ℝ≥0) (H : ℕ) : 0 < planeBoxOuterRadius K H := by
  unfold planeBoxOuterRadius
  positivity

theorem exhaustionBox_image_mem_outerBall {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (K : ℝ≥0) (he : LipschitzWith K e)
    (H : ℕ) (u : ι → ℝ) (hu : u ∈ exhaustionBox ι H) :
    e u ∈ ball (e 0) (planeBoxOuterRadius K H) := by
  apply mem_ball.mpr
  have hdist := (he.dist_le_mul u 0).trans
    (mul_le_mul_of_nonneg_left (exhaustionBox_dist_zero_le H u hu) K.coe_nonneg)
  dsimp [planeBoxOuterRadius]
  nlinarith

theorem boundedProjectionRegion_isOpen {ι : Type*} [Fintype ι] {d : ℕ}
    (π : Ambient d → ι → ℝ) (hπ : Continuous π) (a : Ambient d) (K : ℝ≥0) (H : ℕ) :
    IsOpen (boundedProjectionRegion π a K H) :=
  (openProjectionBox_isOpen (exhaustionBox ι H) π hπ).inter isOpen_ball

theorem coordinatePlaneMeasure_restrict_boundedRegion {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K : ℝ≥0) (he : LipschitzWith K e) (hπ : Continuous π) (hleft : LeftInverse π e) (H : ℕ) :
    (coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H) =
      boxPlaneMeasure (exhaustionBox ι H) e := by
  have hpre : e ⁻¹' boundedProjectionRegion π (e 0) K H = Box.Ioo (exhaustionBox ι H) := by
    ext u
    change (π (e u) ∈ Box.Ioo (exhaustionBox ι H) ∧
      e u ∈ ball (e 0) (planeBoxOuterRadius K H)) ↔ u ∈ Box.Ioo (exhaustionBox ι H)
    rw [hleft u]
    exact ⟨And.left, fun hu => ⟨hu, exhaustionBox_image_mem_outerBall e K he H u
      ((exhaustionBox ι H).Ioo_subset_coe hu)⟩⟩
  rw [coordinatePlaneMeasure, Measure.restrict_map he.continuous.measurable
    (boundedProjectionRegion_isOpen π hπ (e 0) K H).measurableSet, hpre,
    Measure.restrict_congr_set ((exhaustionBox ι H).Ioo_ae_eq_Icc.trans
      (exhaustionBox ι H).coe_ae_eq_Icc.symm)]
  rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BoundedBoxBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Null boundaries of coordinate boxes

The frontier of an open coordinate box lies in the difference between its
closed and open versions. Their almost-everywhere equality for volume shows
that this frontier has measure zero.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem box_Ioo_frontier_volume_zero {ι : Type*} [Fintype ι] (I : Box ι) :
    (volume : Measure (ι → ℝ)) (frontier (Box.Ioo I)) = 0 := by
  have hopen : IsOpen (Box.Ioo I) := isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hsub : frontier (Box.Ioo I) ⊆ Box.Icc I \ Box.Ioo I := by
    rw [hopen.frontier_eq]
    exact sdiff_subset_sdiff_left (closure_minimal I.Ioo_subset_Icc I.isCompact_Icc.isClosed)
  have heq : (Box.Icc I \ Box.Ioo I) =ᵐ[volume] (∅ : Set (ι → ℝ)) := by
    filter_upwards [I.Ioo_ae_eq_Icc] with x hx
    apply propext
    change (x ∈ Box.Icc I ∧ x ∉ Box.Ioo I) ↔ False
    have hx' : x ∈ Box.Ioo I ↔ x ∈ Box.Icc I := iff_of_eq hx
    tauto
  exact measure_mono_null hsub ((measure_congr heq).trans measure_empty)

theorem exhaustionBox_Icc_dist_zero_le {ι : Type*} [Fintype ι] (H : ℕ) (u : ι → ℝ)
    (hu : u ∈ Box.Icc (exhaustionBox ι H)) : dist u 0 ≤ (H : ℝ) + 1 := by
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ H + 1)).mpr
  intro i
  have hi : -((H : ℝ) + 1) ≤ u i ∧ u i ≤ (H : ℝ) + 1 := ⟨hu.1 i, hu.2 i⟩
  simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using! abs_le.mpr hi

theorem exhaustionBox_Icc_image_mem_outerBall {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (K : ℝ≥0) (he : LipschitzWith K e)
    (H : ℕ) (u : ι → ℝ) (hu : u ∈ Box.Icc (exhaustionBox ι H)) :
    e u ∈ ball (e 0) (planeBoxOuterRadius K H) := by
  apply mem_ball.mpr
  have hdist := (he.dist_le_mul u 0).trans
    (mul_le_mul_of_nonneg_left (exhaustionBox_Icc_dist_zero_le H u hu) K.coe_nonneg)
  dsimp [planeBoxOuterRadius]
  nlinarith

theorem boundedProjectionRegion_preimage_frontier_subset {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K : ℝ≥0) (he : LipschitzWith K e) (hπ : Continuous π) (hleft : LeftInverse π e) (H : ℕ) :
    e ⁻¹' frontier (boundedProjectionRegion π (e 0) K H) ⊆
      frontier (Box.Ioo (exhaustionBox ι H)) := by
  intro u hu
  have hsplit := frontier_inter_subset (openProjectionBox (exhaustionBox ι H) π)
    (ball (e 0) (planeBoxOuterRadius K H)) hu
  rcases hsplit with hA | hB
  · have h := hπ.frontier_preimage_subset (Box.Ioo (exhaustionBox ι H)) hA.1
    simpa only [mem_preimage, hleft u] using! h
  · have hclos : closure (openProjectionBox (exhaustionBox ι H) π) ⊆
        π ⁻¹' Box.Icc (exhaustionBox ι H) :=
      closure_minimal (fun _ hx => (exhaustionBox ι H).Ioo_subset_Icc hx)
        ((exhaustionBox ι H).isCompact_Icc.isClosed.preimage hπ)
    have hucc : u ∈ Box.Icc (exhaustionBox ι H) := by
      simpa only [mem_preimage, hleft u] using! hclos hB.1
    have hin := exhaustionBox_Icc_image_mem_outerBall e K he H u hucc
    have hout := hB.2
    rw [isOpen_ball.frontier_eq] at hout
    exact False.elim (hout.2 hin)

theorem boundedProjectionRegion_null_frontier {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K : ℝ≥0) (he : LipschitzWith K e) (hπ : Continuous π) (hleft : LeftInverse π e) (H : ℕ) :
    coordinatePlaneMeasure e (frontier (boundedProjectionRegion π (e 0) K H)) = 0 := by
  rw [coordinatePlaneMeasure, Measure.map_apply he.continuous.measurable isClosed_frontier.measurableSet]
  exact measure_mono_null (boundedProjectionRegion_preimage_frontier_subset e π K he hπ hleft H)
    (box_Ioo_frontier_volume_zero (exhaustionBox ι H))

theorem boundedProjectionRegion_compact_closure {ι : Type*} {d : ℕ}
    (π : Ambient d → ι → ℝ) (a : Ambient d) (K : ℝ≥0) (H : ℕ) :
    IsCompact (closure (boundedProjectionRegion π a K H)) := by
  apply (isCompact_closedBall a (planeBoxOuterRadius K H)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  exact fun _ hx => mem_closedBall.mpr hx.2.le

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_BoundedBoxConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Compact-test convergence to a coordinate-plane measure yields weak convergence of finite measures
on bounded projection regions, using compact closures and null frontiers.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem boundedProjectionFiniteMeasure_tendsto {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (hlocal : CompactTestConvergence μ (coordinatePlaneMeasure e)) (H : ℕ) :
    Tendsto (fun j => boundedProjectionFiniteMeasure (μ j) π (e 0) K H) atTop
      (𝓝 (boxPlaneFiniteMeasure (exhaustionBox ι H) e)) := by
  let : IsFiniteMeasureOnCompacts (coordinatePlaneMeasure e) :=
    coordinatePlaneMeasure_finite_on_compacts e π he.continuous.measurable Q hπ hleft
  let s := boundedProjectionRegion π (e 0) K H
  have hs : MeasurableSet s := (boundedProjectionRegion_isOpen π hπ.continuous (e 0) K H).measurableSet
  have hc : IsCompact (closure s) := boundedProjectionRegion_compact_closure π (e 0) K H
  have h := compactTestConvergence_restrict_tendsto μ (coordinatePlaneMeasure e) hlocal s hs hc
    (boundedProjectionRegion_null_frontier e π K he hπ.continuous hleft H)
  have heq : relativelyCompactFiniteMeasure (coordinatePlaneMeasure e) s hc =
      boxPlaneFiniteMeasure (exhaustionBox ι H) e := by
    apply Subtype.ext
    exact coordinatePlaneMeasure_restrict_boundedRegion e π K he hπ.continuous hleft H
  rw [heq] at h
  exact h

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

theorem exists_boundedProjectionRegion_containing_ball {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e) (R : ℝ) :
    ∃ H : ℕ, ball (e 0) R ⊆ boundedProjectionRegion π (e 0) K H := by
  obtain ⟨H, hH⟩ := exists_nat_gt (((Q : ℝ) + 1) * R)
  have hden : 0 < (Q : ℝ) + 1 := by positivity
  have hR : R ≤ planeBoxInnerRadius Q H := by
    unfold planeBoxInnerRadius
    apply (le_div_iff₀ hden).mpr
    nlinarith
  exact ⟨H, (ball_subset_ball hR).trans (ball_subset_boundedProjectionRegion e π K Q hπ hleft H)⟩

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_EuclideanCoordinateMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Euclidean second moments from coordinate moments

The squared Euclidean norm is a finite sum of squared coordinates. This identity
transfers coordinatewise integrability, integral formulas, and convergence of
second moments to their Euclidean counterparts, including varying measures.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

theorem integrable_euclidean_norm_sq_of_coordinates {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (w : X → Ambient q)
    (hi : ∀ i : Fin q, Integrable (fun x => (w x i) ^ 2) μ) :
    Integrable (fun x => ‖w x‖ ^ 2) μ := by
  simpa only [EuclideanSpace.real_norm_sq_eq] using!
    integrable_finsetSum Finset.univ (fun i _ => hi i)

theorem integral_euclidean_norm_sq_eq_sum {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (w : X → Ambient q)
    (hi : ∀ i : Fin q, Integrable (fun x => (w x i) ^ 2) μ) :
    (∫ x, ‖w x‖ ^ 2 ∂μ) = ∑ i : Fin q, ∫ x, (w x i) ^ 2 ∂μ := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  exact integral_finsetSum Finset.univ (fun i _ => hi i)

theorem euclidean_norm_sq_tendsto_zero_of_coordinates
    {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : ℕ → Measure X) (w : ℕ → X → Ambient q)
    (hi : ∀ j i, Integrable (fun x => (w j x i) ^ 2) (μ j))
    (hlim : ∀ i : Fin q,
      Tendsto (fun j => ∫ x, (w j x i) ^ 2 ∂μ j) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, ‖w j x‖ ^ 2 ∂μ j) atTop (𝓝 0) := by
  simp_rw [integral_euclidean_norm_sq_eq_sum _ _ (hi _)]
  simpa only [Finset.sum_const_zero] using!
    tendsto_finsetSum Finset.univ (fun i _ => hlim i)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalizedNormalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric

theorem tangentPlaneProjection_continuous {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) : Continuous (tangentPlaneProjection a L) := by
  unfold tangentPlaneProjection
  fun_prop

theorem normalizedNormalHeight_continuous {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (δ : ℝ) : Continuous (normalizedNormalHeight a N δ) := by
  unfold normalizedNormalHeight
  fun_prop

theorem normalizedNormalHeight_reconstruct {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (δ : ℝ) (hδ : δ ≠ 0) (x : Ambient d) :
    δ • N (normalizedNormalHeight a N δ x) = N (N.toContinuousLinearMap.adjoint (x - a)) := by
  rw [normalizedNormalHeight, map_smul, smul_smul, mul_inv_cancel₀ hδ, one_smul]

theorem normal_coordinates_decomposition {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hsplit : ∀ y, L (L.toContinuousLinearMap.adjoint y) + N (N.toContinuousLinearMap.adjoint y) = y)
    (δ : ℝ) (hδ : δ ≠ 0) (x : Ambient d) :
    x - a = L (L.toContinuousLinearMap.adjoint (x - a)) + δ • N (normalizedNormalHeight a N δ x) := by
  rw [normalizedNormalHeight_reconstruct a N δ hδ]
  exact (hsplit (x - a)).symm

theorem physical_projection_distance_eq {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hsplit : ∀ y, L (L.toContinuousLinearMap.adjoint y) + N (N.toContinuousLinearMap.adjoint y) = y)
    (δ : ℝ) (hδ : 0 < δ) (x : Ambient d) :
    dist x (tangentPlaneProjection a L x) = δ * ‖normalizedNormalHeight a N δ x‖ := by
  have h := normal_coordinates_decomposition a L N hsplit δ hδ.ne' x
  have he : x - tangentPlaneProjection a L x = δ • N (normalizedNormalHeight a N δ x) := by
    unfold tangentPlaneProjection
    rw [← sub_sub]
    exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hδ, N.norm_map]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalCoordinateTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open WithLp
open scoped NNReal

theorem normalDirection_norm {q d : ℕ} (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) :
    ‖normalDirection N i‖ = 1 := by
  rw [normalDirection, N.norm_map]
  exact (EuclideanSpace.basisFun (Fin q) ℝ).norm_eq_one i

theorem normalCoordinate_eq_inner {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) (x : Ambient d) :
    normalCoordinate a N i x = inner ℝ (normalDirection N i) (x - a) := by
  calc
    _ = inner ℝ (EuclideanSpace.basisFun (Fin q) ℝ i)
        (N.toContinuousLinearMap.adjoint (x - a)) :=
      (EuclideanSpace.basisFun_inner (Fin q) ℝ (N.toContinuousLinearMap.adjoint (x - a)) i).symm
    _ = _ := N.toContinuousLinearMap.adjoint_inner_right _ _

theorem normalCoordinate_difference {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) (x y : Ambient d) :
    normalCoordinate a N i x - normalCoordinate a N i y = inner ℝ (normalDirection N i) (x - y) := by
  rw [normalCoordinate_eq_inner, normalCoordinate_eq_inner, ← inner_sub_right,
    sub_sub_sub_cancel_right]

theorem normalCoordinate_lipschitz {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) : LipschitzWith 1 (normalCoordinate a N i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, normalCoordinate_difference, dist_eq_norm]
  have h := abs_real_inner_le_norm (normalDirection N i) (x - y)
  simpa only [normalDirection_norm, one_mul] using! h

theorem normalCoordinate_normalized_vector {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (δ : ℝ) (x : Ambient d) :
    toLp 2 (fun i => normalCoordinate a N i x / δ) = normalizedNormalHeight a N δ x := by
  ext i
  change (N.toContinuousLinearMap.adjoint (x - a) i) / δ =
    δ⁻¹ * (N.toContinuousLinearMap.adjoint (x - a) i)
  rw [div_eq_mul_inv, mul_comm]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalCoordinateMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory

theorem normalizedNormalHeight_second_moment_bound {q d : ℕ}
    (μ : Measure (Ambient d)) (a : Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d) (δ : ℝ)
    (hw : ∀ i, MemLp (fun x => normalCoordinate a N i x / δ) 2 μ)
    (C : ℝ) (hC : ∀ i, (∫ x, (normalCoordinate a N i x / δ) ^ 2 ∂μ) ≤ C) :
    Integrable (fun x => ‖normalizedNormalHeight a N δ x‖ ^ 2) μ ∧
      (∫ x, ‖normalizedNormalHeight a N δ x‖ ^ 2 ∂μ) ≤ (q : ℝ) * C := by
  have heq : ∀ x i, normalizedNormalHeight a N δ x i = normalCoordinate a N i x / δ := by
    intro x i
    exact congrArg (fun v : Ambient q => v i) (normalCoordinate_normalized_vector a N δ x).symm
  have hi : ∀ i, Integrable (fun x => (normalizedNormalHeight a N δ x i) ^ 2) μ := by
    intro i
    simpa only [heq] using! (hw i).integrable_sq
  refine ⟨integrable_euclidean_norm_sq_of_coordinates μ (normalizedNormalHeight a N δ) hi, ?_⟩
  rw [integral_euclidean_norm_sq_eq_sum μ (normalizedNormalHeight a N δ) hi]
  calc
    _ ≤ ∑ _i : Fin q, C := by
      apply Finset.sum_le_sum
      intro i _hi
      simpa only [heq] using! hC i
    _ = _ := by simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LocalizedNormalTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem lipschitz_product_of_bound_on_support {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℝ) (Kf Kg Bf Bg : ℝ≥0) (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, |f x| ≤ (Bf : ℝ)) (hBg : ∀ x, f x ≠ 0 → |g x| ≤ (Bg : ℝ)) :
    LipschitzWith (Bf * Kg + Kf * Bg) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hf' : |f x - f y| ≤ (Kf : ℝ) * dist x y := by simpa only [Real.dist_eq] using! hf.dist_le_mul x y
  have hg' : |g x - g y| ≤ (Kg : ℝ) * dist x y := by simpa only [Real.dist_eq] using! hg.dist_le_mul x y
  by_cases hy : f y = 0
  · by_cases hx : f x = 0
    · simp only [hx, hy, zero_mul, dist_self]
      positivity
    · calc
        dist (f x * g x) (f y * g y) = |f x - f y| * |g x| := by
          simp only [hy, zero_mul, Real.dist_eq, sub_zero, abs_mul]
        _ ≤ ((Kf : ℝ) * dist x y) * (Bg : ℝ) :=
          mul_le_mul hf' (hBg x hx) (abs_nonneg _) (by positivity)
        _ ≤ ((Bf * Kg + Kf * Bg : ℝ≥0) : ℝ) * dist x y := by
          simp only [NNReal.coe_add, NNReal.coe_mul]
          nlinarith [mul_nonneg (mul_nonneg Bf.coe_nonneg Kg.coe_nonneg) (dist_nonneg (x := x) (y := y))]
  · calc
      dist (f x * g x) (f y * g y) = |f x * (g x - g y) + (f x - f y) * g y| := by
        rw [Real.dist_eq]
        congr 1
        ring
      _ ≤ |f x| * |g x - g y| + |f x - f y| * |g y| := by
        simpa only [abs_mul] using! abs_add_le (f x * (g x - g y)) ((f x - f y) * g y)
      _ ≤ (Bf : ℝ) * ((Kg : ℝ) * dist x y) + ((Kf : ℝ) * dist x y) * (Bg : ℝ) :=
        add_le_add (mul_le_mul (hBf x) hg' (abs_nonneg _) (by positivity))
          (mul_le_mul hf' (hBg y hy) (abs_nonneg _) (by positivity))
      _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul] <;> ring

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

theorem exists_compact_lipschitz_test_on_ball {d : ℕ} (a : Ambient d) (R : ℝ)
    (ψ : Ambient d → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ) :
    ∃ (g : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport g ∧ LipschitzWith K g ∧
      (∀ x, |g x| ≤ (B : ℝ)) ∧ ∀ x ∈ ball a R, g x = ψ x := by
  let χ := radialUnitCutoff a R
  let B : ℝ≥0 := Real.toNNReal ((L : ℝ) * (R + 1) + |ψ a|)
  have hχ : LipschitzWith 1 χ := radialUnitCutoff_lipschitz a R
  have hχB : ∀ x, |χ x| ≤ (1 : ℝ≥0) := by
    intro x
    change |radialUnitCutoff a R x| ≤ 1
    rw [abs_of_nonneg (radialUnitCutoff_bounds a R x).1]
    exact (radialUnitCutoff_bounds a R x).2
  have hB : ∀ x, χ x ≠ 0 → |ψ x| ≤ (B : ℝ) := by
    intro x hx
    have hdist : dist x a ≤ R + 1 := radialUnitCutoff_support_bound a R x hx
    have hdiff : |ψ x - ψ a| ≤ (L : ℝ) * dist x a := by
      simpa only [Real.dist_eq] using! hψ.dist_le_mul x a
    calc
      |ψ x| ≤ |ψ x - ψ a| + |ψ a| := by simpa only [sub_add_cancel] using! abs_add_le (ψ x - ψ a) (ψ a)
      _ ≤ (L : ℝ) * (R + 1) + |ψ a| :=
        add_le_add (hdiff.trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)) le_rfl
      _ ≤ (B : ℝ) := Real.le_coe_toNNReal _
  refine ⟨fun x => χ x * ψ x, 1 * L + 1 * B, B,
    (radialUnitCutoff_hasCompactSupport a R).mul_right,
    lipschitz_product_of_bound_on_support χ ψ 1 L 1 B hχ hψ hχB hB, ?_, ?_⟩
  · intro x
    by_cases hx : χ x = 0
    · simp only [hx, zero_mul, abs_zero]
      exact B.coe_nonneg
    · calc
        |χ x * ψ x| = |χ x| * |ψ x| := abs_mul _ _
        _ ≤ 1 * (B : ℝ) := mul_le_mul (hχB x) (hB x hx) (abs_nonneg _) (by norm_num)
        _ = _ := one_mul _
  · intro x hx
    change χ x * ψ x = ψ x
    rw [show χ x = 1 from radialUnitCutoff_eq_one a R x hx.le, one_mul]

theorem compact_moments_extend_on_ball {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (a : Ambient d) (R : ℝ)
    (hμ : ∀ j, ∀ᵐ x ∂μ j, x ∈ ball a R) (hν : ∀ᵐ x ∂ν, x ∈ ball a R)
    (w : ℕ → Ambient d → ℝ) (v : Ambient d → ℝ)
    (hmoment : ∀ (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop (𝓝 (∫ x, v x * ψ x ∂ν))) :
    ∀ (ψ : Ambient d → ℝ) (L : ℝ≥0), LipschitzWith L ψ →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop (𝓝 (∫ x, v x * ψ x ∂ν)) := by
  intro ψ L hψ
  obtain ⟨g, K, B, hgc, hgLip, hgB, heq⟩ := exists_compact_lipschitz_test_on_ball a R ψ L hψ
  have hm : ∀ j, (∫ x, w j x * g x ∂μ j) = ∫ x, w j x * ψ x ∂μ j := by
    intro j
    apply integral_congr_ae
    filter_upwards [hμ j] with x hx
    rw [heq x hx]
  have hn : (∫ x, v x * g x ∂ν) = ∫ x, v x * ψ x ∂ν := by
    apply integral_congr_ae
    filter_upwards [hν] with x hx
    rw [heq x hx]
  simpa only [hm, hn] using! hmoment g K B hgc hgLip hgB

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_LipschitzSquareWeakLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal BoundedContinuousFunction

theorem lipschitz_memLp_of_ae_ball {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ]
    (a : Ambient d) (R : ℝ) (hμ : ∀ᵐ x ∂μ, x ∈ ball a R)
    (v : Ambient d → ℝ) (L : ℝ≥0) (hv : LipschitzWith L v) :
    MemLp v 2 μ := by
  obtain ⟨g, K, B, _, hg, hB, heq⟩ := exists_compact_lipschitz_test_on_ball a R v L hv
  have hgm : MemLp g 2 μ := MemLp.of_bound hg.continuous.aestronglyMeasurable (B : ℝ)
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hB x)
  apply hgm.ae_eq
  filter_upwards [hμ] with x hx
  exact heq x hx

theorem lipschitz_square_integral_tendsto_of_ae_ball {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (a : Ambient d) (R : ℝ)
    (hμ : ∀ j, ∀ᵐ x ∂(μ j : Measure (Ambient d)), x ∈ ball a R)
    (hν : ∀ᵐ x ∂(ν : Measure (Ambient d)), x ∈ ball a R)
    (v : Ambient d → ℝ) (L : ℝ≥0) (hv : LipschitzWith L v) :
    Tendsto (fun j => ∫ x, v x ^ 2 ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x, v x ^ 2 ∂(ν : Measure (Ambient d)))) := by
  obtain ⟨g, K, B, _, hg, hB, heq⟩ := exists_compact_lipschitz_test_on_ball a R v L hv
  let G : Ambient d →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    g hg.continuous (B : ℝ) (fun x => by simpa only [Real.norm_eq_abs] using! hB x)
  have hm : ∀ j, (∫ x, (G * G) x ∂(μ j : Measure (Ambient d))) =
      ∫ x, v x ^ 2 ∂(μ j : Measure (Ambient d)) := by
    intro j
    apply integral_congr_ae
    filter_upwards [hμ j] with x hx
    change g x * g x = v x ^ 2
    rw [heq x hx, pow_two]
  have hn : (∫ x, (G * G) x ∂(ν : Measure (Ambient d))) =
      ∫ x, v x ^ 2 ∂(ν : Measure (Ambient d)) := by
    apply integral_congr_ae
    filter_upwards [hν] with x hx
    change g x * g x = v x ^ 2
    rw [heq x hx, pow_two]
  simpa only [hm, hn] using!
    FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (G * G)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_FiniteAffineVectorLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vector-valued affine strong limits

Coordinatewise affine limits assemble into one ambient affine map. On bounded projection
regions, coordinate square integrability and convergence combine through the Euclidean norm
identity to give vector-valued strong convergence.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Topology WithLp
open scoped NNReal

theorem exists_vector_affine_strong_limit_of_coordinates {n q d : ℕ}
    (a z : Ambient d) (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (π : Ambient d → Fin n → ℝ) (K Q : ℝ≥0) (hπ : LipschitzWith Q π)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)]
    (w : Fin q → ℕ → Ambient d → ℝ)
    (hw : ∀ i H j, MemLp (w i j) 2 ((σ j).restrict (boundedProjectionRegion π z K H)))
    (c : Fin q → ℝ) (M : Fin q → Ambient n →L[ℝ] ℝ)
    (hstrong : ∀ i H, Tendsto (fun j => ∫ x,
      (w i j x - ambientAffineHeight a L (c i) (M i) x) ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π z K H)) atTop (𝓝 0)) :
    ∃ b : Ambient q, ∃ B : Ambient d →L[ℝ] Ambient q, ∀ H,
      (∀ j, Integrable (fun x => ‖toLp 2 (fun i => w i j x) - (b + B x)‖ ^ 2)
        ((σ j).restrict (boundedProjectionRegion π z K H))) ∧
      Tendsto (fun j => ∫ x, ‖toLp 2 (fun i => w i j x) - (b + B x)‖ ^ 2
        ∂(σ j).restrict (boundedProjectionRegion π z K H)) atTop (𝓝 0) := by
  obtain ⟨b, B, hcoord⟩ := exists_ambient_vector_affine a L c M
  refine ⟨b, B, ?_⟩
  intro H
  let μ := fun j => (σ j).restrict (boundedProjectionRegion π z K H)
  let r := fun j x => (toLp 2 (fun i => w i j x) : Ambient q) - (b + B x)
  have hr : ∀ j x i, r j x i = w i j x - ambientAffineHeight a L (c i) (M i) x := by
    intro j x i
    change w i j x - (b + B x) i = _
    rw [hcoord]
  have hi : ∀ j i, Integrable (fun x => (r j x i) ^ 2) (μ j) := by
    intro j i
    let := boundedProjectionRegion_finite (σ j) π z K H
    have hball : ∀ᵐ x ∂μ j, x ∈ ball z (planeBoxOuterRadius K H) := by
      filter_upwards [ae_restrict_mem (μ := σ j)
        (boundedProjectionRegion_isOpen π hπ.continuous z K H).measurableSet] with x hx
      exact hx.2
    have hv := lipschitz_memLp_of_ae_ball (μ j) z (planeBoxOuterRadius K H) hball
      (ambientAffineHeight a L (c i) (M i)) _ (ambientAffineHeight_lipschitz a L (c i) (M i))
    simpa only [hr] using! ((hw i H j).sub hv).integrable_sq
  refine ⟨fun j => integrable_euclidean_norm_sq_of_coordinates (μ j) (r j) (hi j), ?_⟩
  apply euclidean_norm_sq_tendsto_zero_of_coordinates μ r hi
  intro i
  simpa only [hr] using! hstrong i H

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

theorem squaredExcess_nonneg {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r) : 0 ≤ squaredExcess n μ a r := by
  apply Real.sInf_nonneg
  rintro t ⟨S, _hS, rfl⟩
  exact quadraticPlaneError_nonneg n μ a r hr S

theorem squaredExcess_le_planeError {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) :
    squaredExcess n μ a r ≤ quadraticPlaneError n μ a r S := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨T, _hT, rfl⟩
    exact quadraticPlaneError_nonneg n μ a r hr T
  · exact ⟨S, hS, rfl⟩

theorem squaredExcess_div_sq_le {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) (δ : ℝ) :
    squaredExcess n μ a r / δ ^ 2 ≤ (r ^ (n + 2))⁻¹ *
      ∫ x in ball a r, (infDist x (S : Set (Ambient d)) / δ) ^ 2 ∂μ := by
  calc
    _ ≤ quadraticPlaneError n μ a r S / δ ^ 2 :=
      div_le_div_of_nonneg_right (squaredExcess_le_planeError n μ a r hr S hS) (sq_nonneg δ)
    _ = _ := by
      simp only [quadraticPlaneError, div_pow, integral_div]
      ring

theorem squaredExcess_ratio_tendsto_zero_of_planes {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (a : Ambient d) (r : ℝ) (hr : 0 ≤ r)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane n (S j))
    (δ : ℕ → ℝ)
    (hlim : Tendsto (fun j => ∫ x in ball a r,
      (infDist x (S j : Set (Ambient d)) / δ j) ^ 2 ∂μ j) atTop (𝓝 0)) :
    Tendsto (fun j => squaredExcess n (μ j) a r / δ j ^ 2) atTop (𝓝 0) := by
  have hlim' := hlim.const_mul ((r ^ (n + 2))⁻¹)
  simp only [mul_zero] at hlim'
  exact squeeze_zero (fun j => div_nonneg (squaredExcess_nonneg n (μ j) a r hr) (sq_nonneg _))
    (fun j => squaredExcess_div_sq_le n (μ j) a r hr (S j) (hS j) (δ j)) hlim'

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LipschitzRetractionError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped NNReal

theorem lipschitz_retraction_error_integral_bound {d q k : ℕ}
    (μ : Measure (Ambient d)) (v : Ambient d → Ambient q) (J : ℝ≥0)
    (hv : LipschitzWith J v) (P : Ambient d → Ambient d) (hP : Measurable P)
    (δ : ℝ) (hδ : 0 ≤ δ) (r : Ambient d → Ambient k)
    (hr : Integrable (fun x => ‖r x‖ ^ 2) μ)
    (hbound : ∀ᵐ x ∂μ, dist x (P x) ≤ δ * ‖r x‖) :
    Integrable (fun x => ‖v x - v (P x)‖ ^ 2) μ ∧
      (∫ x, ‖v x - v (P x)‖ ^ 2 ∂μ) ≤ ((J : ℝ) * δ) ^ 2 * (∫ x, ‖r x‖ ^ 2 ∂μ) := by
  have hb : ∀ᵐ x ∂μ, ‖v x - v (P x)‖ ^ 2 ≤ ((J : ℝ) * δ) ^ 2 * ‖r x‖ ^ 2 := by
    filter_upwards [hbound] with x hx
    have hn : ‖v x - v (P x)‖ ≤ ((J : ℝ) * δ) * ‖r x‖ := by
      calc
        _ = dist (v x) (v (P x)) := (dist_eq_norm _ _).symm
        _ ≤ (J : ℝ) * dist x (P x) := hv.dist_le_mul x (P x)
        _ ≤ (J : ℝ) * (δ * ‖r x‖) := mul_le_mul_of_nonneg_left hx J.coe_nonneg
        _ = _ := (mul_assoc _ _ _).symm
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (mul_nonneg J.coe_nonneg hδ) (norm_nonneg _))).mpr hn
    simpa only [mul_pow] using! hs
  have hm : AEStronglyMeasurable (fun x => ‖v x - v (P x)‖ ^ 2) μ :=
    ((hv.continuous.measurable.sub (hv.continuous.measurable.comp hP)).norm.pow_const 2).aestronglyMeasurable
  have hi := (hr.const_mul (((J : ℝ) * δ) ^ 2)).mono' hm (hb.mono fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖v x - v (P x)‖)]
    exact hx)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, ((J : ℝ) * δ) ^ 2 * ‖r x‖ ^ 2 ∂μ :=
      integral_mono_ae hi (hr.const_mul _) hb
    _ = _ := integral_const_mul _ _

theorem lipschitz_retraction_error_tendsto_zero {d q k : ℕ}
    (μ : ℕ → Measure (Ambient d)) (v : Ambient d → Ambient q) (J : ℝ≥0)
    (hv : LipschitzWith J v) (P : ℕ → Ambient d → Ambient d) (hP : ∀ j, Measurable (P j))
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 ≤ δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (r : ℕ → Ambient d → Ambient k) (hr : ∀ j, Integrable (fun x => ‖r j x‖ ^ 2) (μ j))
    (hbound : ∀ j, ∀ᵐ x ∂μ j, dist x (P j x) ≤ δ j * ‖r j x‖)
    (B : ℝ) (hB : ∀ j, (∫ x, ‖r j x‖ ^ 2 ∂μ j) ≤ B) :
    Tendsto (fun j => ∫ x, ‖v x - v (P j x)‖ ^ 2 ∂μ j) atTop (𝓝 0) := by
  have hlim : Tendsto (fun j => ((J : ℝ) * δ j) ^ 2 * B) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] using!
      ((hδlim.const_mul (J : ℝ)).pow 2).mul_const B
  apply squeeze_zero (fun j => integral_nonneg fun x => sq_nonneg ‖v x - v (P j x)‖) _ hlim
  intro j
  exact (lipschitz_retraction_error_integral_bound (μ j) v J hv (P j) (hP j)
    (δ j) (hδ j) (r j) (hr j) (hbound j)).2.trans
    (mul_le_mul_of_nonneg_left (hB j) (sq_nonneg _))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_VectorStrongLimitStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

theorem euclidean_sub_sq_three_point_bound {q : ℕ} (x y z : Ambient q) :
    ‖x - z‖ ^ 2 ≤ 2 * (‖x - y‖ ^ 2 + ‖y - z‖ ^ 2) := by
  have hn := norm_add_le (x - y) (y - z)
  rw [sub_add_sub_cancel] at hn
  have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
  nlinarith [sq_nonneg (‖x - y‖ - ‖y - z‖)]

theorem vector_error_integrable_and_bound {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (w v g : X → Ambient q) (hw : Measurable w) (hg : Measurable g)
    (h₁ : Integrable (fun x => ‖w x - v x‖ ^ 2) μ)
    (h₂ : Integrable (fun x => ‖v x - g x‖ ^ 2) μ) :
    Integrable (fun x => ‖w x - g x‖ ^ 2) μ ∧
      (∫ x, ‖w x - g x‖ ^ 2 ∂μ) ≤
        2 * ((∫ x, ‖w x - v x‖ ^ 2 ∂μ) + (∫ x, ‖v x - g x‖ ^ 2 ∂μ)) := by
  have hb := fun x => euclidean_sub_sq_three_point_bound (w x) (v x) (g x)
  have hi := ((h₁.add h₂).const_mul 2).mono'
    (((hw.sub hg).norm.pow_const 2).aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      simpa only [Pi.sub_apply, Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖w x - g x‖)] using! hb x)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, 2 * (‖w x - v x‖ ^ 2 + ‖v x - g x‖ ^ 2) ∂μ :=
      integral_mono hi ((h₁.add h₂).const_mul 2) hb
    _ = _ := by rw [integral_const_mul, integral_add h₁ h₂]

theorem vector_strong_limit_trans {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : ℕ → Measure X) (w v g : ℕ → X → Ambient q)
    (hw : ∀ j, Measurable (w j)) (hg : ∀ j, Measurable (g j))
    (h₁ : ∀ j, Integrable (fun x => ‖w j x - v j x‖ ^ 2) (μ j))
    (h₂ : ∀ j, Integrable (fun x => ‖v j x - g j x‖ ^ 2) (μ j))
    (hlim₁ : Tendsto (fun j => ∫ x, ‖w j x - v j x‖ ^ 2 ∂μ j) atTop (𝓝 0))
    (hlim₂ : Tendsto (fun j => ∫ x, ‖v j x - g j x‖ ^ 2 ∂μ j) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, ‖w j x - g j x‖ ^ 2 ∂μ j) atTop (𝓝 0) := by
  have hlim : Tendsto (fun j => 2 * ((∫ x, ‖w j x - v j x‖ ^ 2 ∂μ j) +
      (∫ x, ‖v j x - g j x‖ ^ 2 ∂μ j))) atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using! (hlim₁.add hlim₂).const_mul 2
  exact squeeze_zero (fun j => integral_nonneg fun x => sq_nonneg ‖w j x - g j x‖)
    (fun j => (vector_error_integrable_and_bound (μ j) (w j) (v j) (g j)
      (hw j) (hg j) (h₁ j) (h₂ j)).2) hlim

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_MovingAffineGraphLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped NNReal

theorem moving_affine_graph_distance_tendsto_zero {n q d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (a : ℕ → Ambient d)
    (L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d) (N : ℕ → Ambient q →ₗᵢ[ℝ] Ambient d)
    (horth : ∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0)
    (hsplit : ∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
      N j ((N j).toContinuousLinearMap.adjoint y) = y)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (b : Ambient q) (B : Ambient d →L[ℝ] Ambient q)
    (hraw : ∀ j, Integrable (fun x => ‖normalizedNormalHeight (a j) (N j) (δ j) x‖ ^ 2) (μ j))
    (C : ℝ) (hC : ∀ j, (∫ x, ‖normalizedNormalHeight (a j) (N j) (δ j) x‖ ^ 2 ∂μ j) ≤ C)
    (herr : ∀ j, Integrable
      (fun x => ‖normalizedNormalHeight (a j) (N j) (δ j) x - (b + B x)‖ ^ 2) (μ j))
    (hstrong : Tendsto (fun j => ∫ x,
      ‖normalizedNormalHeight (a j) (N j) (δ j) x - (b + B x)‖ ^ 2 ∂μ j) atTop (𝓝 0)) :
    ∃ S : ℕ → AffineSubspace ℝ (Ambient d),
      (∀ j, (S j : Set (Ambient d)).Nonempty ∧ Module.finrank ℝ (S j).direction = n) ∧
      (∀ j, Integrable (fun x => (infDist x (S j : Set (Ambient d)) / δ j) ^ 2) (μ j)) ∧
      Tendsto (fun j => ∫ x, (infDist x (S j : Set (Ambient d)) / δ j) ^ 2 ∂μ j)
        atTop (𝓝 0) := by
  let w := fun j => normalizedNormalHeight (a j) (N j) (δ j)
  let P := fun j => tangentPlaneProjection (a j) (L j)
  let v := fun x => b + B x
  have hwm : ∀ j, Measurable (w j) :=
    fun j => (normalizedNormalHeight_continuous (a j) (N j) (δ j)).measurable
  have hPm : ∀ j, Measurable (P j) :=
    fun j => (tangentPlaneProjection_continuous (a j) (L j)).measurable
  have hv : LipschitzWith ‖B‖₊ v := vectorAffine_lipschitz b B
  have hvm : Measurable v := hv.continuous.measurable
  have hphysical : ∀ j, ∀ᵐ x ∂μ j, dist x (P j x) ≤ δ j * ‖w j x‖ := by
    intro j
    exact Eventually.of_forall fun x =>
      (physical_projection_distance_eq (a j) (L j) (N j) (hsplit j) (δ j) (hδ j) x).le
  have hproj : ∀ j, Integrable (fun x => ‖v x - v (P j x)‖ ^ 2) (μ j) :=
    fun j => (lipschitz_retraction_error_integral_bound (μ j) v ‖B‖₊ hv (P j) (hPm j)
      (δ j) (hδ j).le (w j) (hraw j) (hphysical j)).1
  have hprojlim := lipschitz_retraction_error_tendsto_zero μ v ‖B‖₊ hv P hPm δ
    (fun j => (hδ j).le) hδlim w hraw hphysical C hC
  have hi : ∀ j, Integrable (fun x => ‖w j x - v (P j x)‖ ^ 2) (μ j) :=
    fun j => (vector_error_integrable_and_bound (μ j) (w j) v (fun x => v (P j x))
      (hwm j) (hvm.comp (hPm j)) (herr j) (hproj j)).1
  have hlim := vector_strong_limit_trans μ w (fun _ => v) (fun j x => v (P j x))
    hwm (fun j => hvm.comp (hPm j)) herr hproj hstrong hprojlim
  let c := fun j => b + B (a j)
  let A := fun j => B.comp (L j).toContinuousLinearMap
  let t := fun j x => (L j).toContinuousLinearMap.adjoint (x - a j)
  have heq : ∀ j x, v (P j x) = c j + A j (t j x) := by
    intro j x
    change b + B (a j + L j ((L j).toContinuousLinearMap.adjoint (x - a j))) =
      (b + B (a j)) + B (L j ((L j).toContinuousLinearMap.adjoint (x - a j)))
    rw [map_add, add_assoc]
  let S := fun j => affineGraphPlane (a j) (L j) (N j) (c j) (A j) (δ j)
  have hg : ∀ j,
      Integrable (fun x => (infDist x (S j : Set (Ambient d)) / δ j) ^ 2) (μ j) ∧
      (∫ x, (infDist x (S j : Set (Ambient d)) / δ j) ^ 2 ∂μ j) ≤
        ∫ x, ‖w j x - v (P j x)‖ ^ 2 ∂μ j := by
    intro j
    have hi' : Integrable (fun x => ‖w j x - (c j + A j (t j x))‖ ^ 2) (μ j) := by
      simpa only [heq] using! hi j
    have h := affineGraphPlane_integral_normalized_distance_sq_le (μ j) (a j) (L j) (N j)
      (c j) (A j) (δ j) (hδ j) (t j) (w j)
      (Eventually.of_forall fun x => normal_coordinates_decomposition (a j) (L j) (N j)
        (hsplit j) (δ j) (hδ j).ne' x) hi'
    simpa only [heq] using! h
  refine ⟨S, ?_, fun j => (hg j).1, ?_⟩
  · intro j
    exact ⟨AffineSubspace.mk'_nonempty _ _,
      affineGraphPlane_direction_finrank (a j) (L j) (N j) (c j) (A j) (δ j) (horth j)⟩
  · exact squeeze_zero (fun j => integral_nonneg fun x => sq_nonneg _)
      (fun j => (hg j).2) hlim

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_NormalFrameExcessLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Topology

theorem moving_normal_frame_squaredExcess_ratio_tendsto_zero {n q d : ℕ}
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)]
    (center : Ambient d) (r : ℝ) (hr : 0 ≤ r) (a : ℕ → Ambient d)
    (L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d) (N : ℕ → Ambient q →ₗᵢ[ℝ] Ambient d)
    (horth : ∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0)
    (hsplit : ∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
      N j ((N j).toContinuousLinearMap.adjoint y) = y)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (b : Ambient q) (B : Ambient d →L[ℝ] Ambient q)
    (hraw : ∀ j, Integrable (fun x => ‖normalizedNormalHeight (a j) (N j) (δ j) x‖ ^ 2) ((σ j).restrict (ball center r)))
    (C : ℝ) (hC : ∀ j, (∫ x, ‖normalizedNormalHeight (a j) (N j) (δ j) x‖ ^ 2 ∂(σ j).restrict (ball center r)) ≤ C)
    (herr : ∀ j, Integrable
      (fun x => ‖normalizedNormalHeight (a j) (N j) (δ j) x - (b + B x)‖ ^ 2) ((σ j).restrict (ball center r)))
    (hstrong : Tendsto (fun j => ∫ x,
      ‖normalizedNormalHeight (a j) (N j) (δ j) x - (b + B x)‖ ^ 2 ∂(σ j).restrict (ball center r)) atTop (𝓝 0)) :
    Tendsto (fun j => squaredExcess n (σ j) center r / δ j ^ 2) atTop (𝓝 0) := by
  obtain ⟨S, hS, _hi, hlim⟩ := moving_affine_graph_distance_tendsto_zero
    (fun j => (σ j).restrict (ball center r)) a L N horth hsplit δ hδ hδlim
    b B hraw C hC herr hstrong
  exact squaredExcess_ratio_tendsto_zero_of_planes n σ center r hr S hS δ hlim

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_NormalAffineExcessBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology WithLp
open scoped NNReal ENNReal

theorem normal_frame_excess_of_common_affine_coordinates {n q d : ℕ}
    (e : (Fin n → ℝ) → Ambient d) (π : Ambient d → Fin n → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (z : Ambient d) (Llim : Ambient n →ₗᵢ[ℝ] Ambient d)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (a : ℕ → Ambient d) (L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d)
    (N : ℕ → Ambient q →ₗᵢ[ℝ] Ambient d)
    (horth : ∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0)
    (hsplit : ∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
      N j ((N j).toContinuousLinearMap.adjoint y) = y)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (hw : ∀ i H j, MemLp (fun x => normalCoordinate (a j) (N j) i x / δ j) 2
      ((μ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B₀ : ℕ → ℝ)
    (hB₀ : ∀ i H j, (∫ x, (normalCoordinate (a j) (N j) i x / δ j) ^ 2
      ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B₀ H)
    (c : Fin q → ℝ) (M : Fin q → Ambient n →L[ℝ] ℝ)
    (hscalar : ∀ i H, Tendsto (fun j => ∫ x,
      (normalCoordinate (a j) (N j) i x / δ j - ambientAffineHeight z Llim (c i) (M i) x) ^ 2
      ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop (𝓝 0)) :
    ∀ r : ℝ, 0 ≤ r →
      Tendsto (fun j => squaredExcess n (μ j) (e 0) r / δ j ^ 2) atTop (𝓝 0) := by
  obtain ⟨v₀, B, hstrong⟩ := exists_vector_affine_strong_limit_of_coordinates z (e 0) Llim
    π K Q hπ μ (fun i j x => normalCoordinate (a j) (N j) i x / δ j) hw c M hscalar
  simp only [normalCoordinate_normalized_vector] at hstrong
  intro r hr
  obtain ⟨H, hH⟩ := exists_boundedProjectionRegion_containing_ball e π K Q hπ hleft r
  have hraw := fun j => normalizedNormalHeight_second_moment_bound
    ((μ j).restrict (boundedProjectionRegion π (e 0) K H)) (a j) (N j) (δ j)
    (fun i => hw i H j) (B₀ H) (fun i => hB₀ i H j)
  have hrawBall : ∀ j, Integrable (fun x => ‖normalizedNormalHeight (a j) (N j) (δ j) x‖ ^ 2)
      ((μ j).restrict (ball (e 0) r)) :=
    fun j => IntegrableOn.mono_set (hraw j).1 hH
  have hbound : ∀ j, (∫ x in ball (e 0) r,
      ‖normalizedNormalHeight (a j) (N j) (δ j) x‖ ^ 2 ∂μ j) ≤ (q : ℝ) * B₀ H := by
    intro j
    exact (setIntegral_mono_set (hraw j).1
      (Eventually.of_forall fun x => sq_nonneg ‖normalizedNormalHeight (a j) (N j) (δ j) x‖)
      (Eventually.of_forall fun x hx => hH hx)).trans (hraw j).2
  have herr : ∀ j, Integrable
      (fun x => ‖normalizedNormalHeight (a j) (N j) (δ j) x - (v₀ + B x)‖ ^ 2)
      ((μ j).restrict (ball (e 0) r)) :=
    fun j => IntegrableOn.mono_set ((hstrong H).1 j) hH
  have hball : Tendsto (fun j => ∫ x in ball (e 0) r,
      ‖normalizedNormalHeight (a j) (N j) (δ j) x - (v₀ + B x)‖ ^ 2 ∂μ j) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun j => integral_nonneg fun x => sq_nonneg ‖normalizedNormalHeight (a j) (N j) (δ j) x - (v₀ + B x)‖)
      _ (hstrong H).2
    intro j
    exact setIntegral_mono_set ((hstrong H).1 j)
      (Eventually.of_forall fun x => sq_nonneg ‖normalizedNormalHeight (a j) (N j) (δ j) x - (v₀ + B x)‖)
      (Eventually.of_forall fun x hx => hH hx)
  exact moving_normal_frame_squaredExcess_ratio_tendsto_zero μ (e 0) r hr a L N horth hsplit
    δ hδ hδlim v₀ B hrawBall ((q : ℝ) * B₀ H) hbound herr hball

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_NormalHeightFromPlaneMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem normalCoordinate_abs_le_plane_distance {q d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hdist : ∀ x, infDist x (S : Set (Ambient d)) = ‖N.toContinuousLinearMap.adjoint (x - a)‖)
    (i : Fin q) (x : Ambient d) :
    |normalCoordinate a N i x| ≤ infDist x (S : Set (Ambient d)) := by
  rw [hdist x]
  exact PiLp.norm_apply_le (N.toContinuousLinearMap.adjoint (x - a)) i

theorem normalCoordinate_memLp_on_ball {q d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q)
    (R : ℝ) (hR : 0 < R) : MemLp (normalCoordinate a N i) 2 (μ.restrict (ball 0 R)) :=
  lipschitz_height_memLp_on_ball m C μ hg (normalCoordinate a N i) 1
    (normalCoordinate_lipschitz a N i) 0 R hR

theorem normalCoordinate_second_moment_le_plane {q d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth m C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (a : Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hdist : ∀ x, infDist x (S : Set (Ambient d)) = ‖N.toContinuousLinearMap.adjoint (x - a)‖)
    (i : Fin q) (R : ℝ) (hR : 0 < R) :
    (∫ x in ball (0 : Ambient d) R, normalCoordinate a N i x ^ 2 ∂μ) ≤
      ∫ x in ball (0 : Ambient d) R, infDist x (S : Set (Ambient d)) ^ 2 ∂μ := by
  apply integral_mono (normalCoordinate_memLp_on_ball m μ C hg a N i R hR).integrable_sq
    (squared_infDist_integrableOn_ball μ 0 R S hS)
  intro x
  have h := (sq_le_sq₀ (abs_nonneg (normalCoordinate a N i x)) infDist_nonneg).mpr
    (normalCoordinate_abs_le_plane_distance S a N hdist i x)
  simpa only [sq_abs] using! h

theorem normalCoordinate_dyadic_source_bound {n q d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (a : Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hdist : ∀ x, infDist x (S : Set (Ambient d)) = ‖N.toContinuousLinearMap.adjoint (x - a)‖)
    (M δ b : ℝ) (l : ℕ)
    (hbound : (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S : Set (Ambient d)) ^ 2 ∂μ) ≤
      M * (δ * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2)) (i : Fin q) :
    (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), normalCoordinate a N i x ^ 2 ∂μ) ≤
      δ ^ 2 * M * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2 := by
  calc
    _ ≤ ∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S : Set (Ambient d)) ^ 2 ∂μ :=
      normalCoordinate_second_moment_le_plane n μ C hg S hS a N hdist i ((2 : ℝ) ^ l) (by positivity)
    _ ≤ M * (δ * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2) := hbound
    _ = _ := by rw [pow_add ((2 : ℝ) ^ l) n 2]; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_NormalizedLocalEnergyBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local integrability of normalized Lipschitz energies

Growth bounds make normalized Lipschitz functions square-integrable on balls and
their fractional pair energies integrable on the corresponding product measure.
An auxiliary sequence bound absorbs finitely many exceptional scales into one nonnegative bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal

theorem normalized_lipschitz_memLp_on_ball {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (u : Ambient d → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u)
    (a : Ambient d) (r δ : ℝ) (hr : 0 < r) :
    MemLp (fun x => u x / δ) 2 (μ.restrict (ball a r)) := by
  have h := (lipschitz_height_memLp_on_ball n G μ hg u K hu a r hr).const_smul δ⁻¹
  change MemLp (fun x => δ⁻¹ * u x) 2 (μ.restrict (ball a r)) at h
  simpa only [div_eq_mul_inv, mul_comm] using! h

theorem nonnegative_uniform_bound_of_eventually_le (f : ℕ → ℝ) (B : ℝ)
    (hB : ∀ᶠ j in atTop, f j ≤ B) : ∃ M : ℝ, 0 ≤ M ∧ ∀ j, f j ≤ M := by
  have h : IsBoundedUnder (· ≤ ·) atTop f := ⟨B, hB⟩
  obtain ⟨M, hM⟩ := h.bddAbove_range
  exact ⟨max 0 M, le_max_left _ _, fun j => (hM ⟨j, rfl⟩).trans (le_max_right _ _)⟩

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

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SourceNormalizedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem source_normalized_second_moments_on_ball {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (u : ℕ → Ambient d → ℝ) (K : ℝ≥0) (hu : ∀ j, LipschitzWith K (u j))
    (a : Ambient d) (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ)
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), u j x ^ 2 ∂μ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j,
      MemLp (fun x => u j x / δ j) 2 ((μ j).restrict (ball a r)) ∧
      (∫ x in ball a r, (u j x / δ j) ^ 2 ∂μ j) ≤ B := by
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt r (by norm_num : (1 : ℝ) < 2)
  let B₀ := D * ((2 : ℝ) ^ q) ^ n * ((2 : ℝ) ^ q * b ^ q) ^ 2
  have hI (j : ℕ) := normalized_lipschitz_memLp_on_ball n G (μ j) (hg j) (u j) K
    (hu j) a r (δ j) hr
  have hlarge (j : ℕ) := normalized_lipschitz_memLp_on_ball n G (μ j) (hg j) (u j) K
    (hu j) a ((2 : ℝ) ^ q) (δ j) (by positivity)
  have hbound : ∀ᶠ j in atTop, (∫ x in ball a r, (u j x / δ j) ^ 2 ∂μ j) ≤ B₀ := by
    filter_upwards [hN.eventually (eventually_ge_atTop q)] with j hj
    apply (integral_mono_measure
      (Measure.restrict_mono (ball_subset_ball hq.le) le_rfl)
      (Eventually.of_forall fun x => sq_nonneg (u j x / δ j)) (hlarge j).integrable_sq).trans
    apply normalized_second_moment_bound ((μ j).restrict (ball a ((2 : ℝ) ^ q)))
      (u j) (δ j) B₀ (hδ j)
    convert! hsource j q hj using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [B₀]
    ring
  obtain ⟨B, hB, hb⟩ := nonnegative_uniform_bound_of_eventually_le _ B₀ hbound
  exact ⟨B, hB, fun j => ⟨hI j, hb j⟩⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SourceNormalizedRegionData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized height data on bounded projection regions

Uniform square-integral and fractional-energy bounds on balls restrict to the
bounded projection regions inside them. Choosing bounds at each region's outer
radius produces constants indexed by the region size, independent of the
sequence index. Positivity of the integrands and monotonicity of restricted
product measures preserve both estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal

theorem normalized_region_data_of_ball_data {ι : Type*} [Fintype ι] {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, SFinite (μ j)]
    (w : ℕ → Ambient d → ℝ) (a : Ambient d)
    (hball : ∀ r : ℝ, 0 < r → ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ ∀ j,
      MemLp (w j) 2 ((μ j).restrict (ball a r)) ∧
      (∫ x in ball a r, w j x ^ 2 ∂μ j) ≤ B ∧
      Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy n (w j) q.1 q.2)
        (((μ j).restrict (ball a r)).prod ((μ j).restrict (ball a r))) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy n (w j) q.1 q.2
        ∂((μ j).restrict (ball a r)).prod ((μ j).restrict (ball a r))) ≤ E)
    (π : Ambient d → ι → ℝ) (K : ℝ≥0) :
    ∃ B E : ℕ → ℝ, ∀ H, 0 ≤ B H ∧ 0 ≤ E H ∧ ∀ j,
      MemLp (w j) 2 ((μ j).restrict (boundedProjectionRegion π a K H)) ∧
      (∫ x in boundedProjectionRegion π a K H, w j x ^ 2 ∂μ j) ≤ B H ∧
      Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy n (w j) q.1 q.2)
        (((μ j).restrict (boundedProjectionRegion π a K H)).prod
          ((μ j).restrict (boundedProjectionRegion π a K H))) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy n (w j) q.1 q.2
        ∂((μ j).restrict (boundedProjectionRegion π a K H)).prod
          ((μ j).restrict (boundedProjectionRegion π a K H))) ≤ E H := by
  choose B E hB hE hd using
    (fun H => hball (planeBoxOuterRadius K H) (planeBoxOuterRadius_pos K H))
  refine ⟨B, E, fun H => ⟨hB H, hE H, fun j => ?_⟩⟩
  have hs : boundedProjectionRegion π a K H ⊆ ball a (planeBoxOuterRadius K H) := inter_subset_right
  have hμ := Measure.restrict_mono (μ := μ j) hs le_rfl
  have hprod : ((μ j).restrict (boundedProjectionRegion π a K H)).prod
      ((μ j).restrict (boundedProjectionRegion π a K H)) ≤
      ((μ j).restrict (ball a (planeBoxOuterRadius K H))).prod
        ((μ j).restrict (ball a (planeBoxOuterRadius K H))) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    exact Measure.restrict_mono (prod_mono hs hs) le_rfl
  exact ⟨MemLp.mono_measure hμ (hd H j).1,
    (integral_mono_measure hμ (Eventually.of_forall fun x => sq_nonneg (w j x))
      (hd H j).1.integrable_sq).trans (hd H j).2.1,
    (hd H j).2.2.1.mono_measure hprod,
    (integral_mono_measure hprod
      (Eventually.of_forall fun q => fractionalPairEnergy_nonneg n (w j) q.1 q.2)
      (hd H j).2.2.1).trans (hd H j).2.2.2⟩

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

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CommonHeightLocalIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Intrinsic local integrability of common heights

Square integrability on bounded projection regions implies integrability on every
plane ball, since the coordinate-plane measure has finite mass there. Pulling
these ball restrictions back along an affine isometric parametrization gives
local integrability of the intrinsic height function on Euclidean space.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal Topology

theorem locallyIntegrable_of_integrableOn_origin_balls {d : ℕ}
    (f : Ambient d → ℝ)
    (hf : ∀ R : ℝ, 0 < R → IntegrableOn f (ball 0 R)) : LocallyIntegrable f := by
  intro x
  refine ⟨ball 0 (‖x‖ + 1), isOpen_ball.mem_nhds ?_, hf _ (by positivity)⟩
  simp only [mem_ball, dist_zero_right]
  linarith

theorem common_height_intrinsic_locallyIntegrable {n d : ℕ}
    (e : (Fin n → ℝ) → Ambient d) (π : Ambient d → Fin n → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π)
    (hleft : LeftInverse π e) (a : Ambient d) (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (hplane : e = affinePlaneSection a L) (f : Ambient d → ℝ)
    (hf : ∀ H, MemLp f 2
      ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) :
    LocallyIntegrable (fun x : Ambient n => f (a + L x)) := by
  have he0 : e 0 = a := by rw [hplane]; simp [affinePlaneSection]
  have hνg : GlobalUpperGrowth n ((2 * (Q : ℝ)) ^ n) (coordinatePlaneMeasure e) := by
    simpa only [Fintype.card_fin] using! coordinatePlaneMeasure_upper_growth e π
      he.continuous.measurable Q hπ hleft
  apply locallyIntegrable_of_integrableOn_origin_balls
  intro R hR
  obtain ⟨H, hH⟩ := (eventually_ball_subset_boundedProjectionRegion e π K Q hπ hleft R).exists
  have hmem : MemLp f 2 ((coordinatePlaneMeasure e).restrict (ball (e 0) R)) :=
    MemLp.mono_measure (Measure.restrict_mono hH le_rfl) (hf H)
  let : IsFiniteMeasure ((coordinatePlaneMeasure e).restrict (ball (e 0) R)) :=
    finiteMeasure_restrict_ball_of_globalGrowth n ((2 * (Q : ℝ)) ^ n)
      (coordinatePlaneMeasure e) hνg (e 0) R hR
  have hi : IntegrableOn f (ball (e 0) R) (coordinatePlaneMeasure e) :=
    hmem.integrable (by norm_num)
  rw [he0, hplane] at hi
  exact height_local_integrable_affine_pullback a L f R hi

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_LipschitzRepresentativeStrongLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped NNReal

theorem strong_height_convergence_of_lipschitz_representative {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (a : Ambient d) (R : ℝ)
    (hμ : ∀ j, ∀ᵐ x ∂(μ j : Measure (Ambient d)), x ∈ ball a R)
    (hν : ∀ᵐ x ∂(ν : Measure (Ambient d)), x ∈ ball a R)
    (w : ℕ → Ambient d → ℝ) (hw : ∀ j, MemLp (w j) 2 (μ j : Measure (Ambient d)))
    (f v : Ambient d → ℝ) (L : ℝ≥0) (hv : LipschitzWith L v)
    (hfv : f =ᵐ[(ν : Measure (Ambient d))] v)
    (hsecond : Tendsto (fun j => ∫ x, w j x ^ 2 ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x, f x ^ 2 ∂(ν : Measure (Ambient d)))))
    (hmoment : ∀ (ψ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith J ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j : Measure (Ambient d))) atTop
        (𝓝 (∫ x, f x * ψ x ∂(ν : Measure (Ambient d))))) :
    Tendsto (fun j => ∫ x, (w j x - v x) ^ 2 ∂(μ j : Measure (Ambient d)))
      atTop (𝓝 0) := by
  have hvj : ∀ j, MemLp v 2 (μ j : Measure (Ambient d)) :=
    fun j => lipschitz_memLp_of_ae_ball _ a R (hμ j) v L hv
  have hcross := compact_moments_extend_on_ball (fun j => (μ j : Measure (Ambient d)))
    (ν : Measure (Ambient d)) a R hμ hν w f hmoment v L hv
  have hcross_eq : (∫ x, f x * v x ∂(ν : Measure (Ambient d))) =
      ∫ x, f x ^ 2 ∂(ν : Measure (Ambient d)) := by
    apply integral_congr_ae
    filter_upwards [hfv] with x hx
    rw [hx, pow_two]
  rw [hcross_eq] at hcross
  have hsquare := lipschitz_square_integral_tendsto_of_ae_ball μ ν hweak a R hμ hν v L hv
  have hsquare_eq : (∫ x, v x ^ 2 ∂(ν : Measure (Ambient d))) =
      ∫ x, f x ^ 2 ∂(ν : Measure (Ambient d)) := by
    apply integral_congr_ae
    filter_upwards [hfv] with x hx
    rw [hx]
  rw [hsquare_eq] at hsquare
  exact squared_error_tendsto_zero_of_moments (fun j => (μ j : Measure (Ambient d)))
    w v (∫ x, f x ^ 2 ∂(ν : Measure (Ambient d)))
    (fun j => (hw j).integrable_sq) (fun j => (hw j).integrable_mul (hvj j))
    (fun j => (hvj j).integrable_sq) hsecond hcross hsquare

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_BoundedAffineStrongLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem bounded_height_strong_of_lipschitz_representative {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)]
    (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e)) (H : ℕ)
    (w : ℕ → Ambient d → ℝ)
    (hw : ∀ j, MemLp (w j) 2 ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (f v : Ambient d → ℝ) (J : ℝ≥0) (hv : LipschitzWith J v)
    (hfv : f =ᵐ[coordinatePlaneMeasure e] v)
    (hsecond : Tendsto (fun j => ∫ x, w j x ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
      (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))))
    (hmoment : ∀ (ψ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith J ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x
        ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
        (𝓝 (∫ x, f x * ψ x
          ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) :
    Tendsto (fun j => ∫ x, (w j x - v x) ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop (𝓝 0) := by
  let μ := fun j => boundedProjectionFiniteMeasure (σ j) π (e 0) K H
  let ν := boxPlaneFiniteMeasure (exhaustionBox ι H) e
  have hνeq : (coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H) =
      (ν : Measure (Ambient d)) :=
    coordinatePlaneMeasure_restrict_boundedRegion e π K he hπ.continuous hleft H
  have hs := (boundedProjectionRegion_isOpen π hπ.continuous (e 0) K H).measurableSet
  have hμball : ∀ j, ∀ᵐ x ∂(μ j : Measure (Ambient d)),
      x ∈ ball (e 0) (planeBoxOuterRadius K H) := by
    intro j
    filter_upwards [ae_restrict_mem (μ := σ j) hs] with x hx
    exact hx.2
  have hνball : ∀ᵐ x ∂(ν : Measure (Ambient d)),
      x ∈ ball (e 0) (planeBoxOuterRadius K H) := by
    rw [← hνeq]
    filter_upwards [ae_restrict_mem (μ := coordinatePlaneMeasure e) hs] with x hx
    exact hx.2
  have hfv' : f =ᵐ[(ν : Measure (Ambient d))] v := by
    rw [← hνeq]
    exact ae_restrict_of_ae hfv
  apply strong_height_convergence_of_lipschitz_representative μ ν
    (boundedProjectionFiniteMeasure_tendsto e π K Q he hπ hleft σ hlocal H)
    (e 0) (planeBoxOuterRadius K H) hμball hνball w hw f v J hv hfv'
  · simpa only [hνeq] using! hsecond
  · intro ψ J B hc hLip hB
    simpa only [hνeq] using! hmoment ψ J B hc hLip hB

theorem bounded_height_strong_of_intrinsic_affine {n d : ℕ}
    (e : (Fin n → ℝ) → Ambient d) (π : Ambient d → Fin n → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (a : Ambient d) (L : Ambient n →ₗᵢ[ℝ] Ambient d) (hplane : e = affinePlaneSection a L)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)]
    (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e)) (H : ℕ)
    (w : ℕ → Ambient d → ℝ)
    (hw : ∀ j, MemLp (w j) 2 ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (f : Ambient d → ℝ) (hfm : Measurable f) (c : ℝ) (M : Ambient n →L[ℝ] ℝ)
    (hfa : ∀ᵐ x, f (a + L x) = c + M x)
    (hsecond : Tendsto (fun j => ∫ x, w j x ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
      (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))))
    (hmoment : ∀ (ψ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith J ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x
        ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
        (𝓝 (∫ x, f x * ψ x
          ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) :
    Tendsto (fun j => ∫ x, (w j x - ambientAffineHeight a L c M x) ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop (𝓝 0) := by
  have hfv : f =ᵐ[coordinatePlaneMeasure e] ambientAffineHeight a L c M := by
    rw [hplane]
    exact height_ae_eq_ambient_affine a L f hfm c M hfa
  exact bounded_height_strong_of_lipschitz_representative e π K Q he hπ hleft σ hlocal H w hw
    f (ambientAffineHeight a L c M) _ (ambientAffineHeight_lipschitz a L c M) hfv hsecond hmoment

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_AffineHeightRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Function
open scoped NNReal

theorem common_height_intrinsic_ae_affine {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π)
    (hleft : LeftInverse π e) (a : Ambient d) (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d)
    (hplane : e = affinePlaneSection a L) (f : Ambient d → ℝ)
    (hf : ∀ H, MemLp f 2
      ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))
    (T : 𝓢'(Ambient (p + 1), ℂ))
    (hT : ∀ g : 𝓢(Ambient (p + 1), ℂ), T g = ∫ x, f (a + L x) • g x)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, f (a + L x) • fractionalSchwartzTest p g x) = 0)
    (htail : IntegrableOn (fun x => |f x| * inverseDistancePow (p + 1 + 2) (e 0) x)
      (closedExterior (e 0) 1) (coordinatePlaneMeasure e)) :
    ∃ c : ℝ, ∃ M : Ambient (p + 1) →L[ℝ] ℝ, ∀ᵐ x, f (a + L x) = c + M x := by
  have he0 : e 0 = a := by rw [hplane]; simp [affinePlaneSection]
  have htail' := htail
  rw [he0, hplane] at htail'
  exact represented_fractional_height_ae_affine p (fun x => f (a + L x))
    (common_height_intrinsic_locallyIntegrable e π K Q he hπ hleft a L hplane f hf)
    T hT heq (height_tail_integrable_affine_pullback (p + 1 + 2) a L f 1 htail')

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_DyadicCommonAffineStrongLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A common affine strong limit from dyadic bounds

The common height limit satisfies a fractional equation whose rigidity forces
it to be affine on the limiting plane. Second-moment and moment convergence then
give strong square-integral convergence to the corresponding ambient affine
height on every bounded projection region, along one shared subsequence.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology SchwartzMap
open scoped NNReal ENNReal ContDiff

theorem exists_common_affine_strong_limit {d : ℕ} (p : ℕ)
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
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ c : ℝ, ∃ M : Ambient (p + 1) →L[ℝ] ℝ,
      ∀ H, Tendsto (fun j => ∫ x,
        (u (ρ j) x / δ (ρ j) - ambientAffineHeight a L c M x) ^ 2
        ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop (𝓝 0) := by
  obtain ⟨ρ, hρ, f, hfm, hf, hsecond, hmoment, _, hTail, _, hFractional, T, hT, _⟩ :=
    exists_common_height_with_fractional_equation p e π K Q he hπ hleft a L hplane
      σ hlocal C G hC hg hlower hdiam u Ku hu z hz hdiff δ A v hδ hA hosc hratio W hW
      hw B₀ E₀ hB₀ henergy hE₀ N hN D b hb0 hb2 hlast hsource
  obtain ⟨c, M, hfa⟩ := common_height_intrinsic_ae_affine p e π K Q he hπ hleft a L hplane
    f hf T (fun g => (hT g).2) hFractional (hTail 1 (by norm_num))
  have hsub : CompactTestConvergence (fun j => σ (ρ j)) (coordinatePlaneMeasure e) := by
    intro g
    exact (hlocal g).comp hρ.tendsto_atTop
  refine ⟨ρ, hρ, c, M, ?_⟩
  intro H
  exact bounded_height_strong_of_intrinsic_affine e π K Q he hπ hleft a L hplane
    (fun j => σ (ρ j)) hsub H (fun j x => u (ρ j) x / δ (ρ j))
    (fun j => hw H (ρ j)) f hfm c M hfa (hsecond H) (hmoment H)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_NormalFrameSourceEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Source energy in a normal frame

Convergence of frame centers gives a common bound for their normal coordinates at
the origin. Applying the scalar source estimates coordinatewise supplies local L²
and fractional pair-energy bounds for normalized normal heights on every fixed ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem normalCoordinate_abs_at_zero_le_norm {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) :
    |normalCoordinate a N i 0| ≤ ‖a‖ := by
  rw [normalCoordinate_eq_inner]
  simpa only [normalDirection_norm, one_mul, zero_sub, norm_neg] using!
    abs_real_inner_le_norm (normalDirection N i) ((0 : Ambient d) - a)

theorem normalCoordinates_uniform_center_bound {q d : ℕ}
    (a : ℕ → Ambient d) (ha : Tendsto a atTop (𝓝 0))
    (N : ℕ → Ambient q →ₗᵢ[ℝ] Ambient d) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ j i, |normalCoordinate (a j) (N j) i 0| ≤ W := by
  have hn : Tendsto (fun j => ‖a j‖) atTop (𝓝 0) := by simpa only [norm_zero] using! ha.norm
  have hb : ∀ᶠ j in atTop, ‖a j‖ ≤ 1 :=
    (hn.eventually (gt_mem_nhds zero_lt_one)).mono fun _ h => h.le
  obtain ⟨W, hW, hw⟩ := nonnegative_uniform_bound_of_eventually_le _ 1 hb
  exact ⟨W, hW, fun j i => (normalCoordinate_abs_at_zero_le_norm (a j) (N j) i).trans (hw j)⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_FiniteCommonSubsequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

open Function

theorem exists_finite_common_subsequence {ι : Type*} [Fintype ι]
    (P : ι → (ℕ → ℕ) → Prop)
    (hextract : ∀ i ρ, StrictMono ρ → ∃ σ : ℕ → ℕ, StrictMono σ ∧ P i (ρ ∘ σ))
    (hstable : ∀ i ρ σ, P i ρ → StrictMono σ → P i (ρ ∘ σ)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ i, P i ρ := by
  classical
  have hfinite (s : Finset ι) : ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ i ∈ s, P i ρ := by
    induction s using Finset.induction_on with
    | empty => exact ⟨id, strictMono_id, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ρ, hρ, hP⟩ := ih
      obtain ⟨σ, hσ, hiP⟩ := hextract i ρ hρ
      refine ⟨ρ ∘ σ, hρ.comp hσ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hiP
      · exact hstable j ρ σ (hP j hj) hσ
  obtain ⟨ρ, hρ, hP⟩ := hfinite Finset.univ
  exact ⟨ρ, hρ, fun i => hP i (Finset.mem_univ i)⟩

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ScaledRieszOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem nnreal_smul_prod_same {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (c : ℝ≥0) :
    (c • μ).prod (c • ν) = c ^ 2 • μ.prod ν := by
  change ((c : ℝ≥0∞) • μ).prod ((c : ℝ≥0∞) • ν) = ((c ^ 2 : ℝ≥0) : ℝ≥0∞) • μ.prod ν
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  simp only [pow_two, ENNReal.coe_mul]

theorem rieszScalarPairing_smul_nnreal {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (c : ℝ≥0)
    (a : Ambient d) (R : ℝ) (e : Ambient d) (φ : Ambient d → ℝ) :
    rieszScalarPairing n (c • μ) a R e φ = (c : ℝ) ^ 2 * rieszScalarPairing n μ a R e φ := by
  unfold rieszScalarPairing
  dsimp only
  simp_rw [Measure.restrict_smul, nnreal_smul_prod_same]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_pow, smul_eq_mul]
  ring

theorem ScalarOscillationBound.smul_nnreal {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a : Ambient d) (A v : ℝ)
    (hosc : ScalarOscillationBound n μ a A v) (c : ℝ≥0) (hc : 0 < c) :
    ScalarOscillationBound n (c • μ) a A ((c : ℝ) ^ 2 * v) := by
  intro e he φ hφ hs hzero
  have hcR : (c : ℝ) ≠ 0 := (NNReal.coe_pos.mpr hc).ne'
  have hz : (∫ x, φ x ∂μ) = 0 := by
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hcR
  rw [rieszScalarPairing_smul_nnreal, abs_mul, abs_of_nonneg (sq_nonneg (c : ℝ))]
  exact mul_le_mul_of_nonneg_left (hosc e he φ hφ hs hz) (sq_nonneg _)

theorem scaled_cubic_oscillation_ratio_tendsto (δ : ℕ → ℝ)
    (hδ : ∀ j, 0 < δ j) (ht : Tendsto δ atTop (𝓝 0)) (c : ℝ≥0) :
    Tendsto (fun j => ((c : ℝ) ^ 2 * δ j ^ 3) / δ j) atTop (𝓝 0) := by
  have heq (j : ℕ) : ((c : ℝ) ^ 2 * δ j ^ 3) / δ j = (c : ℝ) ^ 2 * δ j ^ 2 := by
    field_simp [(hδ j).ne']
  simp_rw [heq]
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using! (ht.pow 2).const_mul ((c : ℝ) ^ 2)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ScaledSourceMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem positive_nnreal_smul_support {d : ℕ} (μ : Measure (Ambient d))
    (c : ℝ≥0) (hc : 0 < c) : (c • μ).support = μ.support := by
  have hcE : 0 < (c : ℝ≥0∞) := by exact_mod_cast hc
  ext x
  rw [Metric.nhds_basis_ball.mem_measureSupport, Metric.nhds_basis_ball.mem_measureSupport]
  constructor
  · intro hx r hr
    have h := hx r hr
    rw [Measure.coe_nnreal_smul_apply] at h
    exact (ENNReal.mul_pos_iff.mp h).2
  · intro hx r hr
    rw [Measure.coe_nnreal_smul_apply]
    exact ENNReal.mul_pos_iff.mpr ⟨hcE, hx r hr⟩

theorem positive_nnreal_smul_admissibleRadius {d : ℕ} (μ : Measure (Ambient d))
    (c : ℝ≥0) (hc : 0 < c) (r : ℝ) :
    AdmissibleRadius (c • μ) r ↔ AdmissibleRadius μ r := by
  simp only [AdmissibleRadius, positive_nnreal_smul_support μ c hc]

theorem globalUpperGrowth_smul_nnreal {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ) (c : ℝ≥0) :
    GlobalUpperGrowth n ((c : ℝ) * G) (c • μ) := by
  refine ⟨mul_nonneg c.coe_nonneg hg.1, fun x r hr => ?_⟩
  rw [Measure.coe_nnreal_smul_apply]
  calc
    _ ≤ (c : ℝ≥0∞) * ENNReal.ofReal (G * r ^ n) := mul_le_mul_right (hg.2 x r hr) _
    _ = ENNReal.ofReal ((c : ℝ) * G * r ^ n) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg]
      congr 1
      ring

theorem lowerGrowth_smul_nnreal {d : ℕ} (n : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hC : 0 < C)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (c : ℝ≥0) (hc : 0 < c) :
    ∀ x ∈ (c • μ).support, ∀ r : ℝ, AdmissibleRadius (c • μ) r →
      ENNReal.ofReal (r ^ n / (C / (c : ℝ))) ≤ (c • μ) (ball x r) := by
  intro x hx r hr
  have hcR : 0 < (c : ℝ) := NNReal.coe_pos.mpr hc
  have hx' : x ∈ μ.support := by simpa only [positive_nnreal_smul_support μ c hc] using! hx
  have hr' := (positive_nnreal_smul_admissibleRadius μ c hc r).mp hr
  rw [Measure.coe_nnreal_smul_apply]
  calc
    _ = (c : ℝ≥0∞) * ENNReal.ofReal (r ^ n / C) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg]
      congr 1
      field_simp
    _ ≤ _ := mul_le_mul_right (hlower x hx' r hr') _

theorem compactTestConvergence_smul_nnreal {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (hlocal : CompactTestConvergence μ ν) (c : ℝ≥0) :
    CompactTestConvergence (fun j => c • μ j) (c • ν) := by
  intro g
  simpa only [integral_smul_nnreal_measure, smul_eq_mul] using! (hlocal g).const_mul (c : ℝ)

theorem compactTestConvergence_cancel_scalar_limit {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν σ : Measure (Ambient d))
    (hlocal : CompactTestConvergence μ ν) (q : ℝ)
    (hν : ν = ENNReal.ofReal q • σ) (c : ℝ≥0) (hcq : (c : ℝ) * q = 1) :
    CompactTestConvergence (fun j => c • μ j) σ := by
  have h := compactTestConvergence_smul_nnreal μ ν hlocal c
  have heq : c • ν = σ := by
    rw [hν]
    change (c : ℝ≥0∞) • (ENNReal.ofReal q • σ) = σ
    rw [smul_smul]
    have hcoef : (c : ℝ≥0∞) * ENNReal.ofReal q = 1 := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg, hcq, ENNReal.ofReal_one]
    rw [hcoef, one_smul]
  simpa only [heq] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ScaledHeightData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem setIntegral_smul_nnreal_real {d : ℕ} (μ : Measure (Ambient d))
    (s : Set (Ambient d)) (f : Ambient d → ℝ) (c : ℝ≥0) :
    (∫ x in s, f x ∂c • μ) = (c : ℝ) * ∫ x in s, f x ∂μ := by
  rw [Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

theorem restricted_pair_integral_smul_nnreal {d : ℕ} (μ : Measure (Ambient d)) [SFinite μ]
    (s t : Set (Ambient d)) (f : Ambient d × Ambient d → ℝ) (c : ℝ≥0) :
    (∫ q, f q ∂((c • μ).restrict s).prod ((c • μ).restrict t)) =
      (c : ℝ) ^ 2 * ∫ q, f q ∂(μ.restrict s).prod (μ.restrict t) := by
  simp only [Measure.restrict_smul, nnreal_smul_prod_same, integral_smul_nnreal_measure,
    NNReal.smul_def, NNReal.coe_pow, smul_eq_mul]

theorem local_height_data_smul_nnreal {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (s : Set (Ambient d)) (w : Ambient d → ℝ)
    (B E : ℝ) (hw : MemLp w 2 (μ.restrict s))
    (hB : (∫ x in s, w x ^ 2 ∂μ) ≤ B)
    (hI : Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy n w q.1 q.2)
      ((μ.restrict s).prod (μ.restrict s)))
    (hE : (∫ q : Ambient d × Ambient d, fractionalPairEnergy n w q.1 q.2
      ∂(μ.restrict s).prod (μ.restrict s)) ≤ E) (c : ℝ≥0) :
    MemLp w 2 ((c • μ).restrict s) ∧
      (∫ x in s, w x ^ 2 ∂c • μ) ≤ (c : ℝ) * B ∧
      Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy n w q.1 q.2)
        (((c • μ).restrict s).prod ((c • μ).restrict s)) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy n w q.1 q.2
        ∂((c • μ).restrict s).prod ((c • μ).restrict s)) ≤ (c : ℝ) ^ 2 * E := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Measure.restrict_smul]
    exact hw.smul_measure ENNReal.coe_ne_top
  · rw [setIntegral_smul_nnreal_real]
    exact mul_le_mul_of_nonneg_left hB c.coe_nonneg
  · simp only [Measure.restrict_smul, nnreal_smul_prod_same]
    exact hI.smul_measure_nnreal
  · rw [restricted_pair_integral_smul_nnreal]
    exact mul_le_mul_of_nonneg_left hE (sq_nonneg _)

theorem dyadic_source_moments_smul_nnreal {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (a : Ambient d) (u : ℕ → Ambient d → ℝ)
    (δ : ℕ → ℝ) (N : ℕ → ℕ) (D b : ℝ)
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), u j x ^ 2 ∂μ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2) (c : ℝ≥0) :
    ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), u j x ^ 2 ∂c • μ j) ≤
      δ j ^ 2 * ((c : ℝ) * D) * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2 := by
  intro j l hl
  rw [setIntegral_smul_nnreal_real]
  calc
    _ ≤ (c : ℝ) * (δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2) :=
      mul_le_mul_of_nonneg_left (hsource j l hl) c.coe_nonneg
    _ = _ := by ring

theorem tendsto_setIntegral_of_positive_nnreal_smul {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (s : Set (Ambient d))
    (f : ℕ → Ambient d → ℝ) (c : ℝ≥0) (hc : 0 < c)
    (ht : Tendsto (fun j => ∫ x in s, f j x ∂c • μ j) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x in s, f j x ∂μ j) atTop (𝓝 0) := by
  have hcR : (c : ℝ) ≠ 0 := (NNReal.coe_pos.mpr hc).ne'
  have heq (j : ℕ) : (c : ℝ)⁻¹ * (∫ x in s, f j x ∂c • μ j) = ∫ x in s, f j x ∂μ j := by
    rw [setIntegral_smul_nnreal_real, ← mul_assoc, inv_mul_cancel₀ hcR, one_mul]
  simpa only [heq, mul_zero] using! ht.const_mul (c : ℝ)⁻¹

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_ScaledCommonAffineStrongLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Strong affine limits with positive planar density

Rescaling the measures by the reciprocal limiting density reduces to unit planar
density. Growth, oscillation and local energy estimates scale compatibly, and
canceling the positive scalar transfers the common affine strong limit back.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_common_affine_strong_limit_of_positive_density {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (a : Ambient d) (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (hplane : e = affinePlaneSection a L)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)] [∀ j, SFinite (μ j)]
    (ν : Measure (Ambient d)) (hlocal : CompactTestConvergence μ ν)
    (q : ℝ) (hq : 0 < q) (hν : ν = ENNReal.ofReal q • coordinatePlaneMeasure e)
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (u : ℕ → Ambient d → ℝ) (Ku : ℝ≥0) (hu : ∀ j, LipschitzWith Ku (u j))
    (z : ℕ → Ambient d) (hz : ∀ j, ‖z j‖ ≤ 1)
    (hdiff : ∀ j x y, u j x - u j y = inner ℝ (z j) (x - y))
    (δ A : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) (e 0) (A j) (δ j ^ 3))
    (W : ℝ) (hW : ∀ j, |u j (e 0)| ≤ W)
    (hw : ∀ H j, MemLp (fun x => u j x / δ j) 2
      ((μ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B₀ E₀ : ℕ → ℝ)
    (hB₀ : ∀ H j, (∫ x, (u j x / δ j) ^ 2
      ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B₀ H)
    (henergy : ∀ H j, Integrable
      (fun v : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (fun x => u j x / δ j) v.1 v.2)
      (((μ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((μ j).restrict (boundedProjectionRegion π (e 0) K H))))
    (hE₀ : ∀ H j, (∫ v : Ambient d × Ambient d,
      fractionalPairEnergy (p + 1) (fun x => u j x / δ j) v.1 v.2
      ∂(((μ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((μ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball (e 0) ((2 : ℝ) ^ l), u j x ^ 2 ∂μ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ c : ℝ, ∃ M : Ambient (p + 1) →L[ℝ] ℝ,
      ∀ H, Tendsto (fun j => ∫ x,
        (u (ρ j) x / δ (ρ j) - ambientAffineHeight a L c M x) ^ 2
        ∂(μ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop (𝓝 0) := by
  let k : ℝ≥0 := ⟨q⁻¹, (inv_pos.mpr hq).le⟩
  have hk : 0 < k := by exact_mod_cast inv_pos.mpr hq
  have hkR : 0 < (k : ℝ) := NNReal.coe_pos.mpr hk
  have hkq : (k : ℝ) * q = 1 := inv_mul_cancel₀ hq.ne'
  let σ : ℕ → Measure (Ambient d) := fun j => k • μ j
  have hg' : ∀ j, GlobalUpperGrowth (p + 1) ((k : ℝ) * G) (σ j) :=
    fun j => globalUpperGrowth_smul_nnreal (p + 1) G (μ j) (hg j) k
  let (j : ℕ) : IsFiniteMeasureOnCompacts (σ j) := (hg' j).finite_on_compacts
  have hlocal' : CompactTestConvergence σ (coordinatePlaneMeasure e) :=
    compactTestConvergence_cancel_scalar_limit μ ν (coordinatePlaneMeasure e) hlocal q hν k hkq
  have hlower' : ∀ j x, x ∈ (σ j).support → ∀ r : ℝ, AdmissibleRadius (σ j) r →
      ENNReal.ofReal (r ^ (p + 1) / (C / (k : ℝ))) ≤ (σ j) (ball x r) :=
    fun j => lowerGrowth_smul_nnreal (p + 1) C (μ j) hC (hlower j) k hk
  have hdiam' : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (σ j).support := by
    intro r hr
    simpa only [σ, positive_nnreal_smul_support _ k hk] using! hdiam r hr
  have hosc' : ∀ j, ScalarOscillationBound (p + 1) (σ j) (e 0) (A j)
      ((k : ℝ) ^ 2 * δ j ^ 3) :=
    fun j => ScalarOscillationBound.smul_nnreal (p + 1) (μ j) (e 0) (A j) (δ j ^ 3)
      (hosc j) k hk
  have hdata (H j : ℕ) := local_height_data_smul_nnreal (p + 1) (μ j)
    (boundedProjectionRegion π (e 0) K H) (fun x => u j x / δ j) (B₀ H) (E₀ H)
    (hw H j) (hB₀ H j) (henergy H j) (hE₀ H j) k
  obtain ⟨ρ, hρ, c, M, hstrong⟩ := exists_common_affine_strong_limit p e π K Q he hπ hleft
    a L hplane σ hlocal' (C / (k : ℝ)) ((k : ℝ) * G) (div_pos hC hkR) hg' hlower' hdiam'
    u Ku hu z hz hdiff δ A (fun j => (k : ℝ) ^ 2 * δ j ^ 3) hδ hA hosc'
    (scaled_cubic_oscillation_ratio_tendsto δ hδ hδlim k) W hW
    (fun H j => (hdata H j).1) (fun H => (k : ℝ) * B₀ H) (fun H => (k : ℝ) ^ 2 * E₀ H)
    (fun H j => (hdata H j).2.1) (fun H j => (hdata H j).2.2.1)
    (fun H j => (hdata H j).2.2.2) N hN ((k : ℝ) * D) b hb0 hb2 hlast
    (dyadic_source_moments_smul_nnreal (p + 1) μ (e 0) u δ N D b hsource k)
  refine ⟨ρ, hρ, c, M, fun H => ?_⟩
  exact tendsto_setIntegral_of_positive_nnreal_smul (fun j => μ (ρ j))
    (boundedProjectionRegion π (e 0) K H)
    (fun j x => (u (ρ j) x / δ (ρ j) - ambientAffineHeight a L c M x) ^ 2)
    k hk (hstrong H)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_NormalCommonAffineStrongLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous affine limits of normal coordinates

Uniform source-energy bounds and a positive planar weak limit yield local strong convergence
of each normalized normal coordinate to an affine height. Stability under further extraction
allows a finite common subsequence to realize all normal-coordinate limits on every bounded
projection region at once.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_normal_common_affine_strong_limit {p q d : ℕ}
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (hplane : e = affinePlaneSection 0 L)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (ν : Measure (Ambient d)) (hlocal : CompactTestConvergence μ ν)
    (t : ℝ) (ht : 0 < t) (hν : ν = ENNReal.ofReal t • coordinatePlaneMeasure e)
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (a : ℕ → Ambient d) (ha : Tendsto a atTop (𝓝 0))
    (N : ℕ → Ambient q →ₗᵢ[ℝ] Ambient d)
    (δ A : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3))
    (T : ℕ → ℕ) (hT : Tendsto T atTop atTop) (D b : ℝ) (hb1 : 1 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ T j)⁻¹ / δ j) atTop (𝓝 0))
    (hsource : ∀ i j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), normalCoordinate (a j) (N j) i x ^ 2 ∂μ j) ≤
        δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ c : Fin q → ℝ,
      ∃ M : Fin q → Ambient (p + 1) →L[ℝ] ℝ, ∀ i H,
        Tendsto (fun j => ∫ x,
          (normalCoordinate (a (ρ j)) (N (ρ j)) i x / δ (ρ j) -
            ambientAffineHeight 0 L (c i) (M i) x) ^ 2
          ∂(μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)) atTop (𝓝 0) := by
  classical
  have he0 : e 0 = 0 := by simp [hplane, affinePlaneSection]
  obtain ⟨W, _, hW⟩ := normalCoordinates_uniform_center_bound a ha N
  have hball := normal_frame_source_data_on_ball p C G μ hg hC
    (fun j r hr => hlower j 0 (hzero j) r hr) hdiam a ha N
    δ A hδ hδlim hA hosc T hT D b hb1 hb2 hlast hsource
  let P : Fin q → (ℕ → ℕ) → Prop := fun i ρ =>
    ∃ c : ℝ, ∃ M : Ambient (p + 1) →L[ℝ] ℝ, ∀ H,
      Tendsto (fun j => ∫ x,
        (normalCoordinate (a (ρ j)) (N (ρ j)) i x / δ (ρ j) - ambientAffineHeight 0 L c M x) ^ 2
        ∂(μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)) atTop (𝓝 0)
  have hextract : ∀ i ρ, StrictMono ρ → ∃ σ : ℕ → ℕ, StrictMono σ ∧ P i (ρ ∘ σ) := by
    intro i ρ hρ
    obtain ⟨B, E, hdata⟩ := normalized_region_data_of_ball_data (p + 1) μ
      (fun j x => normalCoordinate (a j) (N j) i x / δ j) 0 (hball i) π K
    have hdata' (H j : ℕ) := (hdata H).2.2 (ρ j)
    have hlocal' : CompactTestConvergence (fun j => μ (ρ j)) ν :=
      fun g => (hlocal g).comp hρ.tendsto_atTop
    obtain ⟨σ, hσ, c, M, hs⟩ := exists_common_affine_strong_limit_of_positive_density p e π K Q
      he hπ hleft 0 L hplane (fun j => μ (ρ j)) ν hlocal' t ht hν C G hC
      (fun j => hg (ρ j)) (fun j => hlower (ρ j))
      (fun r hr => hρ.tendsto_atTop.eventually (hdiam r hr))
      (fun j => normalCoordinate (a (ρ j)) (N (ρ j)) i) 1
      (fun j => normalCoordinate_lipschitz (a (ρ j)) (N (ρ j)) i)
      (fun j => normalDirection (N (ρ j)) i)
      (fun j => (normalDirection_norm (N (ρ j)) i).le)
      (fun j => normalCoordinate_difference (a (ρ j)) (N (ρ j)) i)
      (fun j => δ (ρ j)) (fun j => A (ρ j)) (fun j => hδ (ρ j))
      (hδlim.comp hρ.tendsto_atTop) (hA.comp hρ.tendsto_atTop)
      (fun j => by simpa only [he0] using! hosc (ρ j)) W
      (fun j => by simpa only [he0] using! hW (ρ j) i)
      (fun H j => by simpa only [he0] using! (hdata' H j).1) B E
      (fun H j => by simpa only [he0] using! (hdata' H j).2.1)
      (fun H j => by simpa only [he0] using! (hdata' H j).2.2.1)
      (fun H j => by simpa only [he0] using! (hdata' H j).2.2.2)
      (fun j => T (ρ j)) (hT.comp hρ.tendsto_atTop) D b (zero_le_one.trans hb1) hb2
      (hlast.comp hρ.tendsto_atTop)
      (fun j l hl => by simpa only [he0] using! hsource i (ρ j) l hl)
    refine ⟨σ, hσ, c, M, ?_⟩
    simpa only [he0, Function.comp_apply] using! hs
  have hstable : ∀ i ρ σ, P i ρ → StrictMono σ → P i (ρ ∘ σ) := by
    intro i ρ σ hP hσ
    obtain ⟨c, M, hs⟩ := hP
    exact ⟨c, M, fun H => (hs H).comp hσ.tendsto_atTop⟩
  obtain ⟨ρ, hρ, hs⟩ := exists_finite_common_subsequence P hextract hstable
  choose c M hM using hs
  exact ⟨ρ, hρ, c, M, hM⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_DyadicNormalAffineLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Affine limits of dyadic normal heights

A flat-measure subsequence supplies positive planar density and convergent tangent
frames. A further common subsequence makes every normalized normal coordinate
converge strongly to an affine height on bounded projection regions, retaining
the frame decomposition and the weak measure limit.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_dyadic_normal_affine_limit {p d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane (p + 1) (S j))
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (p + 1 + 2))
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3))
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
    (hδpos : ∀ j, 0 < δ j) (hb1 : 1 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ T j)⁻¹ / δ j) atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d), ∃ t : ℝ, 0 < t ∧
      ∃ a : ℕ → Ambient d, ∃ L : ℕ → Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
      ∃ N : ℕ → Ambient (d - (p + 1)) →ₗᵢ[ℝ] Ambient d,
      ∃ Llim : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
        IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
        CompactTestConvergence (fun j => μ (ρ j)) ν ∧
        ν = ENNReal.ofReal t • (volume : Measure (Ambient (p + 1))).map Llim ∧
        Tendsto a atTop (𝓝 0) ∧
        Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) ∧
        (∀ j, a j ∈ S (ρ j)) ∧ (∀ j, (L j).toLinearMap.range = (S (ρ j)).direction) ∧
        (∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0) ∧
        (∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
          N j ((N j).toContinuousLinearMap.adjoint y) = y) ∧
        (∀ j x, infDist x (S (ρ j) : Set (Ambient d)) =
          ‖(N j).toContinuousLinearMap.adjoint (x - a j)‖) ∧
        ∃ c : Fin (d - (p + 1)) → ℝ,
          ∃ B : Fin (d - (p + 1)) → Ambient (p + 1) →L[ℝ] ℝ, ∀ i H,
            Tendsto (fun j => ∫ x,
              (normalCoordinate (a j) (N j) i x / δ (ρ j) -
                ambientAffineHeight 0 Llim (c i) (B i) x) ^ 2
              ∂(μ (ρ j)).restrict
                (boundedProjectionRegion (affinePlaneCoordinates 0 Llim) 0
                  ((Fintype.card (Fin (p + 1)) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal) H))
              atTop (𝓝 0) := by
  obtain ⟨ρ, hρ, ν, a, L, N, Llim, hfinite, hne, hweak, _, _, _, _,
    hdensity, ha, hLlim, hcenter, hL, horth, hsplit, hdist, _, hsource, _, _, _⟩ :=
    exists_dyadic_flat_measure_limit_with_energy μ C G hC hg hlower hdiam hzero
      S hS δ T hδ hT M b hmoment A hA hosc D hB hδpos hb1 hb2 hlast
  obtain ⟨f, _, _, _, t, ht, _, _, _, hν⟩ := hdensity
  have hplane : coordinatePlaneMeasure (affinePlaneSection 0 Llim) =
      (volume : Measure (Ambient (p + 1))).map Llim := by
    simpa only [zero_add] using! coordinatePlaneMeasure_affine_eq_map (0 : Ambient d) Llim
  have hν' : ν = ENNReal.ofReal t • coordinatePlaneMeasure (affinePlaneSection 0 Llim) := by
    rw [hplane]
    exact hν
  obtain ⟨τ, hτ, c, B, hstrong⟩ := exists_normal_common_affine_strong_limit
    (affinePlaneSection 0 Llim) (affinePlaneCoordinates 0 Llim)
    ((Fintype.card (Fin (p + 1)) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal)
    ‖Llim.toContinuousLinearMap.adjoint‖₊ (affinePlaneSection_lipschitz 0 Llim)
    (affinePlaneCoordinates_lipschitz 0 Llim) (affinePlaneCoordinates_leftInverse 0 Llim)
    Llim rfl (fun j => μ (ρ j)) ν hweak t ht hν' C G hC
    (fun j => hg (ρ j)) (fun j => hlower (ρ j))
    (fun r hr => hρ.tendsto_atTop.eventually (hdiam r hr)) (fun j => hzero (ρ j))
    a ha N (fun j => δ (ρ j)) (fun j => A (ρ j)) (fun j => hδpos (ρ j))
    (hδ.comp hρ.tendsto_atTop) (hA.comp hρ.tendsto_atTop) (fun j => hosc (ρ j))
    (fun j => T (ρ j)) (hT.comp hρ.tendsto_atTop) M b hb1 hb2
    (hlast.comp hρ.tendsto_atTop) hsource
  refine ⟨ρ ∘ τ, hρ.comp hτ, ν, t, ht, a ∘ τ, L ∘ τ, N ∘ τ, Llim, hfinite, hne,
    ?_, hν, ha.comp hτ.tendsto_atTop, hLlim.comp hτ.tendsto_atTop,
    (fun j => hcenter (τ j)), (fun j => hL (τ j)),
    (fun j => horth (τ j)), (fun j => hsplit (τ j)), (fun j => hdist (τ j)), c, B, hstrong⟩
  intro g
  exact (hweak g).comp hτ.tendsto_atTop

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_DyadicSourceExcessLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vanishing normalized excess along dyadic source limits

The common affine limits of normal coordinates determine improved approximating planes.
Dyadic source moments provide uniform local second-moment bounds, allowing the normal-frame
excess estimate to show that squared excess divided by the original scale squared tends to zero
along one subsequence at every nonnegative radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_dyadic_source_excess_limit_oai {p d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane (p + 1) (S j))
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (p + 1 + 2))
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3))
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
    (hδpos : ∀ j, 0 < δ j) (hb1 : 1 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ T j)⁻¹ / δ j) atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ r : ℝ, 0 ≤ r →
      Tendsto (fun j => squaredExcess (p + 1) (μ (ρ j)) 0 r / δ (ρ j) ^ 2) atTop (𝓝 0) := by
  classical
  obtain ⟨ρ, hρ, _, _, _, a, L, N, Llim, _, _, _, _, _, _, _, _, horth, hsplit, hdist,
    c, B, hstrong⟩ := exists_dyadic_normal_affine_limit μ C G hC hg hlower hdiam hzero
      S hS δ T hδ hT M b hmoment A hA hosc D hB hδpos hb1 hb2 hlast
  let K : ℝ≥0 := ((Fintype.card (Fin (p + 1)) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal)
  let π := affinePlaneCoordinates (0 : Ambient d) Llim
  have he0 : affinePlaneSection (0 : Ambient d) Llim 0 = 0 := by simp [affinePlaneSection]
  have hsource (i : Fin (d - (p + 1))) (j l : ℕ) (hl : l ≤ T (ρ j)) :
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), normalCoordinate (a j) (N j) i x ^ 2 ∂μ (ρ j)) ≤
        δ (ρ j) ^ 2 * M * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2 :=
    normalCoordinate_dyadic_source_bound (μ (ρ j)) G (hg (ρ j))
      (S (ρ j)) (hS (ρ j)).1 (a j) (N j) (hdist j) M (δ (ρ j)) b l (hmoment (ρ j) l hl) i
  have hdata : ∀ i : Fin (d - (p + 1)), ∀ H : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ j,
      MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
        ((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)) ∧
      (∫ x in boundedProjectionRegion π 0 K H,
        (normalCoordinate (a j) (N j) i x / δ (ρ j)) ^ 2 ∂μ (ρ j)) ≤ B := by
    intro i H
    obtain ⟨B, hB, hb⟩ := source_normalized_second_moments_on_ball (p + 1) G (fun j => μ (ρ j))
      (fun j => hg (ρ j)) (fun j => normalCoordinate (a j) (N j) i) 1
      (fun j => normalCoordinate_lipschitz (a j) (N j) i) 0 (fun j => δ (ρ j))
      (fun j => hδpos (ρ j)) (fun j => T (ρ j)) (hT.comp hρ.tendsto_atTop)
      M b (hsource i) (planeBoxOuterRadius K H) (planeBoxOuterRadius_pos K H)
    refine ⟨B, hB, fun j => ?_⟩
    have hs : boundedProjectionRegion π 0 K H ⊆ ball 0 (planeBoxOuterRadius K H) := inter_subset_right
    have hμ := Measure.restrict_mono (μ := μ (ρ j)) hs le_rfl
    exact ⟨MemLp.mono_measure hμ (hb j).1,
      (integral_mono_measure hμ
        (Eventually.of_forall fun x => sq_nonneg (normalCoordinate (a j) (N j) i x / δ (ρ j)))
        (hb j).1.integrable_sq).trans (hb j).2⟩
  choose B₀ hB₀ hdata₀ using hdata
  let Bound : ℕ → ℝ := fun H => ∑ i, B₀ i H
  have hbound (i : Fin (d - (p + 1))) (H : ℕ) : B₀ i H ≤ Bound H :=
    Finset.single_le_sum (fun j _ => hB₀ j H) (Finset.mem_univ i)
  have hlim := normal_frame_excess_of_common_affine_coordinates
    (affinePlaneSection 0 Llim) π K ‖Llim.toContinuousLinearMap.adjoint‖₊
    (affinePlaneCoordinates_lipschitz 0 Llim) (affinePlaneCoordinates_leftInverse 0 Llim)
    0 Llim (fun j => μ (ρ j)) a L N horth hsplit (fun j => δ (ρ j))
    (fun j => hδpos (ρ j)) (hδ.comp hρ.tendsto_atTop)
    (fun i H j => by simpa only [he0] using! (hdata₀ i H j).1) Bound
    (fun i H j => by simpa only [he0] using! ((hdata₀ i H j).2.trans (hbound i H)))
    c B (by simpa only [he0] using! hstrong)
  exact ⟨ρ, hρ, by simpa only [he0] using! hlim⟩

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.exists_dyadic_source_excess_limit_oai := @OAI.RieszRectifiability.exists_dyadic_source_excess_limit_oai
