-- Prove2me | solution 1 for OAI.Falconer.exists_policy_positive_common_budgets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:18:15.895991+00:00
-- url     : https://prove2.me/submissions/713b34b7-e64a-4f7f-9869-bd135b060e95

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_exists_policy_prefix_common_budgets

section
-- module Solutions.OAIQ088_FD.Falconer_Frostman_FrostmanProfileCells
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Metric
open scoped ENNReal

theorem fixed_constant_absorbed {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C ≤ ((2:ℝ)^N)^lam := by
  have hb : 1 < (2:ℝ)^lam := Real.one_lt_rpow (by norm_num) hlam
  obtain ⟨N₀,hN₀⟩ := pow_unbounded_of_one_lt C hb
  refine ⟨N₀,fun N hN => ?_⟩
  have hh := hN₀.le.trans (pow_le_pow_right₀ hb.le hN)
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm,
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hh
  exact hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularUniformAbsorption
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem fixed_linear_subpower (C : ℝ) (hC : 0 ≤ C) {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C*(1+2*(N:ℝ)) ≤ ((2:ℝ)^N)^e := by
  obtain ⟨N₁,hN₁⟩ := fixed_constant_absorbed (half_pos he) C
  obtain ⟨N₂,hN₂⟩ := fixed_polynomial_subpower 1 (half_pos he)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN
  have hc := hN₁ N ((le_max_left _ _).trans hN)
  have hp := hN₂ N ((le_max_right _ _).trans hN)
  simp only [pow_one] at hp
  have hlin : 1+2*(N:ℝ) ≤ ((2:ℝ)^N)^(e/2) := by
    have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
    linarith
  calc
    _ ≤ C*((2:ℝ)^N)^(e/2) := mul_le_mul_of_nonneg_left hlin hC
    _ ≤ ((2:ℝ)^N)^(e/2)*((2:ℝ)^N)^(e/2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SmoothReciprocal
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth reciprocal of a nonstationary phase derivative

The reciprocal is extended smoothly across zero by a scalar bump. At a
point where the denominator is bounded below, its derivative bounds
depend only on the normalized derivatives of that denominator.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem smoothReciprocal_eq {τ u : ℝ} (hτ : 0 < τ) (hu : τ ≤ |u|) :
    u * smoothReciprocal τ hτ u = 1 := by
  have hb : PlanarFalconer.sineZeroCutoff τ hτ u = 0 :=
    (PlanarFalconer.sineZeroCutoff τ hτ).zero_of_le_dist
      (by simpa [PlanarFalconer.sineZeroCutoff, Real.dist_eq] using hu)
  have hune : u ≠ 0 := by intro he; simp [he] at hu; linarith
  simp [smoothReciprocal,hb,hune]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_AllDimensionalGraphGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Geometry of the retained graph in arbitrary dimension

The graph tests use orthogonal distance to a line and one scalar longitudinal
constraint. Each longitudinal constraint is in the unknown endpoint's own
cap direction. In particular these bounds do not divide by the angle between
the two endpoint directions.
-/

namespace Falconer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Moving a unit direction changes the perpendicular test by at most twice
its angular displacement times the size of the tested vector. -/
theorem perpendicularPart_direction_error {w z : E} (hw : ‖w‖ = 1) (hz : ‖z‖ = 1)
    (v : E) :
    ‖perpendicularPart w v - perpendicularPart z v‖ ≤ 2 * ‖w-z‖ * ‖v‖ := by
  have he : perpendicularPart w v - perpendicularPart z v =
      inner ℝ z v • (z-w) + inner ℝ (z-w) v • w := by
    simp only [perpendicularPart, inner_sub_left, sub_smul, smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖inner ℝ z v • (z-w)‖ + ‖inner ℝ (z-w) v • w‖ := norm_add_le _ _
    _ = |inner ℝ z v| * ‖z-w‖ + |inner ℝ (z-w) v| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hw, mul_one]
    _ ≤ (‖z‖ * ‖v‖) * ‖z-w‖ + (‖z-w‖ * ‖v‖) := by
      exact add_le_add (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm z v)
        (norm_nonneg _)) (abs_real_inner_le_norm (z-w) v)
    _ = _ := by rw [hz, one_mul, norm_sub_rev z w]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PolicyDescriptors
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem policyDescriptor_origin (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    {d : PolicyDescriptor} (hd : d ∈ policyDescriptorList A N q a t) :
    ∃ b u : ℕ, a ≤ b ∧ u ≤ t ∧ b+100*q < u ∧
      descriptorAnchor d = policyDepth A N q b u ∧ 0 < descriptorLength d ∧
      b ≤ descriptorAnchor d-descriptorLength d ∧ descriptorAnchor d+descriptorLength d ≤ u := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,hb,hu,hwide⟩ := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  exact ⟨z.1,z.2,hb,hu,hwide,originDescriptor_anchor A hd,
    originDescriptor_length A hq huN hwide hd⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapDenominator
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform bounds for the cap partition denominator

Only centers whose closed cap contains the point contribute to a derivative.
The proved local packing bound therefore controls the sum independently of
the total number of caps.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem capDenominator_ge_one {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (w : Sphere d) :
    1 ≤ capDenominator δ hδ S w := by
  obtain ⟨c,hc,hwc⟩ := hcover w
  have hval : capBump δ hδ c w = 1 :=
    (capBump δ hδ c).one_of_mem_closedBall (Metric.mem_closedBall.mpr hwc)
  calc
    1 = capBump δ hδ c w := hval.symm
    _ ≤ capDenominator δ hδ S w :=
      Finset.single_le_sum (fun c _ => (capBump δ hδ c).nonneg) hc

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapReciprocal
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivatives of the cap normalization factor -/

namespace Falconer
open Set
open scoped ContDiff Topology

theorem capDenominator_mul_reciprocal {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (w : Sphere d) :
    capDenominator δ hδ S w * capReciprocal δ hδ S w = 1 := by
  exact smoothReciprocal_eq zero_lt_one
    ((capDenominator_ge_one hδ S hcover w).trans (le_abs_self _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_NormalizedCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The normalized cap partition and its uniform derivative bounds

The normalization uses the same fixed smooth reciprocal for all radii.
On the sphere the covering bound makes it the exact reciprocal of the
positive bump sum.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem normalizedCap_properties {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) :
    (∀ w : Sphere d, ∑ c ∈ S, normalizedCap δ hδ S c w = 1) ∧
    (∀ c ∈ S, ∀ w : Sphere d, 0 ≤ normalizedCap δ hδ S c w ∧
      normalizedCap δ hδ S c w ≤ 1) ∧
    (∀ c ∈ S, ∀ x : Space d, normalizedCap δ hδ S c x ≠ 0 → ‖x-(c : Space d)‖ ≤ δ) := by
  have hrec (w : Sphere d) : capReciprocal δ hδ S w = (capDenominator δ hδ S w)⁻¹ := by
    have hg : capDenominator δ hδ S w ≠ 0 :=
      ne_of_gt (zero_lt_one.trans_le (capDenominator_ge_one hδ S hcover w))
    apply mul_left_cancel₀ hg
    rw [capDenominator_mul_reciprocal hδ S hcover w,mul_inv_cancel₀ hg]
  refine ⟨?_,?_,?_⟩
  · intro w
    simpa only [normalizedCap,← Finset.sum_mul,capDenominator] using
      capDenominator_mul_reciprocal hδ S hcover w
  · intro c hc w
    have hb : capBump δ hδ c w ≤ capDenominator δ hδ S w :=
      Finset.single_le_sum (fun c _ => (capBump δ hδ c).nonneg) hc
    have hg : 0 < capDenominator δ hδ S w :=
      zero_lt_one.trans_le (capDenominator_ge_one hδ S hcover w)
    simp only [normalizedCap,hrec]
    exact ⟨mul_nonneg (capBump δ hδ c).nonneg (inv_nonneg.mpr hg.le),
      (mul_inv_le_iff₀ hg).mpr (by simpa only [one_mul] using hb)⟩
  · intro c _ x hx
    have hb : capBump δ hδ c x ≠ 0 := (mul_ne_zero_iff.mp hx).1
    have hm : x ∈ Metric.ball (c : Space d) δ := by
      change x ∈ Metric.ball (c : Space d) (capBump δ hδ c).rOut
      rw [← (capBump δ hδ c).support_eq]
      exact hb
    exact (mem_ball_iff_norm.mp hm).le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereNormalization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable sphere normalization with a fixed value at zero -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

theorem normalizeToSphere_measurable (w₀ : Sphere d) :
    Measurable (normalizeToSphere w₀) := by
  apply Measurable.subtype_mk
  exact Measurable.ite (by simp)
    measurable_const (measurable_id.norm.inv.smul measurable_id)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic cubes in the ambient dimension of the manuscript

Half-open cubes partition without boundary overlaps. Their centers and
Euclidean diameter bounds use the same original ambient coordinates as the
distance measure.
-/

namespace Falconer
open Set MeasureTheory

theorem DyadicCube.measurable {d : ℕ} (Q : DyadicCube d) : MeasurableSet Q.carrier := by
  simp only [carrier, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable).inter
    (measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SmoothMask
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth angular masks from buffered good sets

A finite subcollection of the normalized cap partition gives a cutoff
supported inside a prescribed set. It equals one wherever a closed ball
of twice the cap radius lies in that set. No regularity of the set is
needed for this finite construction.
-/

namespace Falconer
open Set
open scoped ContDiff
attribute [local instance] Classical.propDecidable

theorem capCutoffAmbient_properties {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (U : Set (Sphere d)) :
    (∀ w : Sphere d, 0 ≤ capCutoffAmbient δ hδ S U w ∧ capCutoffAmbient δ hδ S U w ≤ 1) ∧
    (∀ w : Sphere d, capCutoffAmbient δ hδ S U w ≠ 0 → w ∈ U) ∧
    (∀ w : Sphere d, (∀ z : Sphere d, dist z w ≤ 2*δ → z ∈ U) →
      capCutoffAmbient δ hδ S U w = 1) := by
  obtain ⟨hpart,hbounds,hsupport⟩ := normalizedCap_properties hδ S hcover
  have hsub : cutoffCapCenters δ S U ⊆ S := Finset.filter_subset _ _
  refine ⟨?_,?_,?_⟩
  · intro w
    constructor
    · exact Finset.sum_nonneg (fun c hc => (hbounds c (hsub hc) w).1)
    · apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun c hc _ => (hbounds c hc w).1))
      exact (hpart w).le
  · intro w hw
    obtain ⟨c,hc,hcw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    have hsel := (Finset.mem_filter.mp hc).2
    apply hsel w
    exact hsupport c (hsub hc) w hcw
  · intro w hcore
    rw [← hpart w]
    apply Finset.sum_subset hsub
    intro c hc hnot
    by_contra hn
    have hdist : dist w c ≤ δ := hsupport c hc w hn
    apply hnot
    apply Finset.mem_filter.mpr ⟨hc,?_⟩
    intro z hz
    apply hcore z
    calc
      dist z w ≤ dist z c+dist c w := dist_triangle _ _ _
      _ ≤ δ+δ := add_le_add hz (by simpa only [dist_comm] using hdist)
      _ = 2*δ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AnchoredMasks
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Angular masks attached to actual dyadic anchor cells

The spatial dependence is a finite Borel choice of the anchor cell.
On every descendant of an anchor cell, its angular mask is exactly
constant in the spatial variable.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
attribute [local instance] Classical.propDecidable

theorem anchoredMask_on_cell {d n : ℕ} (Q : DyadicCube d)
    (F : List (Fin d → Bool) → Sphere d → ℝ) (p : List (Fin d → Bool)) (hp : p.length = n)
    {x : Space d} (hx : x ∈ (Q.descendant p).carrier) (w : Sphere d) :
    anchoredMask Q n F x w = F p w := by
  unfold anchoredMask
  rw [Finset.sum_eq_single p]
  · simp [hx]
  · intro q hq hqp
    have hdis := Q.descendants_disjoint ((mem_cubePaths d n q).mp hq |>.trans hp.symm) hqp
    have hn : x ∉ (Q.descendant q).carrier := fun hq => Set.disjoint_left.mp hdis hq hx
    simp [hn]
  · exact fun hn => (hn ((mem_cubePaths d n p).mpr hp)).elim

theorem anchoredMask_off_parent {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    (F : List (Fin d → Bool) → Sphere d → ℝ) {x : Space d} (hx : x ∉ Q.carrier)
    (w : Sphere d) : anchoredMask Q n F x w = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  have hn : x ∉ (Q.descendant p).carrier := fun h => hx (Q.descendant_subset p h)
  simp [hn]

theorem anchoredMask_bounds {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    (F : List (Fin d → Bool) → Sphere d → ℝ)
    (hF : ∀ p ∈ cubePaths d n, ∀ w, 0 ≤ F p w ∧ F p w ≤ 1)
    (x : Space d) (w : Sphere d) :
    0 ≤ anchoredMask Q n F x w ∧ anchoredMask Q n F x w ≤ 1 := by
  by_cases hx : x ∈ Q.carrier
  · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth n hx
    rw [anchoredMask_on_cell Q F p ((mem_cubePaths d n p).mp hp) hxp]
    exact hF p hp w
  · rw [anchoredMask_off_parent Q n F hx]
    norm_num

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AnchoredBufferedMasks
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Buffered masks on the original spatial anchor cells

These masks are jointly measurable, bounded between zero and one, smooth
in every adapted angular chart, and constant in the spatial variable on
all descendants of a reached anchor. Their angular derivative constants
are independent of the number of anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem anchoredBufferedMask_bounds {d : ℕ} (Q : DyadicCube d) (g : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2)
    (U : List (Fin d → Bool) → Set (Sphere d)) (x : Space d) (w : Sphere d) :
    0 ≤ anchoredBufferedMask Q g δ hδ S U x w ∧
      anchoredBufferedMask Q g δ hδ S U x w ≤ 1 :=
  anchoredMask_bounds Q g _ (fun p _ => (capCutoffAmbient_properties hδ S hcover (U p)).1) x w

theorem anchoredBufferedMask_support {d g : ℕ} (Q : DyadicCube d)
    {δ : ℝ} (hδ : 0 < δ) (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2)
    (U : List (Fin d → Bool) → Set (Sphere d))
    (p : List (Fin d → Bool)) (hp : p.length = g) {x : Space d}
    (hx : x ∈ (Q.descendant p).carrier) (w : Sphere d)
    (hw : anchoredBufferedMask Q g δ hδ S U x w ≠ 0) : w ∈ U p := by
  apply (capCutoffAmbient_properties hδ S hcover (U p)).2.1 w
  simpa only [anchoredBufferedMask,anchoredMask_on_cell Q _ p hp hx] using hw

theorem anchoredBufferedMask_core {d g : ℕ} (Q : DyadicCube d)
    {δ : ℝ} (hδ : 0 < δ) (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2)
    (U : List (Fin d → Bool) → Set (Sphere d))
    (p : List (Fin d → Bool)) (hp : p.length = g) {x : Space d}
    (hx : x ∈ (Q.descendant p).carrier) (w : Sphere d)
    (hw : ∀ z : Sphere d, dist z w ≤ 2*δ → z ∈ U p) :
    anchoredBufferedMask Q g δ hδ S U x w = 1 := by
  rw [anchoredBufferedMask,anchoredMask_on_cell Q _ p hp hx]
  exact (capCutoffAmbient_properties hδ S hcover (U p)).2.2 w hw

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DistanceFourierDifference
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory ComplexConjugate

theorem integral_distanceDifferenceMeasure (μ : Measure ℝ) (F : ℝ → ℂ)
    (hF : StronglyMeasurable F) :
    (∫ s, F s ∂distanceDifferenceMeasure μ) = ∫ z, F (z.1-z.2) ∂μ.prod μ :=
  integral_map_of_stronglyMeasurable (by fun_prop) hF

theorem charFun_distanceDifferenceMeasure (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℝ) :
    charFun (distanceDifferenceMeasure μ) r = (‖charFun μ r‖^2:ℂ) := by
  rw [charFun_apply_real,integral_distanceDifferenceMeasure μ _ (by fun_prop)]
  have he : (fun z : ℝ × ℝ => Complex.exp ((r*(z.1-z.2):ℝ)*Complex.I)) =
      fun z => Complex.exp ((r*z.1:ℝ)*Complex.I) *
        conj (Complex.exp ((r*z.2:ℝ)*Complex.I)) := by
    funext z
    rw [← Complex.exp_conj,← Complex.exp_add]
    congr 1
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_sub,Complex.ofReal_mul]
    ring
  simp only [Complex.ofReal_mul] at he
  rw [he,integral_prod_mul (fun x : ℝ => Complex.exp ((r:ℂ)*x*Complex.I))
    (fun y : ℝ => conj (Complex.exp ((r:ℂ)*y*Complex.I))),integral_conj,← charFun_apply_real,Complex.mul_conj]
  exact_mod_cast Complex.normSq_eq_norm_sq (charFun μ r)

theorem integral_charFun_scale_swap (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : ℝ) :
    (∫ s, charFun μ (A*s) ∂ν) = ∫ r, charFun ν (A*r) ∂μ := by
  simp only [charFun_apply_real]
  rw [integral_integral_swap]
  · apply integral_congr_ae
    filter_upwards with r
    apply integral_congr_ae
    filter_upwards with s
    congr 2
    push_cast
    ring
  · exact (integrable_const (1:ℝ)).mono (by fun_prop)
      (by filter_upwards with z; simp [Function.uncurry,Complex.norm_exp])

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DistanceSincKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem distanceSincKernel_nonneg (u s : ℝ) : 0 ≤ distanceSincKernel u s := sq_nonneg _

theorem distanceSincKernel_le_one (u s : ℝ) : distanceSincKernel u s ≤ 1 := by
  have h := Real.abs_sinc_le_one (u*s)
  dsimp [distanceSincKernel]
  exact (sq_abs _).symm.trans_le ((pow_le_pow_left₀ (abs_nonneg _) h 2).trans_eq (by norm_num))

theorem continuous_distanceSincKernel (u : ℝ) : Continuous (distanceSincKernel u) :=
  (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2

theorem exists_distanceSincKernel : ∃ u : ℝ, 0 < u ∧ 2*u ≤ 1 ∧
    ∀ s : ℝ, |s| ≤ 100 → (1/4:ℝ) ≤ distanceSincKernel u s := by
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp
    Real.continuous_sinc.continuousAt (1/2:ℝ) (by norm_num)
  let u := min (δ/201) (1/4:ℝ)
  have hu : 0 < u := lt_min (by positivity) (by norm_num)
  refine ⟨u,hu,by have := min_le_right (δ/201) (1/4:ℝ); dsimp [u]; linarith,?_⟩
  intro s hs
  have hb : |u*s| < δ := by
    rw [abs_mul,abs_of_pos hu]
    have h₁ := mul_le_mul_of_nonneg_left hs hu.le
    have h₂ := min_le_left (δ/201) (1/4:ℝ)
    dsimp [u] at h₁ ⊢
    nlinarith
  have hc := hclose (show dist (u*s) 0 < δ by simpa [Real.dist_eq] using hb)
  rw [Real.dist_eq,Real.sinc_zero] at hc
  have hp : 1/2 < Real.sinc (u*s) := by have := (abs_lt.mp hc).1; linarith
  dsimp [distanceSincKernel]
  nlinarith

theorem interval_exp_eq_sinc (u s : ℝ) :
    (∫ r in -u..u, Complex.exp ((r*s:ℝ)*Complex.I)) =
      ((2*u*Real.sinc (u*s):ℝ):ℂ) := by
  by_cases hs : s = 0
  · simp [hs]
    ring
  have h := intervalIntegral.integral_comp_mul_right
    (fun t : ℝ => Complex.exp (t*Complex.I)) (a := -u) (b := u) hs
  rw [neg_mul,integral_exp_mul_I_eq_sinc] at h
  rw [h]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  have hs' : (s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  field_simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DistanceFrequencyBox
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem distanceFrequencyBox_mass {u : ℝ} (hu : 0 ≤ u) :
    distanceFrequencyBox u univ = ENNReal.ofReal (2*u) := by
  simp only [distanceFrequencyBox,Measure.restrict_apply_univ,Real.volume_Ioc]
  apply (ENNReal.ofReal_eq_ofReal_iff (sub_nonneg.mpr (neg_le_self hu))
    (mul_nonneg (by norm_num) hu)).2
  ring

theorem distanceFrequencyBox_charFun {u : ℝ} (hu : 0 ≤ u) (s : ℝ) :
    charFun (distanceFrequencyBox u) s = ((2*u*Real.sinc (u*s):ℝ):ℂ) := by
  rw [charFun_apply_real]
  change (∫ r in Ioc (-u) u, Complex.exp ((s:ℂ)*r*Complex.I)) = _
  rw [← intervalIntegral.integral_of_le (by linarith : -u ≤ u)]
  simpa only [Complex.ofReal_mul,mul_comm (s:ℂ)] using interval_exp_eq_sinc u s

theorem distanceFrequencyBox_difference_charFun {u : ℝ} (hu : 0 ≤ u) (s : ℝ) :
    charFun (distanceDifferenceMeasure (distanceFrequencyBox u)) s =
      (((2*u)^2 * distanceSincKernel u s:ℝ):ℂ) := by
  rw [charFun_distanceDifferenceMeasure,distanceFrequencyBox_charFun hu,
    Complex.norm_real,Real.norm_eq_abs,← Complex.ofReal_pow,sq_abs]
  congr 1
  dsimp [distanceSincKernel]
  ring

theorem distanceFrequencyBox_difference_le_volume {u : ℝ} (hu : 0 ≤ u) :
    distanceDifferenceMeasure (distanceFrequencyBox u) ≤ ENNReal.ofReal (2*u) • volume := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [distanceDifferenceMeasure,Measure.map_apply (by fun_prop) hS,
    Measure.prod_apply (hS.preimage (by fun_prop))]
  calc
    _ ≤ ∫⁻ x, volume S ∂distanceFrequencyBox u := by
      apply lintegral_mono
      intro x
      calc
        _ ≤ volume ((fun y : ℝ => x-y) ⁻¹' S) := Measure.restrict_apply_le _ _
        _ = volume S := (volume.measurePreserving_sub_left x).measure_preimage hS.nullMeasurableSet
    _ = _ := by
      rw [lintegral_const,distanceFrequencyBox_mass hu,Measure.smul_apply,smul_eq_mul,mul_comm]

theorem distanceFrequencyBox_difference_supported {u : ℝ} :
    ∀ᵐ s ∂distanceDifferenceMeasure (distanceFrequencyBox u), s ∈ Icc (-2*u) (2*u) := by
  rw [distanceDifferenceMeasure,ae_map_iff (by fun_prop) (by measurability)]
  have hm : ∀ᵐ x ∂distanceFrequencyBox u, x ∈ Ioc (-u) u := ae_restrict_mem measurableSet_Ioc
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hm,
    Measure.quasiMeasurePreserving_snd.ae hm] with z hz₁ hz₂
  exact ⟨by linarith [hz₁.1,hz₂.2],by linarith [hz₁.2,hz₂.1]⟩

theorem distanceFrequencyBox_difference_le_band {u : ℝ} (hu : 0 ≤ u) :
    distanceDifferenceMeasure (distanceFrequencyBox u) ≤
      ENNReal.ofReal (2*u) • volume.restrict (Icc (-2*u) (2*u)) := by
  calc
    _ = (distanceDifferenceMeasure (distanceFrequencyBox u)).restrict (Icc (-2*u) (2*u)) :=
      (Measure.restrict_eq_self_of_ae_mem distanceFrequencyBox_difference_supported).symm
    _ ≤ (ENNReal.ofReal (2*u) • volume).restrict (Icc (-2*u) (2*u)) :=
      Measure.restrict_mono (Subset.refl _) (distanceFrequencyBox_difference_le_volume hu)
    _ = _ := Measure.restrict_smul _ _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DistanceSincSpectralIdentity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem distanceSincKernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (u A : ℝ) :
    Integrable (fun s => distanceSincKernel u (A*s)) μ := by
  apply (integrable_const (1:ℝ)).mono
  · exact ((continuous_distanceSincKernel u).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with s
    rw [Real.norm_eq_abs,abs_of_nonneg (distanceSincKernel_nonneg _ _),norm_one]
    exact distanceSincKernel_le_one _ _

theorem charFun_sq_integrable_finite (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : ℝ) :
    Integrable (fun r => ‖charFun μ (A*r)‖^2) ν := by
  apply (integrable_const ((μ.real univ)^2)).mono
  · exact ((measurable_charFun.comp (measurable_const.mul measurable_id)).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with r
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le _) 2

theorem distanceSincKernel_spectral_identity (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 ≤ u) (A : ℝ) :
    (2*u)^2 * (∫ s, distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) =
      ∫ r, ‖charFun μ (A*r)‖^2 ∂distanceDifferenceMeasure (distanceFrequencyBox u) := by
  have h := integral_charFun_scale_swap
    (distanceDifferenceMeasure (distanceFrequencyBox u)) (distanceDifferenceMeasure μ) A
  simp only [distanceFrequencyBox_difference_charFun hu,charFun_distanceDifferenceMeasure] at h
  have hr : (∫ s, (2*u)^2 * distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) =
      ∫ r, ‖charFun μ (A*r)‖^2 ∂distanceDifferenceMeasure (distanceFrequencyBox u) := by
    apply Complex.ofReal_injective
    simpa only [← Complex.ofReal_pow,integral_complex_ofReal] using h
  rwa [integral_const_mul] at hr

theorem distanceSincKernel_frequency_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) (A : ℝ) :
    (2*u) * (∫ s, distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) ≤
      ∫ r in Icc (-2*u) (2*u), ‖charFun μ (A*r)‖^2 := by
  have hi := charFun_sq_integrable_finite μ (volume.restrict (Icc (-2*u) (2*u))) A
  have hb := integral_mono_measure (distanceFrequencyBox_difference_le_band hu.le)
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun μ (A*r)‖))
    (hi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*u),smul_eq_mul,
    ← distanceSincKernel_spectral_identity μ hu.le A] at hb
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DistanceSincCollision
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem distanceSincKernel_collision_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    {u A : ℝ} (hA : 0 < A)
    (hu : ∀ s : ℝ, |s| ≤ 100 → (1/4:ℝ) ≤ distanceSincKernel u s) :
    ν.real {s : ℝ | |s| ≤ 100/A} ≤ 4 * ∫ s, distanceSincKernel u (A*s) ∂ν := by
  let S : Set ℝ := {s | |s| ≤ 100/A}
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hb := integral_mono ((integrable_const (1/4:ℝ)).indicator hS)
    (distanceSincKernel_integrable ν u A) (show ∀ s, S.indicator (fun _ => (1/4:ℝ)) s ≤
      distanceSincKernel u (A*s) from by
      intro s
      by_cases hs : s ∈ S
      · rw [Set.indicator_of_mem hs]
        apply hu
        rw [abs_mul,abs_of_pos hA]
        have h := (le_div_iff₀ hA).mp hs
        nlinarith
      · rw [Set.indicator_of_notMem hs]
        exact distanceSincKernel_nonneg _ _)
  rw [integral_indicator_const _ hS,smul_eq_mul] at hb
  dsimp [S] at hb
  linarith

theorem integral_scale_Icc (f : ℝ → ℝ) {A u : ℝ} (hA : 0 < A) (hu : 0 ≤ u) :
    A * (∫ r in Icc (-u) u, f (A*r)) = ∫ r in Icc (-A*u) (A*u), f r := by
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -u ≤ u),
    ← intervalIntegral.integral_of_le (by nlinarith : -A*u ≤ A*u)]
  have h := intervalIntegral.smul_integral_comp_mul_left f (a := -u) (b := u) A
  simpa only [smul_eq_mul,mul_neg,neg_mul] using h

theorem distanceSincKernel_scaled_frequency_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u A : ℝ} (hu : 0 < u) (hu₁ : 2*u ≤ 1) (hA : 0 < A) :
    A*(2*u) * (∫ s, distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) ≤
      ∫ r in Icc (-A) A, ‖charFun μ r‖^2 := by
  have h := mul_le_mul_of_nonneg_left (distanceSincKernel_frequency_bound μ hu A) hA.le
  rw [show -2*u = -(2*u) by ring,integral_scale_Icc (fun r => ‖charFun μ r‖^2) hA (by positivity)] at h
  have hs : Icc (-A*(2*u)) (A*(2*u)) ⊆ Icc (-A) A := by
    intro r hr
    constructor <;> nlinarith [hr.1,hr.2]
  have hi : IntegrableOn (fun r => ‖charFun μ r‖^2) (Icc (-A) A) := by
    simpa only [one_mul,IntegrableOn] using charFun_sq_integrable_finite μ (volume.restrict (Icc (-A) A)) 1
  have hb := integral_mono_measure (Measure.restrict_mono hs le_rfl)
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun μ r‖)) hi
  apply le_trans ?_ hb
  simpa only [mul_assoc] using h

theorem finite_measure_distance_collision_fourier : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (A : ℝ), 0 < A →
      A * (μ.prod μ).real {z : ℝ × ℝ | |z.1-z.2| ≤ 100/A} ≤
        C * ∫ r in Icc (-A) A, ‖charFun μ r‖^2 := by
  obtain ⟨u,hu,hu₁,hkernel⟩ := exists_distanceSincKernel
  refine ⟨2/u,by positivity,?_⟩
  intro μ _ A hA
  have hl := distanceSincKernel_collision_bound (distanceDifferenceMeasure μ) hA hkernel
  have hh := distanceSincKernel_scaled_frequency_bound μ hu hu₁ hA
  have he : (distanceDifferenceMeasure μ).real {s : ℝ | |s| ≤ 100/A} =
      (μ.prod μ).real {z : ℝ × ℝ | |z.1-z.2| ≤ 100/A} := by
    simp only [measureReal_def,distanceDifferenceMeasure]
    rw [Measure.map_apply (by fun_prop) (by measurability)]
    rfl
  rw [he] at hl
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hu).mpr
  have h₁ := mul_le_mul_of_nonneg_left hl (show 0 ≤ A*u by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2)
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_AngularTubeCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mean and exceptional mass of a finite original tube count -/

namespace Falconer
open MeasureTheory Set
open scoped ENNReal

theorem angularTubeEvent_measurable {d : ℕ} (v : Space d) (W : ℝ) :
    MeasurableSet (angularTubeEvent v W) := by
  have hc : Continuous (fun w : Sphere d => v-inner ℝ (w:Space d) v • (w:Space d)) :=
    continuous_const.sub ((continuous_subtype_val.inner (𝕜 := ℝ) continuous_const).smul continuous_subtype_val)
  exact measurableSet_le hc.norm.measurable measurable_const

theorem finiteTubeCount_eq_sum {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) (w : Sphere d) :
    (finiteTubeCount S v W w : ℝ≥0∞) =
      ∑ i ∈ S, (angularTubeEvent (v i) W).indicator (fun _ => (1:ℝ≥0∞)) w := by
  classical
  simp only [finiteTubeCount,Finset.natCast_card_filter,Set.indicator_apply]

theorem finiteTubeCount_measurable {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) :
    Measurable (fun w : Sphere d => (finiteTubeCount S v W w : ℝ≥0∞)) := by
  simp_rw [finiteTubeCount_eq_sum]
  exact Finset.measurable_sum S (fun i _ =>
    measurable_const.indicator (angularTubeEvent_measurable (v i) W))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ParallelGood
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal parallel-test good sets and their directional buffer -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal

theorem finiteTubeCount_direction_transfer {d : ℕ} {ι : Type*}
    (S : Finset ι) (v : ι → Space d) {w u : Sphere d}
    {δ M W₀ W₁ : ℝ} (hδ : 0 ≤ δ) (_hM : 0 ≤ M)
    (hclose : dist w u ≤ δ) (hbound : ∀ i ∈ S, ‖v i‖ ≤ M)
    (hwidth : W₁+2*δ*M ≤ W₀) :
    finiteTubeCount S v W₁ u ≤ finiteTubeCount S v W₀ w := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,ht⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨hi,?_⟩
  change ‖perpendicularPart (w:Space d) (v i)‖ ≤ W₀
  have herror := perpendicularPart_direction_error (sphere_norm w) (sphere_norm u) (v i)
  have hdist : ‖(w:Space d)-(u:Space d)‖ ≤ δ := by
    simpa only [Subtype.dist_eq,dist_eq_norm] using hclose
  have hb : 2*‖(w:Space d)-(u:Space d)‖*‖v i‖ ≤ 2*δ*M :=
    mul_le_mul (mul_le_mul_of_nonneg_left hdist (by norm_num)) (hbound i hi)
      (norm_nonneg _) (mul_nonneg (by norm_num) hδ)
  have htri := norm_sub_le_norm_sub_add_norm_sub (perpendicularPart (w:Space d) (v i))
    (perpendicularPart (u:Space d) (v i)) 0
  simp only [sub_zero] at htri
  change ‖perpendicularPart (u:Space d) (v i)‖ ≤ W₁ at ht
  linarith

namespace Regularization
variable {d : ℕ}

theorem parallelGoodSet_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) (W T : ℝ) :
    MeasurableSet (parallelGoodSet Q ρ g p P W T) := by
  classical
  unfold parallelGoodSet
  split_ifs
  · exact measurableSet_le (finiteTubeCount_measurable _ _ _) measurable_const
  · exact MeasurableSet.empty

theorem parallelGoodSet_buffer (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) {W₀ W₁ T δ : ℝ} (hδ : 0 ≤ δ)
    (hwidth : W₁+2*δ*(10*((d:ℝ)+1)/(2:ℝ)^g) ≤ W₀)
    {w u : Sphere d} (hw : w ∈ parallelGoodSet Q ρ g p P W₀ T)
    (hclose : dist w u ≤ δ) : u ∈ parallelGoodSet Q ρ g p P W₁ T := by
  classical
  by_cases hocc : 0 < ρ (Q.descendant P).carrier
  · simp only [parallelGoodSet,ite_eq_left hocc,mem_ofPred_eq] at hw ⊢
    have hc := finiteTubeCount_direction_transfer (parallelTestCells Q ρ g p P)
      (fun c => (Q.descendant c).center-(Q.descendant P).center) hδ
      (by positivity : 0 ≤ 10*((d:ℝ)+1)/(2:ℝ)^g) hclose ?_ hwidth
    · exact (Nat.cast_le.mpr hc).trans hw
    · intro c hc
      have h := (mem_ball.mp (Finset.mem_filter.mp hc).2.2).le
      simpa only [dist_eq_norm] using h
  · simp only [parallelGoodSet,ite_eq_right hocc,mem_empty_iff_false] at hw

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TestWidths
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The width and buffer scales of the all-dimensional tests

These are the exponents 500 and 50 in the all-dimensional test family.
-/

namespace Falconer

theorem angularTestWidth_gap (N : ℕ) (σ : ℝ) {J : ℕ} (hJ : 0 < J) (i n : ℕ) :
    angularTestWidth N σ J i n-angularTestWidth N σ J (i+1) n =
      ((2:ℝ)^N)^(500*σ)/((J:ℝ)*(2:ℝ)^n) := by
  have hj : (J:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hJ.ne'
  simp only [angularTestWidth,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

theorem uniform_angularTestWidth_gap {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) (C : ℝ) (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g n : ℕ, g ≤ n → ∀ i : ℕ,
      angularTestWidth N σ J (i+1) n+
        (C/(2:ℝ)^g)*angularTestRadius N σ (n-g) ≤
      angularTestWidth N σ J i n := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed
    (by positivity : 0 < 450*σ) (C*(J:ℝ))
  refine ⟨N₀,?_⟩
  intro N hN g n hgn i
  have hj : 0 < (J:ℝ) := Nat.cast_pos.mpr hJ
  have hR : 0 < (2:ℝ)^N := by positivity
  have hconst := mul_le_mul_of_nonneg_right (hN₀ N hN)
    (by positivity : 0 ≤ ((2:ℝ)^N)^(50*σ))
  have he : ((2:ℝ)^N)^(450*σ)*((2:ℝ)^N)^(50*σ) =
      ((2:ℝ)^N)^(500*σ) := by rw [← Real.rpow_add hR]; congr 1; ring
  rw [he] at hconst
  have hp : (2:ℝ)^g*(2:ℝ)^(n-g) = (2:ℝ)^n := by
    rw [← pow_add,Nat.add_sub_of_le hgn]
  have hb : (C/(2:ℝ)^g)*angularTestRadius N σ (n-g) ≤
      ((2:ℝ)^N)^(500*σ)/((J:ℝ)*(2:ℝ)^n) := by
    calc
      _ ≤ (C/(2:ℝ)^g)*(1/(2:ℝ)^(n-g)*((2:ℝ)^N)^(50*σ)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = (C*(J:ℝ)*((2:ℝ)^N)^(50*σ))/((J:ℝ)*(2:ℝ)^n) := by
        rw [← hp]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hconst (by positivity)
  rw [← angularTestWidth_gap N σ hJ i n] at hb
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionGood
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable projection tests on the full conditional probability -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem measurable_projectionCollision (μ : Measure (Space d)) [IsFiniteMeasure μ] (W : ℝ) :
    Measurable (fun w : Sphere d => projectionCollision μ (w:Space d) W) := by
  let S := {p : Sphere d × (Space d × Space d) |
    |inner ℝ (p.2.1-p.2.2) (p.1:Space d)| ≤ W}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_le (by fun_prop) measurable_const
  exact measurable_measure_prodMk_left hS

theorem measurableSet_projectionGoodSet (μ : Measure (Space d)) [IsFiniteMeasure μ] (W T : ℝ) :
    MeasurableSet (projectionGoodSet μ W T) :=
  measurableSet_le (measurable_projectionCollision μ W) measurable_const

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionBuffer
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Directional buffers for the actual full-law projection test -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem projectionCollision_direction_transfer (μ : Measure (Space d))
    {D δ W W' : ℝ} (hD : 0 ≤ D) (_hδ : 0 ≤ δ)
    (hsupport : ∀ᵐ z : Space d × Space d ∂μ.prod μ, ‖z.1-z.2‖ ≤ D)
    {v w : Space d} (hvw : ‖v-w‖ ≤ δ) (hwidth : W+D*δ ≤ W') :
    projectionCollision μ v W ≤ projectionCollision μ w W' := by
  apply measure_mono_ae
  filter_upwards [hsupport] with z hz
  intro htest
  have hinner : |inner ℝ (z.1-z.2) (w-v)| ≤ D*δ := by
    have hnorm : ‖w-v‖ ≤ δ := by simpa only [norm_sub_rev] using hvw
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul hz hnorm (norm_nonneg _) hD)
  have he : inner ℝ (z.1-z.2) w = inner ℝ (z.1-z.2) v+inner ℝ (z.1-z.2) (w-v) := by
    rw [inner_sub_right]
    ring
  change |inner ℝ (z.1-z.2) v| ≤ W at htest
  change |inner ℝ (z.1-z.2) w| ≤ W'
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add htest hinner).trans hwidth)

theorem projectionGoodSet_buffer (μ : Measure (Space d))
    {D δ W W' T : ℝ} (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hsupport : ∀ᵐ z : Space d × Space d ∂μ.prod μ, ‖z.1-z.2‖ ≤ D)
    {v w : Sphere d} (hvw : dist v w ≤ δ) (hwidth : W+D*δ ≤ W')
    (hw : w ∈ projectionGoodSet μ W' T) : v ∈ projectionGoodSet μ W T := by
  have hd : ‖(v:Space d)-(w:Space d)‖ ≤ δ := by
    simpa only [Subtype.dist_eq,dist_eq_norm] using hvw
  exact (projectionCollision_direction_transfer μ hD hδ hsupport hd hwidth).trans hw

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ConditionalProjectionBuffer
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projection buffers for the full original conditional laws -/

namespace Falconer.Regularization
open Set MeasureTheory
variable {d : ℕ}

theorem conditional_pair_diameter (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d) :
    ∀ᵐ z : Space d × Space d ∂
      (ProbabilityTheory.cond ρ (Q.descendant P).carrier).prod
        (ProbabilityTheory.cond ρ (Q.descendant P).carrier),
      ‖z.1-z.2‖ ≤ Real.sqrt d*(Q.side/(2:ℝ)^P.length) := by
  have hs : ∀ᵐ z ∂ProbabilityTheory.cond ρ (Q.descendant P).carrier,
      z ∈ (Q.descendant P).carrier :=
    ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable (fun _ hz => hz)
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [hs] with x hx
  filter_upwards [hs] with y hy
  have hh := (Q.descendant P).dist_le (by rw [Q.descendant_side]; positivity) hx hy
  simpa only [dist_eq_norm,Q.descendant_side] using hh

theorem conditional_projection_buffer (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d)
    {δ W W' T : ℝ} (hδ : 0 ≤ δ) {v w : Sphere d} (hvw : dist v w ≤ δ)
    (hwidth : W+(Real.sqrt d/(2:ℝ)^P.length)*δ ≤ W')
    (hw : w ∈ projectionGoodSet (ProbabilityTheory.cond ρ (Q.descendant P).carrier) W' T) :
    v ∈ projectionGoodSet (ProbabilityTheory.cond ρ (Q.descendant P).carrier) W T := by
  apply projectionGoodSet_buffer _ (by positivity) hδ _ hvw hwidth hw
  simpa only [hQ,mul_one_div] using conditional_pair_diameter Q (by rw [hQ]; norm_num) ρ P

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ConditionalProjectionTest
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal occupied-anchor projection tests -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

namespace Regularization

theorem conditionalProjectionGoodSet_measurable (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d) (W T : ℝ) :
    MeasurableSet (conditionalProjectionGoodSet Q ρ P W T) := by
  classical
  unfold conditionalProjectionGoodSet
  split_ifs
  · exact measurableSet_projectionGoodSet _ _ _
  · exact MeasurableSet.empty

theorem conditionalProjectionGoodSet_buffer (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d)
    {δ W W' T : ℝ} (hδ : 0 ≤ δ) {v w : Sphere d} (hvw : dist v w ≤ δ)
    (hwidth : W+(Real.sqrt d/(2:ℝ)^P.length)*δ ≤ W')
    (hw : w ∈ conditionalProjectionGoodSet Q ρ P W' T) :
    v ∈ conditionalProjectionGoodSet Q ρ P W T := by
  classical
  unfold conditionalProjectionGoodSet at hw ⊢
  split_ifs at hw ⊢ with hocc
  · exact conditional_projection_buffer Q hQ ρ P hδ hvw hwidth hw
  · exact False.elim hw

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorTests
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual all-dimensional tests indexed by policy descriptors

The policy list is scalar. Its tests use original occupied cells and the
full conditional probability of the current ambient-dimensional class.
The tolerance is the manuscript's 500-sigma width at every level.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)

variable {d : ℕ}

theorem descriptorGoodDirections_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (P : List (Fin d → Bool)) (b : PolicyDescriptor) :
    MeasurableSet (descriptorGoodDirections Q ρ m N σ J i P b) := by
  cases b with
  | parallel g p => exact Regularization.parallelGoodSet_measurable _ _ _ _ _ _ _
  | projection p t => exact Regularization.conditionalProjectionGoodSet_measurable _ _ _ _ _

theorem uniform_descriptor_direction_buffer {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (b : PolicyDescriptor), descriptorValid N b →
      ∀ (P : List (Fin d → Bool)), P.length = descriptorAnchor b →
      ∀ (i : ℕ) (w u : Sphere d),
        dist w u ≤ C*angularTestRadius N σ (descriptorLength b) →
        w ∈ descriptorGoodDirections Q ρ m N σ J i P b →
        u ∈ descriptorGoodDirections Q ρ m N σ J (i+1) P b := by
  obtain ⟨N₁,h₁⟩ := uniform_angularTestWidth_gap hσ hJ
    (20*((d:ℝ)+1)*C) (by positivity)
  obtain ⟨N₂,h₂⟩ := uniform_angularTestWidth_gap hσ hJ
    (Real.sqrt d*C) (by positivity)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q hQ ρ _ m b hb P hP i w u hwu hw
  cases b with
  | parallel g p =>
    apply Regularization.parallelGoodSet_buffer Q ρ g p P
      (mul_nonneg hC (angularTestRadius_pos N σ (p-g)).le) ?_ hw hwu
    convert h₁ N ((le_max_left _ _).trans hN) g p hb.1 i using 1 <;> first | rfl | ring
  | projection p t =>
    apply Regularization.conditionalProjectionGoodSet_buffer Q hQ ρ P
      (mul_nonneg hC (angularTestRadius_pos N σ (t-p)).le)
      (by simpa only [dist_comm, descriptorLength] using hwu) ?_ hw
    have hh := h₂ N ((le_max_right _ _).trans hN) p t hb.1 i
    dsimp only [descriptorAnchor] at hP
    rw [hP]
    convert hh using 1 <;> first | rfl | ring

theorem policy_descriptor_valid (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) {b : PolicyDescriptor}
    (hb : b ∈ PlanarFalconer.policyDescriptorList A N q a t) : descriptorValid N b := by
  obtain ⟨s,u,_,hut,_,_,hpos,_,hbound⟩ := PlanarFalconer.policyDescriptor_origin A hq hb
  cases b <;> simp only [descriptorLength,descriptorAnchor,descriptorValid] at hpos hbound ⊢ <;>
    omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorMasks
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual anchored masks and retained pair tests in every dimension

The angular set at an anchor is tested against the full conditional law.
Masks use finite spherical nets at one eighth of the manuscript's buffer
radius. Their construction is independent of the number of anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
variable {d : ℕ}

theorem descriptorEndpointGood_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) :
    MeasurableSet (descriptorEndpointGood Q ρ m N σ J i b) := by
  classical
  have hm : MeasurableSet (⋂ p ∈ cubePaths d (descriptorAnchor b),
      {z : Space d × Sphere d | z.1 ∈ (Q.descendant p).carrier →
        z.2 ∈ descriptorGoodDirections Q ρ m N σ J i p b}) := by
    apply Finset.measurableSet_biInter
    intro p _
    convert ((Q.descendant p).measurable.preimage measurable_fst).compl.union
      ((descriptorGoodDirections_measurable Q ρ m N σ J i p b).preimage measurable_snd) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [mem_ofPred_eq,mem_union,mem_compl_iff,mem_preimage,imp_iff_not_or]
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp [descriptorEndpointGood]

theorem descriptorMask_bounds (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ descriptorMaskRadius N σ b/2)
    (x : Space d) (w : Sphere d) :
    0 ≤ descriptorMask Q ρ m N σ J i b S x w ∧
      descriptorMask Q ρ m N σ J i b S x w ≤ 1 :=
  anchoredBufferedMask_bounds Q _ (descriptorMaskRadius_pos N σ b) S hcover _ x w

theorem descriptorMask_support (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ descriptorMaskRadius N σ b/2)
    {x : Space d} (w : Sphere d)
    (hw : descriptorMask Q ρ m N σ J i b S x w ≠ 0) :
    (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  intro p hp hx
  exact anchoredBufferedMask_support Q (descriptorMaskRadius_pos N σ b) S hcover _ p
    ((mem_cubePaths _ _ _).mp hp) hx w hw

theorem uniform_descriptorMask_core {σ : ℝ} (hσ : 0 < σ) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (b : PolicyDescriptor), descriptorValid N b →
      ∀ (S : Finset (Sphere d)),
      (∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ descriptorMaskRadius N σ b/2) →
      ∀ (i : ℕ) (x : Space d), x ∈ Q.carrier → ∀ w : Sphere d,
      (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b →
      descriptorMask Q ρ m N σ J i b S x w = 1 := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptor_direction_buffer (d := d) hσ hJ (C := 1) (by norm_num)
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ m b hb S hcover i x hx w hw
  obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth (descriptorAnchor b) hx
  apply anchoredBufferedMask_core Q (descriptorMaskRadius_pos N σ b) S hcover _ p
    ((mem_cubePaths _ _ _).mp hp) hxp w
  intro z hz
  apply h₀ N hN Q hQ ρ m b hb p ((mem_cubePaths _ _ _).mp hp) i w z _ (hw p hp hxp)
  have hr := angularTestRadius_pos N σ (descriptorLength b)
  dsimp only [descriptorMaskRadius] at hz
  rw [dist_comm] at hz
  linarith

theorem descriptorPairTests_measurable (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor) :
    MeasurableSet (descriptorPairTests w₀ Q ρ m N σ J i B) := by
  classical
  have hm := (normalizeToSphere_measurable w₀).comp (measurable_fst.sub measurable_snd)
  have hset : MeasurableSet (⋂ b ∈ B, {z : Space d × Space d |
      (z.1,normalizeToSphere w₀ (z.1-z.2)) ∈ descriptorEndpointGood Q ρ m N σ J i b ∧
      (z.2,normalizeToSphere w₀ (z.1-z.2)) ∈ descriptorEndpointGood Q ρ m N σ J i b}) := by
    apply Finset.measurableSet_biInter
    intro b _
    exact ((descriptorEndpointGood_measurable Q ρ m N σ J i b).preimage
      (measurable_fst.prodMk hm)).inter
        ((descriptorEndpointGood_measurable Q ρ m N σ J i b).preimage
          (measurable_snd.prodMk hm))
  convert hset using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp [descriptorPairTests]

theorem descriptorPairTests_mono (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    {A B : Finset PolicyDescriptor} (hAB : A ⊆ B) :
    descriptorPairTests w₀ Q ρ m N σ J i B ⊆ descriptorPairTests w₀ Q ρ m N σ J i A :=
  fun _ hz b hb => hz b (hAB hb)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DistanceFrequencyMajorant
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem distanceFrequencyBox_two_lower :
    (2:ℝ≥0∞) • volume.restrict (Icc (-1:ℝ) 1) ≤
      distanceDifferenceMeasure (distanceFrequencyBox 2) := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [distanceDifferenceMeasure,Measure.map_apply (by fun_prop) hS,
    Measure.prod_apply (hS.preimage (by fun_prop))]
  have hsub : distanceFrequencyBox 1 ≤ distanceFrequencyBox 2 :=
    Measure.restrict_mono (Ioc_subset_Ioc (by norm_num) (by norm_num)) le_rfl
  calc
    _ = ∫⁻ _x, volume (S ∩ Icc (-1:ℝ) 1) ∂distanceFrequencyBox 1 := by
      rw [lintegral_const,distanceFrequencyBox_mass (by norm_num),
        Measure.smul_apply,Measure.restrict_apply hS,smul_eq_mul]
      norm_num
      exact mul_comm _ _
    _ ≤ ∫⁻ x, distanceFrequencyBox 2 ((fun y : ℝ => x-y) ⁻¹' S) ∂distanceFrequencyBox 1 := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with x hx
      rw [distanceFrequencyBox,Measure.restrict_apply (hS.preimage (by fun_prop))]
      rw [← (volume.measurePreserving_sub_left x).measure_preimage
        (hS.inter measurableSet_Icc).nullMeasurableSet]
      apply measure_mono
      intro y hy
      refine ⟨hy.1,?_,?_⟩ <;> dsimp at * <;> linarith [hy.2.1,hy.2.2,hx.1,hx.2]
    _ ≤ _ := lintegral_mono' hsub (fun _ => le_rfl)

theorem distanceSincKernel_two_decay (s : ℝ) :
    distanceSincKernel 2 s ≤ 4/(1+|s|)^2 := by
  have hden : 0 < (1+|s|)^2 := by positivity
  apply (le_div_iff₀ hden).mpr
  by_cases hs : |s| ≤ 1
  · have h := distanceSincKernel_le_one 2 s
    have hn := distanceSincKernel_nonneg 2 s
    nlinarith [abs_nonneg s,mul_le_mul_of_nonneg_right h (sq_nonneg (1+|s|))]
  · have hs' : 1 < |s| := lt_of_not_ge hs
    have hn : s ≠ 0 := by intro h; norm_num [h] at hs'
    have he : distanceSincKernel 2 s * (2*s)^2 = (Real.sin (2*s))^2 := by
      rw [distanceSincKernel,Real.sinc_of_ne_zero (mul_ne_zero (by norm_num) hn),div_pow]
      field_simp
    have hb : (Real.sin (2*s))^2 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_one (2*s)) 2
      simpa only [sq_abs,one_pow] using h
    have hn' := distanceSincKernel_nonneg 2 s
    have hsq : (1+|s|)^2 ≤ 4*s^2 := by nlinarith [sq_abs s]
    have hm := mul_le_mul_of_nonneg_left hsq hn'
    nlinarith

theorem frequency_band_le_sinc (μ : Measure ℝ) [IsFiniteMeasure μ] (A : ℝ) :
    (∫ r in Icc (-1:ℝ) 1, ‖charFun μ (A*r)‖^2) ≤
      8 * ∫ s, distanceSincKernel 2 (A*s) ∂distanceDifferenceMeasure μ := by
  have hi := charFun_sq_integrable_finite μ (distanceDifferenceMeasure (distanceFrequencyBox 2)) A
  have h := integral_mono_measure distanceFrequencyBox_two_lower
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun μ (A*r)‖)) hi
  rw [integral_smul_measure,smul_eq_mul,ENNReal.toReal_ofNat,
    ← distanceSincKernel_spectral_identity μ (by norm_num : (0:ℝ) ≤ 2) A] at h
  norm_num at h
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DistanceBandKernelBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem distanceBandKernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    {A : ℝ} (hA : 0 ≤ A) :
    Integrable (fun z : ℝ × ℝ => 1/(1+A*|z.1-z.2|)^2) (μ.prod μ) := by
  apply (integrable_const (1:ℝ)).mono (by apply Measurable.aestronglyMeasurable; fun_prop)
  filter_upwards with z
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),norm_one]
  apply (div_le_one (by positivity : 0 < (1+A*|z.1-z.2|)^2)).mpr
  nlinarith [mul_nonneg hA (abs_nonneg (z.1-z.2))]

theorem distance_band_kernel_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {A : ℝ} (hA : 0 < A) :
    (∫ r in Icc (-A) A, ‖charFun μ r‖^2) ≤
      32*A * ∫ z : ℝ × ℝ, 1/(1+A*|z.1-z.2|)^2 ∂μ.prod μ := by
  have h := mul_le_mul_of_nonneg_left (frequency_band_le_sinc μ A) hA.le
  rw [integral_scale_Icc (fun r => ‖charFun μ r‖^2) hA (by norm_num : (0:ℝ) ≤ 1)] at h
  simp only [mul_one] at h
  have he : (∫ s, distanceSincKernel 2 (A*s) ∂distanceDifferenceMeasure μ) =
      ∫ z : ℝ × ℝ, distanceSincKernel 2 (A*(z.1-z.2)) ∂μ.prod μ :=
    integral_map_of_stronglyMeasurable (by fun_prop)
      (((continuous_distanceSincKernel 2).comp (continuous_const.mul continuous_id)).stronglyMeasurable)
  rw [he] at h
  have hi : Integrable (fun z : ℝ × ℝ => distanceSincKernel 2 (A*(z.1-z.2))) (μ.prod μ) := by
    apply (integrable_const (1:ℝ)).mono (by
      exact ((continuous_distanceSincKernel 2).comp
        (continuous_const.mul (continuous_fst.sub continuous_snd))).aestronglyMeasurable)
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_nonneg (distanceSincKernel_nonneg _ _),norm_one]
    exact distanceSincKernel_le_one _ _
  have hk := integral_mono hi ((distanceBandKernel_integrable μ hA.le).const_mul 4)
    (show ∀ z : ℝ × ℝ, distanceSincKernel 2 (A*(z.1-z.2)) ≤
      4*(1/(1+A*|z.1-z.2|)^2) from by
      intro z
      simpa only [abs_mul,abs_of_pos hA,mul_one_div] using
        distanceSincKernel_two_decay (A*(z.1-z.2)))
  rw [integral_const_mul] at hk
  have hh := mul_le_mul_of_nonneg_left hk (show 0 ≤ A*8 by positivity)
  nlinarith

theorem distance_band_kernel_bound_ennreal (μ : Measure ℝ) [IsFiniteMeasure μ]
    {A : ℝ} (hA : 0 < A) :
    ENNReal.ofReal (∫ r in Icc (-A) A, ‖charFun μ r‖^2) ≤
      ENNReal.ofReal (32*A) *
        ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+A*|z.1-z.2|)^2) ∂μ.prod μ := by
  have h := ENNReal.ofReal_le_ofReal (distance_band_kernel_bound μ hA)
  rw [ENNReal.ofReal_mul (by positivity),ofReal_integral_eq_lintegral_ofReal
    (distanceBandKernel_integrable μ hA.le) (Filter.Eventually.of_forall (fun _ => by positivity))] at h
  exact h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_Bins
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set

theorem diagonal_bin_mass_le {ι : Type*} [Countable ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (I : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (I i))
    (hdisj : Pairwise fun i j => Disjoint (I i) (I j)) (w : ℝ)
    (hdiam : ∀ i x, x ∈ I i → ∀ y, y ∈ I i → |x-y| ≤ w) :
    (∑' i, (μ (I i))^2) ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
  have hd : Pairwise fun i j => Disjoint (I i ×ˢ I i) (I j ×ˢ I j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact Set.disjoint_left.mp (hdisj hij) hi.1 hj.1
  calc
    (∑' i, (μ (I i))^2) = ∑' i, (μ.prod μ) (I i ×ˢ I i) := by
      simp only [Measure.prod_prod, pow_two]
    _ = (μ.prod μ) (⋃ i, I i ×ˢ I i) :=
      (measure_iUnion hd (fun i => (hmeas i).prod (hmeas i))).symm
    _ ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
      apply measure_mono
      intro z hz
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      exact hdiam i z.1 hi.1 z.2 hi.2

theorem realBin_measurable (w : ℝ) (j : ℤ) : MeasurableSet (realBin w j) :=
  measurableSet_Ico

theorem realBin_disjoint {w : ℝ} (hw : 0 < w) :
    Pairwise fun i j => Disjoint (realBin w i) (realBin w j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : ((i+1 : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show i+1 ≤ j by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxj.1.trans' hm)) hxi.2
  · have hc : ((j+1 : ℤ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show j+1 ≤ i by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxi.1.trans' hm)) hxj.2

theorem realBin_diameter (w : ℝ) (j : ℤ) {x y : ℝ}
    (hx : x ∈ realBin w j) (hy : y ∈ realBin w j) : |x-y| ≤ w := by
  simp only [realBin, Set.mem_Ico, Int.cast_add, Int.cast_one] at hx hy
  apply abs_le.mpr
  constructor <;> nlinarith

theorem real_bin_collision_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {w : ℝ} (hw : 0 < w) :
    (∑' j : ℤ, (μ (realBin w j))^2) ≤
      (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} :=
  diagonal_bin_mass_le μ (realBin w) (realBin_measurable w) (realBin_disjoint hw) w
    (fun j _ hx _ hy => realBin_diameter w j hx hy)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_BinOffsets
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

 theorem ennreal_offset_cauchy (a b : ℤ → ℝ≥0∞) (h : ℤ) :
    (∑' j : ℤ, a j*b (j-h)) ≤
      (∑' j : ℤ, (a j)^2)^(1/2 : ℝ) * (∑' j : ℤ, (b j)^2)^(1/2 : ℝ) := by
  have hpq : (2:ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ℤ) hpq
    (measurable_of_countable a).aemeasurable
    (measurable_of_countable (fun j => b (j-h))).aemeasurable
  simp only [lintegral_count, ENNReal.rpow_two] at hh
  have he : (∑' j : ℤ, (b (j-h))^2) = ∑' j : ℤ, (b j)^2 :=
    (Equiv.subRight h).tsum_eq (fun j => (b j)^2)
  simpa only [one_div, he, Pi.mul_apply] using hh

 theorem realBin_cover {w : ℝ} (hw : 0 < w) (x : ℝ) :
    x ∈ realBin w ⌊x/w⌋ := by
  constructor
  · exact (le_div_iff₀ hw).mp (Int.floor_le (x/w))
  · simpa only [Int.cast_add,Int.cast_one] using
      (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (x/w))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_BinKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

 theorem half_le_abs_int_add_half (h : ℤ) : (1/2:ℝ) ≤ |(h:ℝ)+1/2| := by
  by_cases hh : 0 ≤ h
  · have hr : (0:ℝ) ≤ h := by exact_mod_cast hh
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hr : (h:ℝ) ≤ -1 := by exact_mod_cast (show h ≤ -1 by omega)
    rw [abs_of_nonpos (by linarith)]
    linarith

 theorem realBin_kernel_bound {w x y : ℝ} (hw : 0 < w) {i j : ℤ}
    (hi : x ∈ realBin w i) (hj : y ∈ realBin w j) :
    1/(1+|x-y|/w)^2 ≤ 4/(((i-j:ℤ):ℝ)+1/2)^2 := by
  have hi1 : (i:ℝ) ≤ x/w := (le_div_iff₀ hw).mpr hi.1
  have hi2 : x/w < (i:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hi.2
  have hj1 : (j:ℝ) ≤ y/w := (le_div_iff₀ hw).mpr hj.1
  have hj2 : y/w < (j:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hj.2
  have hd : |(((i-j:ℤ):ℝ)+1/2)| ≤ 2*(1+|x-y|/w) := by
    rw [abs_le]
    have h1 := neg_abs_le ((x-y)/w)
    have h2 := le_abs_self ((x-y)/w)
    rw [abs_div,abs_of_pos hw,sub_div] at h1 h2
    simp only [Int.cast_sub]
    constructor <;> linarith [div_nonneg (abs_nonneg (x-y)) hw.le]
  have hpos : 0 < 1+|x-y|/w := by positivity
  have hh := half_le_abs_int_add_half (i-j)
  have hsq : 0 < ((((i-j:ℤ):ℝ)+1/2)^2) := by
    nlinarith [sq_abs ((((i-j:ℤ):ℝ)+1/2))]
  apply (div_le_div_iff₀ (sq_pos_of_pos hpos) hsq).mpr
  nlinarith [sq_abs ((((i-j:ℤ):ℝ)+1/2)), sq_nonneg (2*(1+|x-y|/w)-|(((i-j:ℤ):ℝ)+1/2)|)]

 theorem binKernelConstant_ne_top : binKernelConstant ≠ ∞ := by
  have hs := (Real.summable_one_div_int_add_rpow (1/2) 2).mpr (by norm_num)
  have ht : Summable (fun h : ℤ => 4/((h:ℝ)+1/2)^2) := by
    simpa only [Real.rpow_two,sq_abs,mul_one_div] using hs.mul_left 4
  exact ht.tsum_ofReal_ne_top

 theorem weighted_offset_kernel_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (w : ℝ) (c : ℤ → ℝ≥0∞) :
    (∫⁻ z : ℝ × ℝ, ∑' h : ℤ, ∑' j : ℤ,
      (realBin w j ×ˢ realBin w (j-h)).indicator (fun _ => c h) z ∂μ.prod ν) ≤
      (∑' h : ℤ, c h) * (binL2Norm μ w * binL2Norm ν w) := by
  have hm (h j : ℤ) : Measurable ((realBin w j ×ˢ realBin w (j-h)).indicator
      (fun _ : ℝ × ℝ => c h)) :=
    measurable_const.indicator ((realBin_measurable w j).prod (realBin_measurable w (j-h)))
  rw [lintegral_tsum (fun h => (Measurable.tsum (fun j => hm h j)).aemeasurable)]
  simp_rw [lintegral_tsum (fun j => (hm _ j).aemeasurable)]
  simp_rw [lintegral_indicator_const ((realBin_measurable w _).prod (realBin_measurable w _)),
    Measure.prod_prod, ENNReal.tsum_mul_left]
  calc
    _ ≤ ∑' h : ℤ, c h * (binL2Norm μ w * binL2Norm ν w) := by
      apply ENNReal.tsum_le_tsum
      intro h
      exact mul_le_mul_right (ennreal_offset_cauchy (fun j => μ (realBin w j))
        (fun j => ν (realBin w j)) h) (c h)
    _ = _ := ENNReal.tsum_mul_right

 theorem real_bin_decaying_kernel_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {w : ℝ} (hw : 0 < w) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/w)^2) ∂μ.prod ν) ≤
      binKernelConstant * (binL2Norm μ w * binL2Norm ν w) := by
  apply le_trans (lintegral_mono (fun z => ?_))
    (weighted_offset_kernel_bound μ ν w binKernelWeight)
  let i : ℤ := ⌊z.1/w⌋
  let j : ℤ := ⌊z.2/w⌋
  have hi := realBin_cover hw z.1
  have hj := realBin_cover hw z.2
  have he : i-(i-j)=j := by omega
  have hz : z ∈ realBin w i ×ˢ realBin w (i-(i-j)) := ⟨hi,by simpa only [he] using hj⟩
  calc
    _ ≤ binKernelWeight (i-j) := ENNReal.ofReal_le_ofReal (realBin_kernel_bound hw hi hj)
    _ = (realBin w i ×ˢ realBin w (i-(i-j))).indicator
        (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z := (indicator_of_mem hz (fun _ : ℝ × ℝ => binKernelWeight (i-j))).symm
    _ ≤ ∑' k : ℤ, (realBin w k ×ˢ realBin w (k-(i-j))).indicator
        (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z :=
      ENNReal.le_tsum (f := fun index : ℤ =>
        (realBin w index ×ˢ realBin w (index-(i-j))).indicator
          (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z) i
    _ ≤ ∑' h : ℤ, ∑' k : ℤ, (realBin w k ×ˢ realBin w (k-h)).indicator
        (fun _ : ℝ × ℝ => binKernelWeight h) z :=
      ENNReal.le_tsum (f := fun offset : ℤ => ∑' index : ℤ,
        (realBin w index ×ˢ realBin w (index-offset)).indicator
          (fun _ : ℝ × ℝ => binKernelWeight offset) z) (i-j)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_BinEstimates
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem binL2Norm_mul_self (μ : Measure ℝ) (w : ℝ) :
    binL2Norm μ w * binL2Norm μ w = ∑' j : ℤ, (μ (realBin w j))^2 := by
  unfold binL2Norm
  rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num)]
  norm_num

theorem real_bin_decaying_self_kernel_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {w : ℝ} (hw : 0 < w) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/w)^2) ∂μ.prod μ) ≤
      binKernelConstant * (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
  have h := real_bin_decaying_kernel_bound μ μ hw
  rw [binL2Norm_mul_self] at h
  exact h.trans (mul_le_mul_right (real_bin_collision_bound μ hw) _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DominatedBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive dominated-measure bound on a real frequency band

Scalar real-line binning and sinc estimates control the frequency band.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

 theorem dominated_real_frequency_band (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A c : ℝ} (hA : 0 < A) (hc : 0 ≤ c)
    (hdom : μ ≤ ENNReal.ofReal c • ν) :
    ∫ r in Icc (-A) A, ‖charFun μ r‖^2 ≤
      32*A*c^2*PlanarFalconer.binKernelConstant.toReal *
        (ν.prod ν).real {z : ℝ × ℝ | |z.1-z.2| ≤ 1/A} := by
  let F : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (1/(1+A*|z.1-z.2|)^2)
  have hp := Measure.prod_mono hdom hdom
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul] at hp
  have hk := lintegral_mono' hp (fun z => le_refl (F z))
  rw [lintegral_smul_measure] at hk
  simp only [smul_eq_mul] at hk
  have hb := PlanarFalconer.real_bin_decaying_self_kernel_bound ν (one_div_pos.mpr hA)
  have he : (fun z : ℝ × ℝ => ENNReal.ofReal (1/(1+|z.1-z.2|/(1/A))^2)) = F := by
    funext z
    simp only [F,div_eq_mul_inv,one_mul,mul_one,inv_inv,mul_comm]
  rw [he] at hb
  have hk' := hk.trans (mul_le_mul_right hb (ENNReal.ofReal c*ENNReal.ofReal c))
  have hh := (PlanarFalconer.distance_band_kernel_bound_ennreal μ hA).trans
    (mul_le_mul_right hk' (ENNReal.ofReal (32*A)))
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top PlanarFalconer.binKernelConstant_ne_top (measure_ne_top (ν.prod ν) _)))) hh
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun r => sq_nonneg ‖charFun μ r‖))] at hr
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc,
    ENNReal.toReal_ofReal (show 0 ≤ 32*A by positivity),measureReal_def,pow_two,mul_assoc] using hr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_Shells
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set ComplexConjugate
open scoped ENNReal

theorem fourier_energy_even (μ : Measure ℝ) (r : ℝ) :
    ‖charFun μ (-r)‖^2 = ‖charFun μ r‖^2 := by
  rw [charFun_neg]
  simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_DistanceLinearization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual distance Taylor error for the suffix reduction

The error estimate is dimension independent before insertion of the cube
diameter. Its proof is the exact squared-norm identity, so no differentiable
extension across the diagonal is needed.
-/

namespace Falconer
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem pair_displacement_bound (x y c₁ c₂ : E) {δ₁ δ₂ : ℝ}
    (h₁ : ‖x-c₁‖ ≤ δ₁) (h₂ : ‖y-c₂‖ ≤ δ₂) :
    ‖(x-y)-(c₁-c₂)‖ ≤ δ₁+δ₂ := by
  have he : (x-y)-(c₁-c₂) = (x-c₁)-(y-c₂) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add h₁ h₂)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SuffixGrouping
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse grouping of the actual all-dimensional distance cells

Two fine distance distributions sharing one bin force all distances of
their full cell pairs into a common coarse collision band. The width
constant retains the ambient dimension explicitly.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem cellDistance_mass (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : DyadicCube d) : cellDistance μ ν P Q univ = μ P.carrier*ν Q.carrier := by
  rw [cellDistance,Measure.map_apply (by fun_prop) MeasurableSet.univ,preimage_univ,
    ← univ_prod_univ,Measure.prod_prod,Measure.restrict_apply_univ,Measure.restrict_apply_univ]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RetainedPairs
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact decomposition into the suffix cells having a witness

Only actual original-law restrictions occur. Empty intersections with the
parent's good-pair set contribute zero, so retaining witnessed cells is an
exact identity, before their full cell measures are used for comparison.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem testedCellDistance_le (μ ν : Measure (Space d))
    (P Q : DyadicCube d) (G : Set (Space d × Space d)) :
    testedCellDistance μ ν P Q G ≤ cellDistance μ ν P Q := by
  exact Measure.map_mono Measure.restrict_le_self (by fun_prop)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SuffixScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The suffix scale hypotheses in the manuscript's separated geometry -/

namespace Falconer
open Set MeasureTheory

theorem sqrt_dimension_le (d : ℕ) : Real.sqrt (d : ℝ) ≤ (d : ℝ)+1 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (d : ℝ),Nat.cast_nonneg (α := ℝ) d]

theorem DyadicCube.separated_pairs_lower {d : ℕ} (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    (hsep : 125*((d:ℝ)+1)*P.side ≤ ‖P.center-Q.center‖)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    100*((d:ℝ)+1)*P.side ≤ ‖x-y‖ := by
  have hQp : 0 < Q.side := by rwa [hQ]
  have h₁ := P.dist_le hP.le hx (P.center_mem hP)
  have h₂ := Q.dist_le hQp.le hy (Q.center_mem hQp)
  rw [hQ] at h₂
  have hδ : ‖(x-y)-(P.center-Q.center)‖ ≤ 2*Real.sqrt d*P.side := by
    simpa only [dist_eq_norm,two_mul,mul_add,add_mul] using
      pair_displacement_bound x y P.center Q.center h₁ h₂
  have hnorm : ‖P.center-Q.center‖ ≤ ‖x-y‖+‖(x-y)-(P.center-Q.center)‖ := by
    have he : P.center-Q.center = (x-y)-((x-y)-(P.center-Q.center)) := by abel
    calc
      _ = ‖(x-y)-((x-y)-(P.center-Q.center))‖ := congrArg norm he
      _ ≤ _ := norm_sub_le _ _
  have hs := mul_le_mul_of_nonneg_right (sqrt_dimension_le d) hP.le
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PositiveFourier
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fourier control of the actual positive collision state

The tolerance is the manuscript's 100(d+1)2⁻ᵗ. The frequency interval
is enlarged from 2ᵗ/(d+1) to 2ᵗ using positivity, with a fixed dimensional
constant. No regularity of the tested pair measure is required here.
-/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem dyadic_distance_collision_fourier (d : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (a t : ℕ), a ≤ t →
      (2:ℝ)^(t-a) * (μ.prod μ).real
        {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^t} ≤
      (C/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^t) ((2:ℝ)^t), ‖charFun μ r‖^2 := by
  obtain ⟨C,hC,h⟩ := PlanarFalconer.finite_measure_distance_collision_fourier
  refine ⟨((d:ℝ)+1)*C,by positivity,?_⟩
  intro μ _ a t hat
  let A := (2:ℝ)^t/((d:ℝ)+1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hAle : A ≤ (2:ℝ)^t := by
    apply (div_le_iff₀ (by positivity : 0 < (d:ℝ)+1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) d,show 0 ≤ (2:ℝ)^t by positivity]
  have htol : 100/A = 100*((d:ℝ)+1)/(2:ℝ)^t := by dsimp [A]; field_simp
  have hh := h μ A hA
  rw [htol] at hh
  have hi : IntegrableOn (fun r => ‖charFun μ r‖^2)
      (Icc (-(2:ℝ)^t) ((2:ℝ)^t)) := by
    simpa only [one_mul,IntegrableOn] using
      PlanarFalconer.charFun_sq_integrable_finite μ
        (volume.restrict (Icc (-(2:ℝ)^t) ((2:ℝ)^t))) 1
  have hsub : Icc (-A) A ⊆ Icc (-(2:ℝ)^t) ((2:ℝ)^t) := by
    intro r hr
    exact ⟨by linarith [hr.1],hr.2.trans hAle⟩
  have hint := integral_mono_measure (Measure.restrict_mono hsub le_rfl)
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun μ r‖)) hi
  have hpow : (2:ℝ)^t = (2:ℝ)^a * (2:ℝ)^(t-a) := by
    rw [← pow_add,Nat.add_sub_of_le hat]
  have hscale : (2:ℝ)^(t-a) = (((d:ℝ)+1)/(2:ℝ)^a)*A := by
    dsimp [A]
    rw [hpow]
    field_simp
  calc
    _ = (((d:ℝ)+1)/(2:ℝ)^a) *
        (A*(μ.prod μ).real {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^t}) := by
      rw [hscale]; ring
    _ ≤ (((d:ℝ)+1)/(2:ℝ)^a) *
        (C*∫ r in Icc (-A) A, ‖charFun μ r‖^2) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ (((d:ℝ)+1)/(2:ℝ)^a) *
        (C*∫ r in Icc (-(2:ℝ)^t) ((2:ℝ)^t), ‖charFun μ r‖^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hint hC.le) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DescriptorProduct
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual descriptor products and their reached angular factors -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem descriptorProduct_bounds (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d, ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (x : Space d) (w : Sphere d) :
    0 ≤ descriptorProduct Q ρ m N σ J i B S x w ∧
      descriptorProduct Q ρ m N σ J i B S x w ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun b hb =>
      (descriptorMask_bounds Q ρ m N σ J i b (S b) (hcover b hb) x w).1)
  · exact Finset.prod_le_one (fun b hb =>
      (descriptorMask_bounds Q ρ m N σ J i b (S b) (hcover b hb) x w).1)
      (fun b hb => (descriptorMask_bounds Q ρ m N σ J i b (S b) (hcover b hb) x w).2)

theorem descriptorProduct_support (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d, ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    {x : Space d} {w : Sphere d} (h : descriptorProduct Q ρ m N σ J i B S x w ≠ 0) :
    ∀ b ∈ B, (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  intro b hb
  apply descriptorMask_support Q ρ m N σ J i b (S b) (hcover b hb) w
  exact (Finset.prod_ne_zero_iff.mp h) b hb

theorem uniform_descriptorProduct_core {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (B : Finset PolicyDescriptor), (∀ b ∈ B, descriptorValid N b) →
      ∀ (S : PolicyDescriptor → Finset (Sphere d)),
      (∀ b ∈ B, ∀ w : Sphere d,
        ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2) →
      ∀ (i : ℕ) (x : Space d), x ∈ Q.carrier → ∀ w : Sphere d,
      (∀ b ∈ B, (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b) →
      descriptorProduct Q ρ m N σ J i B S x w = 1 := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorMask_core (d := d) hσ hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ m B hB S hS i x hx w hw
  apply Finset.prod_eq_one
  intro b hb
  exact h₀ N hN Q hQ ρ m b (hB b hb) (S b) (hS b hb) i x hx w (hw b hb)

theorem descriptorProduct_pair_support (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    {x y : Space d}
    (h : descriptorProduct Q ρ m N σ J i B S x (normalizeToSphere w₀ (x-y)) *
      descriptorProduct Q ρ m N σ J i B S y (normalizeToSphere w₀ (x-y)) ≠ 0) :
    (x,y) ∈ descriptorPairTests w₀ Q ρ m N σ J (i+1) B := by
  intro b hb
  exact ⟨descriptorProduct_support Q ρ m N σ J i B S hcover
      (mul_ne_zero_iff.mp h).1 b hb,
    descriptorProduct_support Q ρ m N σ J i B S hcover (mul_ne_zero_iff.mp h).2 b hb⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_WeightedLowpass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive lowpass comparison for the actual masked distance law

The comparison is made between positive measures before taking Fourier
transforms. All old masks remain in the weighted distance pushforward.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

/-- A lower bound only on the tested set suffices for positive domination. -/
theorem restrict_smul_le_withDensity {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : Set X) (hG : MeasurableSet G)
    (w : X → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ᵐ x ∂μ, x ∈ G → c ≤ w x) :
    c • μ.restrict G ≤ μ.withDensity w := by
  rw [← withDensity_const,← withDensity_indicator hG]
  apply withDensity_mono
  filter_upwards [h] with x hx
  by_cases hxG : x ∈ G
  · simpa only [indicator_of_mem hxG] using hx hxG
  · simp only [indicator_of_notMem hxG]
    exact bot_le

theorem dyadic_collision_fourier_of_domination (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (c : ℝ), 0 ≤ c → ENNReal.ofReal c • μ ≤ ν →
      ∀ (a t : ℕ), a ≤ t →
      c^2 * (2:ℝ)^(t-a) * (μ.prod μ).real
        {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^t} ≤
      (C/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^t) ((2:ℝ)^t), ‖charFun ν r‖^2 := by
  obtain ⟨C,hC,hb⟩ := dyadic_distance_collision_fourier d
  refine ⟨C,hC,?_⟩
  intro μ ν _ _ c hc hdom a t hat
  have hp := Measure.prod_mono hdom hdom
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,
    ← ENNReal.ofReal_mul hc] at hp
  have hr := ENNReal.toReal_mono (measure_ne_top (ν.prod ν) _)
    (hp {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^t})
  simp only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg hc hc)] at hr
  have hh := (mul_le_mul_of_nonneg_left hr (show 0 ≤ (2:ℝ)^(t-a) by positivity)).trans
    (hb ν a t hat)
  simpa only [measureReal_def,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh

/-- Core masks preserve the original tested pairs; only their distance weight
enters the domination constant. -/
theorem maskedCellDistance_dominates
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (X Y : DyadicCube d) (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (c : ℝ) (_hc : 0 ≤ c)
    (hcore : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier), z ∈ G →
      descriptorProduct Q ρ (fun u => m (u/N)) N σ J i B S z.1 (normalizeToSphere w₀ (z.1-z.2)) = 1 ∧
      descriptorProduct Q ρ (fun u => m (u/N)) N σ J i B S z.2 (normalizeToSphere w₀ (z.1-z.2)) = 1)
    (hweight : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier), z ∈ G →
      c ≤ (dist z.1 z.2*(2:ℝ)^a)^(-(((d:ℝ)-1)/2))) :
    ENNReal.ofReal ((profileModelMass m N a)⁻¹^2*c) • testedCellDistance ρ ρ X Y G ≤
      maskedCellDistance w₀ Q ρ m N σ J i a B S X Y := by
  have hh := restrict_smul_le_withDensity ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier))
    G hG (fun z => ENNReal.ofReal ((profileModelMass m N a)⁻¹^2 *
      descriptorPairWeight w₀ Q ρ m N σ J i a B S z))
    (ENNReal.ofReal ((profileModelMass m N a)⁻¹^2*c)) (by
      filter_upwards [hcore,hweight] with z hz hw
      intro hzg
      obtain ⟨h₁,h₂⟩ := hz hzg
      apply ENNReal.ofReal_le_ofReal
      simpa only [descriptorPairWeight,h₁,h₂,mul_one] using
        mul_le_mul_of_nonneg_left (hw hzg) (sq_nonneg _))
  have hm := Measure.map_mono hh (show Measurable (fun z : Space d × Space d => dist z.1 z.2) by fun_prop)
  rw [Measure.map_smul] at hm
  simpa only [testedCellDistance,testedCellPair,maskedCellDistance] using hm

theorem profileModelMass_inverse_four (m : ℝ → ℝ) (N a : ℕ) :
    ((profileModelMass m N a)⁻¹)^4 = ((2:ℝ)^N)^(4*m ((a:ℝ)/N)) := by
  unfold profileModelMass
  rw [← Real.rpow_neg (by positivity : 0 ≤ (2:ℝ)^N),← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity : 0 ≤ (2:ℝ)^N)]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PositiveTerminal
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Terminal bounds for the actual positive distance states

The profile is evaluated at integer depths in the recursive state.  The
regularized class stores its profile on [0,1], so the final theorem explicitly
uses `u ↦ m (u / N)` when passing to that state.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem testedCellDistance_mass_le (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (P Q : DyadicCube d) (G : Set (Space d × Space d)) :
    testedCellDistance ρ ρ P Q G univ ≤ ρ P.carrier * ρ Q.carrier := by
  exact (testedCellDistance_le ρ ρ P Q G univ).trans_eq (cellDistance_mass ρ ρ P Q)

theorem positiveCollisionCount_mass_bound (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (A : ℕ → ℝ)
    (N : ℕ) (σ : ℝ) (J i q a t : ℕ) (X Y : List (Fin d → Bool))
    (ℓ : ℝ)
    (hX : ρ (Q.descendant X).carrier ≤ ENNReal.ofReal (((2:ℝ)^N)^(ℓ-m a)))
    (hY : ρ (Q.descendant Y).carrier ≤ ENNReal.ofReal (((2:ℝ)^N)^(ℓ-m a))) :
    positiveCollisionCount w₀ Q ρ m A N σ J i q a t X Y ≤
      ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*ℓ)) := by
  let θ := testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
    (policyTestPairs w₀ Q ρ m A N σ J i q a t)
  have ht : θ univ ≤ (ENNReal.ofReal (((2:ℝ)^N)^(ℓ-m a)))^2 := by
    exact (testedCellDistance_mass_le ρ _ _ _).trans
      (by simpa only [pow_two] using mul_le_mul' hX hY)
  have hc : (θ.prod θ) {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^t} ≤
      (ENNReal.ofReal (((2:ℝ)^N)^(ℓ-m a)))^4 := by
    calc
      _ ≤ (θ.prod θ) univ := measure_mono (subset_univ _)
      _ = θ univ * θ univ := by rw [← univ_prod_univ,Measure.prod_prod]
      _ ≤ _ := by convert mul_le_mul' ht ht using 1 <;> first | (with_reducible_and_instances rfl) | ring
  change ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a)) * (θ.prod θ) _ ≤ _
  apply (mul_le_mul' le_rfl hc).trans_eq
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hp : ((((2:ℝ)^N)^(ℓ-m a))^4) = ((2:ℝ)^N)^(4*(ℓ-m a)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
    congr 1
    ring
  rw [hp,mul_assoc,← Real.rpow_add (by positivity)]
  congr 2
  ring

theorem positiveCollisionCount_regularized (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m)
    (A : ℕ → ℝ) (σ : ℝ) (J i q : ℕ) {a t : ℕ}
    (ha : a ≤ N) (X Y : List (Fin d → Bool))
    (hX : X.length = a) (hY : Y.length = a) :
    positiveCollisionCount w₀ Q ρ (fun u => m (u/N)) A N σ J i q a t X Y ≤
      ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*((d:ℝ)+1)*lam)) := by
  let := hreg.probability
  have hcell (P : List (Fin d → Bool)) (hP : P.length = a) :
      ρ (Q.descendant P).carrier ≤
        ENNReal.ofReal (((2:ℝ)^N)^(((d:ℝ)+1)*lam-m ((a:ℝ)/N))) := by
    by_cases hp : 0 < ρ (Q.descendant P).carrier
    · rw [← ENNReal.ofReal_toReal (measure_ne_top ρ _)]
      apply ENNReal.ofReal_le_ofReal
      exact (hreg.cells a ha P hP hp).2.trans_eq
        (Real.rpow_add (by positivity) _ _).symm
    · simp only [not_lt,le_zero_iff] at hp
      rw [hp]
      exact zero_le
  simpa only [mul_assoc] using positiveCollisionCount_mass_bound w₀ Q ρ
    (fun u => m (u/N)) A N σ J i q a t X Y (((d:ℝ)+1)*lam)
    (hcell X hX) (hcell Y hY)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_MaskedDistanceBounds
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the original masked distance measure

Here `m` is the unit-interval regularized profile. Descriptor predicates
receive its depth parametrization `u ↦ m (u/N)`.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

 theorem descriptorPairWeight_bounds (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (hd : 1 ≤ d) {L : ℝ} (hL : 0 < L) (z : Space d × Space d)
    (hz : L ≤ dist z.1 z.2*(2:ℝ)^a) :
    0 ≤ descriptorPairWeight w₀ Q ρ m N σ J i a B S z ∧
      descriptorPairWeight w₀ Q ρ m N σ J i a B S z ≤ L^(-(((d:ℝ)-1)/2)) := by
  have h₁ := descriptorProduct_bounds Q ρ (fun u => m (u/N)) N σ J i B S hcover
    z.1 (normalizeToSphere w₀ (z.1-z.2))
  have h₂ := descriptorProduct_bounds Q ρ (fun u => m (u/N)) N σ J i B S hcover
    z.2 (normalizeToSphere w₀ (z.1-z.2))
  have hd' : (1:ℝ) ≤ d := Nat.one_le_cast.mpr hd
  have hh : -(((d:ℝ)-1)/2) ≤ 0 := by linarith
  have hr : 0 ≤ (dist z.1 z.2*(2:ℝ)^a)^(-(((d:ℝ)-1)/2)) :=
    (Real.rpow_pos_of_pos (hL.trans_le hz) _).le
  constructor
  · exact mul_nonneg (mul_nonneg hr h₁.1) h₂.1
  · apply (mul_le_of_le_one_right (mul_nonneg hr h₁.1) h₂.2).trans
    exact (mul_le_of_le_one_right hr h₁.2).trans (Real.rpow_le_rpow_of_nonpos hL hz hh)

 theorem maskedCellDistance_finite (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ)
    (σ : ℝ) (J i a : ℕ) (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (hd : 1 ≤ d) {L : ℝ} (hL : 0 < L) (X Y : DyadicCube d)
    (hsep : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
      L ≤ dist z.1 z.2*(2:ℝ)^a) :
    IsFiniteMeasure (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) := by
  let π := (ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)
  have hbound : ∀ᵐ z ∂π,
      ENNReal.ofReal ((profileModelMass m N a)⁻¹^2 * descriptorPairWeight w₀ Q ρ m N σ J i a B S z) ≤
        ENNReal.ofReal ((profileModelMass m N a)⁻¹^2 * L^(-(((d:ℝ)-1)/2))) := by
    filter_upwards [hsep] with z hz
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (descriptorPairWeight_bounds w₀ Q ρ m N σ J i a B S hcover hd hL z hz).2 (sq_nonneg _))
  let := finite_withDensity_of_bounded π _ ENNReal.ofReal_lt_top hbound
  unfold maskedCellDistance
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

 theorem uniform_maskedCellDistance_dominates {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) (hd : 1 ≤ d) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (B : Finset PlanarFalconer.PolicyDescriptor), (∀ b ∈ B, descriptorValid N b) →
      ∀ (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)),
      (∀ b ∈ B, ∀ w : Sphere d,
        ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2) →
      ∀ (i a : ℕ) (w₀ : Sphere d) (X Y : List (Fin d → Bool)) (U : ℝ), 0 < U →
      (∀ᵐ z ∂(ρ.restrict (Q.descendant X).carrier).prod (ρ.restrict (Q.descendant Y).carrier),
        0 < dist z.1 z.2*(2:ℝ)^a ∧ dist z.1 z.2*(2:ℝ)^a ≤ U) →
      ENNReal.ofReal ((profileModelMass m N a)⁻¹^2 * U^(-(((d:ℝ)-1)/2))) •
        testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
          (descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J i B) ≤
        maskedCellDistance w₀ Q ρ m N σ J i a B S (Q.descendant X) (Q.descendant Y) := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorProduct_core (d := d) hσ hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ m B hB S hS i a w₀ X Y U hU hdist
  have hmem : ∀ᵐ z ∂(ρ.restrict (Q.descendant X).carrier).prod (ρ.restrict (Q.descendant Y).carrier),
      z.1 ∈ Q.carrier ∧ z.2 ∈ Q.carrier := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (Q.descendant X).measurable),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (Q.descendant Y).measurable)] with z hx hy
    exact ⟨Q.descendant_subset X hx,Q.descendant_subset Y hy⟩
  apply maskedCellDistance_dominates w₀ Q ρ m N σ J i a B S _ _ _
    (descriptorPairTests_measurable w₀ Q ρ _ N σ J i B) _ (by positivity)
  · filter_upwards [hmem] with z hz
    intro hzg
    exact ⟨h₀ N hN Q hQ ρ (fun u => m (u/N)) B hB S hS i z.1 hz.1 _
      (fun b hb => (hzg b hb).1),
      h₀ N hN Q hQ ρ (fun u => m (u/N)) B hB S hS i z.2 hz.2 _
      (fun b hb => (hzg b hb).2)⟩
  · filter_upwards [hdist] with z hz
    intro _
    apply Real.rpow_le_rpow_of_nonpos hz.1 hz.2
    have hd' : (1:ℝ) ≤ d := Nat.one_le_cast.mpr hd
    linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_MaskedNested
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support of all old masks controls the positive low-frequency child

The old weighted law is dominated by the unweighted child restriction.
This comparison takes place before applying the scalar real-line bin bound.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

 theorem maskedCellDistance_le_tested (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B B' : Finset PlanarFalconer.PolicyDescriptor) (hsub : B' ⊆ B)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (hd : 1 ≤ d) (X Y : DyadicCube d)
    (hsep : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
      1 ≤ dist z.1 z.2*(2:ℝ)^a)
    (hG : MeasurableSet (descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J (i+1) B')) :
    maskedCellDistance w₀ Q ρ m N σ J i a B S X Y ≤
      ENNReal.ofReal ((profileModelMass m N a)⁻¹^2) •
        testedCellDistance ρ ρ X Y
          (descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J (i+1) B') := by
  let π := (ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)
  let G := descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J (i+1) B'
  let K := ENNReal.ofReal ((profileModelMass m N a)⁻¹^2)
  have hh : π.withDensity (fun z => ENNReal.ofReal ((profileModelMass m N a)⁻¹^2 *
      descriptorPairWeight w₀ Q ρ m N σ J i a B S z)) ≤ K • π.restrict G := by
    rw [← withDensity_const,← withDensity_indicator hG]
    apply withDensity_mono
    filter_upwards [hsep] with z hz
    by_cases hgood : z ∈ G
    · rw [indicator_of_mem hgood]
      apply ENNReal.ofReal_le_ofReal
      have hb := (descriptorPairWeight_bounds w₀ Q ρ m N σ J i a B S hcover hd
        (by norm_num : (0:ℝ) < 1) z hz).2
      simp only [Real.one_rpow] at hb
      exact mul_le_of_le_one_right (sq_nonneg _) hb
    · rw [indicator_of_notMem hgood]
      have hw : descriptorPairWeight w₀ Q ρ m N σ J i a B S z = 0 := by
        by_contra hn
        have hp : descriptorProduct Q ρ (fun u => m (u/N)) N σ J i B S z.1
            (normalizeToSphere w₀ (z.1-z.2)) *
            descriptorProduct Q ρ (fun u => m (u/N)) N σ J i B S z.2
            (normalizeToSphere w₀ (z.1-z.2)) ≠ 0 := by
          intro hp
          apply hn
          simp only [descriptorPairWeight,mul_assoc,hp,mul_zero]
        exact hgood (descriptorPairTests_mono w₀ Q ρ _ N σ J (i+1) hsub
          (descriptorProduct_pair_support w₀ Q ρ _ N σ J i B S hcover hp))
      simp only [hw,mul_zero,ENNReal.ofReal_zero,le_refl]
  have hm := Measure.map_mono hh
    (show Measurable (fun z : Space d × Space d => dist z.1 z.2) by fun_prop)
  rw [Measure.map_smul] at hm
  simpa only [maskedCellDistance,testedCellDistance,testedCellPair,K,π,G] using hm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_MaskedLowBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact normalization of the positive low-shell reduction

There is no comparison of different model masses in this step: parent and
child retain the same start depth and the same `profileModelMass`.
-/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

 theorem masked_distance_low_band (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ)
    (σ : ℝ) (J i a v : ℕ) (hav : a ≤ v)
    (B B' : Finset PlanarFalconer.PolicyDescriptor) (hsub : B' ⊆ B)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (hd : 1 ≤ d) (X Y : DyadicCube d)
    (hsep : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
      1 ≤ dist z.1 z.2*(2:ℝ)^a)
    [IsFiniteMeasure (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y)] :
    (1/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^v) ((2:ℝ)^v),
      ‖charFun (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) r‖^2 ≤
    (32*PlanarFalconer.binKernelConstant.toReal) *
      ((2:ℝ)^N)^(4*m ((a:ℝ)/N))*(2:ℝ)^(v-a) *
      ((testedCellDistance ρ ρ X Y
        (descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J (i+1) B')).prod
        (testedCellDistance ρ ρ X Y
          (descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J (i+1) B'))).real
            {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^v} := by
  let θ := testedCellDistance ρ ρ X Y
    (descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J (i+1) B')
  have hdom := maskedCellDistance_le_tested w₀ Q ρ m N σ J i a B B' hsub S hcover hd X Y hsep
    (descriptorPairTests_measurable w₀ Q ρ _ N σ J (i+1) B')
  have hband := dominated_real_frequency_band
    (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) θ
    (by positivity : 0 < (2:ℝ)^v) (sq_nonneg ((profileModelMass m N a)⁻¹)) hdom
  have hm : (((profileModelMass m N a)⁻¹)^2)^2 = ((2:ℝ)^N)^(4*m ((a:ℝ)/N)) := by
    rw [← pow_mul]
    exact profileModelMass_inverse_four m N a
  rw [hm] at hband
  have hcollision : (θ.prod θ).real {z : ℝ × ℝ | |z.1-z.2| ≤ 1/(2:ℝ)^v} ≤
      (θ.prod θ).real {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^v} := by
    apply measureReal_mono (h₂ := measure_ne_top (θ.prod θ) _)
    intro z hz
    change |z.1-z.2| ≤ 1/(2:ℝ)^v at hz
    change |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^v
    apply hz.trans
    exact div_le_div_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α := ℝ) d]) (by positivity)
  have h := hband.trans (mul_le_mul_of_nonneg_left hcollision (by positivity))
  apply (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 1/(2:ℝ)^a)).trans_eq
  rw [show (2:ℝ)^v = (2:ℝ)^a*(2:ℝ)^(v-a) by rw [← pow_add,Nat.add_sub_of_le hav]]
  field_simp
  rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyLowBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive low-prefix transition for the actual policy list -/

namespace Falconer
open Set MeasureTheory

 theorem policy_masked_distance_low_band {d : ℕ}
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (A : ℕ → ℝ) (N : ℕ) (σ : ℝ) (J i q a t v : ℕ)
    (hav : a ≤ v) (hvt : v ≤ t)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ PlanarFalconer.policyDescriptorList A N q a t, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (hd : 1 ≤ d) (X Y : List (Fin d → Bool))
    (hsep : ∀ᵐ z ∂(ρ.restrict (Q.descendant X).carrier).prod (ρ.restrict (Q.descendant Y).carrier),
      1 ≤ dist z.1 z.2*(2:ℝ)^a)
    [IsFiniteMeasure (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
      (Q.descendant X) (Q.descendant Y))] :
    (1/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^v) ((2:ℝ)^v),
      ‖charFun (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
        (Q.descendant X) (Q.descendant Y)) r‖^2 ≤
      (32*PlanarFalconer.binKernelConstant.toReal) *
        (positiveCollisionCount w₀ Q ρ (fun u => m (u/N)) A N σ J (i+1) q a v X Y).toReal := by
  let : IsFiniteMeasure (maskedCellDistance w₀ Q ρ m N σ J i a
      (PlanarFalconer.policyDescriptorList A N q a t) S (Q.descendant X) (Q.descendant Y)) := by
    change IsFiniteMeasure (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
      (Q.descendant X) (Q.descendant Y))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have h := masked_distance_low_band w₀ Q ρ m N σ J i a v hav
    (PlanarFalconer.policyDescriptorList A N q a t)
    (PlanarFalconer.policyDescriptorList A N q a v)
    (PlanarFalconer.policyDescriptorList_mono A (N := N) (q := q) le_rfl hvt)
    S hcover hd (Q.descendant X) (Q.descendant Y) hsep
  simp only [policyMaskedDistance,positiveCollisionCount,policyTestPairs,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show 0 ≤ (2:ℝ)^(v-a)*((2:ℝ)^N)^(4*m ((a:ℝ)/N)) by positivity)]
  simpa only [measureReal_def,mul_assoc,mul_left_comm,mul_comm] using h

theorem policy_masked_distance_low_frequency {d : ℕ}
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d))
    {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m)
    (A : ℕ → ℝ) (σ : ℝ) (J i q a t : ℕ) (ha : a ≤ N) (hat : a ≤ t)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ PlanarFalconer.policyDescriptorList A N q a t, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (hd : 1 ≤ d) (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (hsep : ∀ᵐ z ∂(ρ.restrict (Q.descendant X).carrier).prod (ρ.restrict (Q.descendant Y).carrier),
      1 ≤ dist z.1 z.2*(2:ℝ)^a)
    [IsFiniteMeasure (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
      (Q.descendant X) (Q.descendant Y))] :
    (1/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^a) ((2:ℝ)^a),
      ‖charFun (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
        (Q.descendant X) (Q.descendant Y)) r‖^2 ≤
      (32*PlanarFalconer.binKernelConstant.toReal) *
        ((2:ℝ)^N)^(4*((d:ℝ)+1)*lam) := by
  let := hreg.probability
  have h := policy_masked_distance_low_band w₀ Q ρ m A N σ J i q a t a le_rfl hat
    S hcover hd X Y hsep
  have hb := positiveCollisionCount_regularized w₀ Q ρ hreg A σ J (i+1) q (t := a) ha X Y hX hY
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simp only [Nat.sub_self,pow_zero,one_mul,ENNReal.toReal_ofReal (by positivity :
    0 ≤ ((2:ℝ)^N)^(4*((d:ℝ)+1)*lam))] at hr
  exact h.trans (mul_le_mul_of_nonneg_left hr (by positivity))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_MaskedGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed dimensional weight bounds in separated dyadic cells -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

 theorem DyadicCube.separated_pairs_upper (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    (hsep : ‖P.center-Q.center‖ ≤ 2000*((d:ℝ)+1)*P.side)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    dist x y ≤ 2002*((d:ℝ)+1)*P.side := by
  have hQp : 0 < Q.side := by rwa [hQ]
  have h₁ := P.dist_le hP.le hx (P.center_mem hP)
  have h₂ := Q.dist_le hQp.le (Q.center_mem hQp) hy
  rw [hQ] at h₂
  have hxy : dist x y ≤ dist x P.center+dist P.center Q.center+dist Q.center y :=
    (dist_triangle x P.center y).trans (by
      linarith [dist_triangle P.center Q.center y])
  have hs := mul_le_mul_of_nonneg_right (sqrt_dimension_le d) hP.le
  simp only [dist_eq_norm] at hxy h₁ h₂
  rw [dist_eq_norm]
  linarith

 theorem separated_cell_distance_bounds (Q : DyadicCube d) (hQ : Q.side = 1)
    (a : ℕ) (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (hlo : 125*((d:ℝ)+1)*(Q.descendant X).side ≤
      ‖(Q.descendant X).center-(Q.descendant Y).center‖)
    (hhi : ‖(Q.descendant X).center-(Q.descendant Y).center‖ ≤
      2000*((d:ℝ)+1)*(Q.descendant X).side)
    {x y : Space d} (hx : x ∈ (Q.descendant X).carrier) (hy : y ∈ (Q.descendant Y).carrier) :
    100*((d:ℝ)+1) ≤ dist x y*(2:ℝ)^a ∧
      dist x y*(2:ℝ)^a ≤ 2002*((d:ℝ)+1) := by
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hside : (Q.descendant Y).side = (Q.descendant X).side := by
    rw [Q.descendant_side,Q.descendant_side,hX,hY]
  have hpx : (Q.descendant X).side = 1/(2:ℝ)^a := by rw [Q.descendant_side,hX,hQ]
  have hl := (Q.descendant X).separated_pairs_lower (Q.descendant Y)
    (Q.descendant_side_pos hQpos X) hside hlo hx hy
  have hu := (Q.descendant X).separated_pairs_upper (Q.descendant Y)
    (Q.descendant_side_pos hQpos X) hside hhi hx hy
  rw [hpx,← dist_eq_norm] at hl
  rw [hpx] at hu
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^a)).mp
    simpa only [mul_one,div_eq_mul_inv,mul_assoc,one_mul] using hl
  · apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^a)).mp
    simpa only [mul_one,div_eq_mul_inv,mul_assoc,one_mul] using hu

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyPrefixLowpass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive prefix lowpass inequality with the actual old masks -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

 theorem uniform_policy_prefix_lowpass (d : ℕ) (hd : 1 ≤ d)
    {σ : ℝ} (hσ : 0 < σ) {J : ℕ} (hJ : 0 < J) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (w₀ : Sphere d) (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (A : ℕ → ℝ)
        (q i a t : ℕ), 0 < q → t ≤ N → a ≤ t →
      ∀ (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)),
      (∀ b ∈ PlanarFalconer.policyDescriptorList A N q a t, ∀ w : Sphere d,
        ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2) →
      ∀ (X Y : List (Fin d → Bool)), X.length = a → Y.length = a →
      125*((d:ℝ)+1)*(Q.descendant X).side ≤
        ‖(Q.descendant X).center-(Q.descendant Y).center‖ →
      ‖(Q.descendant X).center-(Q.descendant Y).center‖ ≤
        2000*((d:ℝ)+1)*(Q.descendant X).side →
      (positiveCollisionCount w₀ Q ρ (fun u => m (u/N)) A N σ J i q a t X Y).toReal ≤
        (C/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^t) ((2:ℝ)^t),
          ‖charFun (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
            (Q.descendant X) (Q.descendant Y)) r‖^2 := by
  obtain ⟨C₀,hC₀,hband⟩ := dyadic_collision_fourier_of_domination d
  obtain ⟨N₀,h₀⟩ := uniform_maskedCellDistance_dominates hσ hJ hd
  let U : ℝ := 2002*((d:ℝ)+1)
  let c : ℝ := U^(-(((d:ℝ)-1)/2))
  have hU : 0 < U := by dsimp [U]; positivity
  have hc : 0 < c := Real.rpow_pos_of_pos hU _
  refine ⟨C₀/c^2,by positivity,N₀,?_⟩
  intro N hN w₀ Q hQ ρ _ m A q i a t hq ht hat S hcover X Y hX hY hlo hhi
  let B := PlanarFalconer.policyDescriptorList A N q a t
  let π := (ρ.restrict (Q.descendant X).carrier).prod (ρ.restrict (Q.descendant Y).carrier)
  have hgeo : ∀ᵐ z ∂π, 100*((d:ℝ)+1) ≤ dist z.1 z.2*(2:ℝ)^a ∧
      dist z.1 z.2*(2:ℝ)^a ≤ U := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (Q.descendant X).measurable),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (Q.descendant Y).measurable)] with z hx hy
    exact separated_cell_distance_bounds Q hQ a X Y hX hY hlo hhi hx hy
  have hpositive : ∀ᵐ z ∂π, 0 < dist z.1 z.2*(2:ℝ)^a ∧
      dist z.1 z.2*(2:ℝ)^a ≤ U := hgeo.mono fun _ hz =>
    ⟨(by positivity : (0:ℝ) < 100*((d:ℝ)+1)).trans_le hz.1,hz.2⟩
  have hsep : ∀ᵐ z ∂π, 1 ≤ dist z.1 z.2*(2:ℝ)^a := hgeo.mono fun _ hz =>
    (by nlinarith [Nat.cast_nonneg (α := ℝ) d] : (1:ℝ) ≤ 100*((d:ℝ)+1)).trans hz.1
  have hf := maskedCellDistance_finite w₀ Q ρ m N σ J i a B S hcover hd
    (by norm_num : (0:ℝ) < 1) (Q.descendant X) (Q.descendant Y) hsep
  let := hf
  have hdom := h₀ N hN Q hQ ρ m B (fun b hb => policy_descriptor_valid A hq ht hb)
    S hcover i a w₀ X Y U hU hpositive
  have hbound := hband
    (testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
      (descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J i B))
    (maskedCellDistance w₀ Q ρ m N σ J i a B S (Q.descendant X) (Q.descendant Y))
    ((profileModelMass m N a)⁻¹^2*c) (by positivity) hdom a t hat
  have he : ((profileModelMass m N a)⁻¹^2*c)^2 = c^2*((2:ℝ)^N)^(4*m ((a:ℝ)/N)) := by
    rw [mul_pow,← pow_mul,show 2*2 = 4 from rfl,profileModelMass_inverse_four]
    ring
  rw [he] at hbound
  have hn : c^2*(positiveCollisionCount w₀ Q ρ (fun u => m (u/N)) A N σ J i q a t X Y).toReal ≤
      (C₀/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^t) ((2:ℝ)^t),
        ‖charFun (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
          (Q.descendant X) (Q.descendant Y)) r‖^2 := by
    simp only [positiveCollisionCount,policyTestPairs,policyMaskedDistance,
      ENNReal.toReal_mul,ENNReal.toReal_ofReal (show 0 ≤ (2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m ((a:ℝ)/N)) by positivity)]
    simpa only [B,measureReal_def,mul_assoc,mul_left_comm,mul_comm] using hbound
  calc
    _ ≤ ((C₀/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^t) ((2:ℝ)^t),
        ‖charFun (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
          (Q.descendant X) (Q.descendant Y)) r‖^2)/c^2 :=
      (le_div_iff₀ (sq_pos_of_pos hc)).mpr (by simpa only [mul_comm] using hn)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_FourierBandDecomposition
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem fourier_band_split (μ : Measure ℝ) [IsFiniteMeasure μ]
    {L H : ℝ} (hL : 0 ≤ L) (hLH : L ≤ H) :
    (∫ r in Icc (-H) H, ‖charFun μ r‖^2) =
      (∫ r in Icc (-L) L, ‖charFun μ r‖^2)+2*(∫ r in Icc L H, ‖charFun μ r‖^2) := by
  have hc : Continuous (fun r : ℝ => ‖charFun μ r‖^2) := continuous_charFun.norm.pow 2
  have hset (x y : ℝ) (hxy : x ≤ y) :
      (∫ r in Icc x y, ‖charFun μ r‖^2) = ∫ r in x..y, ‖charFun μ r‖^2 := by
    rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hxy]
  have heven (u : ℝ) :
      (∫ r in -u..0, ‖charFun μ r‖^2) = ∫ r in 0..u, ‖charFun μ r‖^2 := by
    have he := intervalIntegral.integral_comp_neg (f := fun r => ‖charFun μ r‖^2) (a := 0) (b := u)
    simpa only [fourier_energy_even,neg_zero] using he.symm
  have hband (u : ℝ) : (∫ r in -u..u, ‖charFun μ r‖^2) =
      2*(∫ r in 0..u, ‖charFun μ r‖^2) := by
    have he := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) (a := -u) (b := 0)) (hc.intervalIntegrable (μ := volume) (a := 0) (b := u))
    rw [heven] at he
    linarith
  rw [hset _ _ (by linarith),hset _ _ (by linarith),hset _ _ hLH,hband,hband]
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (a := 0) (b := L)) (hc.intervalIntegrable (μ := volume) (a := L) (b := H))
  linarith

theorem fourier_dyadic_band_decomposition (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a t : ℕ} (hat : a ≤ t) :
    (∫ r in Icc (-((2:ℝ)^t)) ((2:ℝ)^t), ‖charFun μ r‖^2) =
      (∫ r in Icc (-((2:ℝ)^a)) ((2:ℝ)^a), ‖charFun μ r‖^2)+
      2*∑ v ∈ Finset.Ioc a t,
        ∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2 := by
  induction t,hat using Nat.le_induction with
  | base => simp
  | succ t hat ih =>
    rw [Finset.sum_Ioc_succ_top hat]
    have hs := fourier_band_split μ (L := (2:ℝ)^t) (H := (2:ℝ)^(t+1))
      (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_succ t))
    rw [ih] at hs
    have he : ((t+1:ℕ):ℝ)-1 = (t:ℝ) := by push_cast; ring
    rw [he,Real.rpow_natCast]
    linarith

theorem fourier_shell_le_band (μ : Measure ℝ) [IsFiniteMeasure μ] (v : ℕ) :
    (∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2) ≤
      ∫ r in Icc (-((2:ℝ)^v)) ((2:ℝ)^v), ‖charFun μ r‖^2 := by
  apply setIntegral_mono_set
    ((continuous_charFun.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall fun r => sq_nonneg ‖charFun μ r‖)
  exact Filter.Eventually.of_forall (fun r hr => ⟨by linarith [hr.1,Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) ((v:ℝ)-1),pow_pos (by norm_num : (0:ℝ)<2) v],hr.2⟩)

theorem fourier_shell_le_expanded (μ : Measure ℝ) [IsFiniteMeasure μ] (v : ℕ) :
    (∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2) ≤
      ∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^((v:ℝ)+1)), ‖charFun μ r‖^2 := by
  apply setIntegral_mono_set
    ((continuous_charFun.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall fun r => sq_nonneg ‖charFun μ r‖)
  apply Filter.Eventually.of_forall
  intro r hr
  refine ⟨hr.1,hr.2.trans ?_⟩
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_FourierBandBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem finite_fourier_band_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a t N : ℕ} (hat : a ≤ t) (htN : t ≤ N) {B : ℝ} (hB : 0 ≤ B)
    (hbase : (2:ℝ)^(-(a:ℝ))*(∫ r in Icc (-((2:ℝ)^a)) ((2:ℝ)^a), ‖charFun μ r‖^2) ≤ B)
    (hshell : ∀ v ∈ Finset.Ioc a t,
      (2:ℝ)^(-(a:ℝ))*(∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2) ≤ B) :
    (2:ℝ)^(-(a:ℝ))*(∫ r in Icc (-((2:ℝ)^t)) ((2:ℝ)^t), ‖charFun μ r‖^2) ≤
      (1+2*(N:ℝ))*B := by
  have hsum := Finset.sum_le_sum hshell
  rw [Finset.sum_const,nsmul_eq_mul] at hsum
  have hcard : ((Finset.Ioc a t).card:ℝ) ≤ (N:ℝ) := by
    rw [Nat.card_Ioc]
    exact_mod_cast (show t-a ≤ N by omega)
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hcard hB)
  rw [fourier_dyadic_band_decomposition μ hat]
  have he : (2:ℝ)^(-(a:ℝ))*(2*∑ v ∈ Finset.Ioc a t,
      ∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2) =
      2*∑ v ∈ Finset.Ioc a t, (2:ℝ)^(-(a:ℝ))*
        (∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2) := by
    rw [← Finset.mul_sum]
    ring
  rw [mul_add,he]
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PolicyPositiveBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive policy count from its actual Fourier bands -/

namespace Falconer
open Set MeasureTheory

namespace PolicyJetData
variable {m : ℕ}

theorem root_list (P : PolicyJetData m) (hleft : P.a₀ = P.a) (hright : P.t₀ = P.t) :
    P.list = PlanarFalconer.policyDescriptorList P.policy P.N P.q P.a P.t := by
  unfold list PlanarFalconer.remainingPolicyDescriptors
  rw [hleft,hright]
  apply Finset.filter_eq_self.mpr
  intro b hb
  exact PlanarFalconer.policyDescriptor_anchor_gt_left P.policy P.q_pos hb

end PolicyJetData

theorem exists_policy_positive_band_bound (m : ℕ) {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
      ∀ P : PolicyJetData m, P.σ = σ → P.J = J → N₀ ≤ P.N →
      P.a₀ = P.a → P.t₀ = P.t → P.a ≤ P.t →
      (∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
        2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side →
      ∀ (w₀ : Sphere (m+3)) (D H : ℝ), 0 ≤ D → 0 ≤ H →
      (∀ v ∈ Finset.Ioc P.a P.t, σ*P.N ≤ (P.t:ℝ)-v →
        (positiveCollisionCount w₀ P.Q P.ρ (fun u => P.profile (u/P.N)) P.policy
          P.N P.σ P.J (P.i+1) P.q P.a v P.X P.Y).toReal ≤ D) →
      (∀ v ∈ Finset.Ioc P.a P.t, (P.t:ℝ)-v < σ*P.N →
        (2:ℝ)^(-(P.a:ℝ))*(∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^((v:ℝ)+1)),
          ‖charFun (P.maskedLaw w₀) r‖^2) ≤ H) →
      P.positiveCount w₀ ≤ C*(1+2*(P.N:ℝ))*
        (((2:ℝ)^P.N)^(4*(((m+3:ℕ):ℝ)+1)*P.lam)+D+H) := by
  obtain ⟨C₀,hC₀,N₀,hfourier⟩ := uniform_policy_prefix_lowpass (m+3) (by omega) hσ hJ
  let c : ℝ := 32*PlanarFalconer.binKernelConstant.toReal
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨C₀*(1+c),by positivity,N₀,?_⟩
  intro P hσP hJP hN hleft hright hat hcover hlo hhi w₀ D H hD hH hlow hhigh
  let := P.regular.probability
  have htN : P.t ≤ P.N := by rw [← hright]; exact P.base_N
  have hlist := P.root_list hleft hright
  have hcover' : ∀ b ∈ PlanarFalconer.policyDescriptorList P.policy P.N P.q P.a P.t,
      ∀ w : Sphere (m+3), ∃ c ∈ P.masks b, dist w c ≤ descriptorMaskRadius P.N P.σ b/2 := by
    simpa only [← hlist] using hcover
  have hsep : ∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
      (P.ρ.restrict (P.Q.descendant P.Y).carrier), 1 ≤ dist z.1 z.2*(2:ℝ)^P.a := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem (P.Q.descendant P.X).measurable),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (P.Q.descendant P.Y).measurable)] with z hx hy
    have hb := separated_cell_distance_bounds P.Q P.unit P.a P.X P.Y
      P.X_length P.Y_length hlo hhi hx hy
    exact (by have := Nat.cast_nonneg (α := ℝ) (m+3); nlinarith :
      (1:ℝ) ≤ 100*(((m+3:ℕ):ℝ)+1)).trans hb.1
  let := maskedCellDistance_finite w₀ P.Q P.ρ P.profile P.N P.σ P.J P.i P.a
    P.list P.masks hcover (by omega) (by norm_num : (0:ℝ) < 1)
    (P.Q.descendant P.X) (P.Q.descendant P.Y) hsep
  have hlaw : P.maskedLaw w₀ = policyMaskedDistance w₀ P.Q P.ρ P.profile P.policy
      P.N P.σ P.J P.i P.q P.a P.t P.masks (P.Q.descendant P.X) (P.Q.descendant P.Y) := by
    unfold PolicyJetData.maskedLaw policyMaskedDistance
    rw [hlist]
  let : IsFiniteMeasure (P.maskedLaw w₀) := by unfold PolicyJetData.maskedLaw; infer_instance
  let : IsFiniteMeasure (policyMaskedDistance w₀ P.Q P.ρ P.profile P.policy
      P.N P.σ P.J P.i P.q P.a P.t P.masks (P.Q.descendant P.X) (P.Q.descendant P.Y)) := by
    rw [← hlaw]; infer_instance
  let F : ℝ := ((2:ℝ)^P.N)^(4*(((m+3:ℕ):ℝ)+1)*P.lam)
  let B : ℝ := F+D+H
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hFB : F ≤ B := by dsimp [B]; linarith
  have hDB : D ≤ B := by dsimp [B]; linarith
  have hHB : H ≤ B := by dsimp [B]; linarith
  have hbase := policy_masked_distance_low_frequency w₀ P.Q P.ρ P.regular P.policy
    P.σ P.J P.i P.q P.a P.t (hat.trans htN) hat P.masks hcover' (by omega)
    P.X P.Y P.X_length P.Y_length hsep
  have hbase' : (2:ℝ)^(-(P.a:ℝ))*(∫ r in Icc (-((2:ℝ)^P.a)) ((2:ℝ)^P.a),
      ‖charFun (P.maskedLaw w₀) r‖^2) ≤ (1+c)*B := by
    rw [hlaw]
    have hp : (2:ℝ)^(-(P.a:ℝ)) = 1/(2:ℝ)^P.a := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
    rw [hp]
    exact hbase.trans (by change c*F ≤ _; nlinarith [mul_nonneg hc (sub_nonneg.mpr hFB)])
  have hshell : ∀ v ∈ Finset.Ioc P.a P.t,
      (2:ℝ)^(-(P.a:ℝ))*(∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v),
        ‖charFun (P.maskedLaw w₀) r‖^2) ≤ (1+c)*B := by
    intro v hv
    by_cases hgap : σ*P.N ≤ (P.t:ℝ)-v
    · have hb := policy_masked_distance_low_band w₀ P.Q P.ρ P.profile P.policy P.N P.σ
        P.J P.i P.q P.a P.t v (Finset.mem_Ioc.mp hv).1.le (Finset.mem_Ioc.mp hv).2
        P.masks hcover' (by omega) P.X P.Y hsep
      have hsmall := mul_le_mul_of_nonneg_left (PlanarFalconer.fourier_shell_le_band (P.maskedLaw w₀) v)
        (show 0 ≤ (2:ℝ)^(-(P.a:ℝ)) by positivity)
      have hp : (2:ℝ)^(-(P.a:ℝ)) = 1/(2:ℝ)^P.a := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
      rw [hlaw,hp] at hsmall
      have hb' : _ ≤ (1+c)*B := (hsmall.trans hb).trans (by
        have hh := hlow v hv hgap
        change c*_ ≤ (1+c)*B
        nlinarith [mul_nonneg hc (sub_nonneg.mpr (hh.trans hDB))])
      simpa only [hlaw,hp] using hb'
    · exact (mul_le_mul_of_nonneg_left (PlanarFalconer.fourier_shell_le_expanded (P.maskedLaw w₀) v)
        (show 0 ≤ (2:ℝ)^(-(P.a:ℝ)) by positivity)).trans
        ((hhigh v hv (lt_of_not_ge hgap)).trans (by nlinarith [mul_nonneg hc hB]))
  have hband := PlanarFalconer.finite_fourier_band_bound (P.maskedLaw w₀) hat htN
    (mul_nonneg (by positivity) hB) hbase' hshell
  have hf := hfourier P.N hN w₀ P.Q P.unit P.ρ P.profile P.policy P.q P.i P.a P.t
    P.q_pos htN hat P.masks (by simpa only [hσP] using hcover') P.X P.Y
    P.X_length P.Y_length hlo hhi
  rw [← hσP,← hJP,← hlaw] at hf
  have hp : C₀/(2:ℝ)^P.a = C₀*(2:ℝ)^(-(P.a:ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,div_eq_mul_inv]
  rw [hp,mul_assoc] at hf
  apply hf.trans
  convert mul_le_mul_of_nonneg_left hband hC₀.le using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [B,F]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PolicyPrefixShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual high-prefix shell reduces to retained-mask child states -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap
open PlanarFalconer (PolicyDescriptor policyDepth)

namespace PolicyJetData
variable {m : ℕ}

theorem directWeight_shift (P : PolicyJetData m) (p : ℕ) (lam σ ε δ : ℝ) :
    ((2:ℝ)^P.N)^δ*P.directWeight p lam σ ε = P.directWeight p lam σ (ε+δ) := by
  unfold directWeight
  rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^P.N)]
  congr 1
  ring

end PolicyJetData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyCommonBudgets
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One derivative budget for positive and angular policy steps -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap
open PlanarFalconer (policyDepth)

theorem exists_policy_positive_common_budgets_oai
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ ε : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    {J : ℕ} (hJ : 0 < J) (T : ℝ)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ := 0) :
    ∃ K : ℕ, minJet ≤ K ∧ ∀ minOrder : ℕ, ∃ (L : ℕ) (Z : ℝ) (N₀ : ℕ), minOrder ≤ L ∧ 1 ≤ Z ∧
      PolicyGraphBound m K L J lam σ ((ε/2)/2) ((T+ε/2)+1+(ε/2)/2) Z N₀ Ψ ∧
      ∀ P : PolicyJetData m, P.σ = σ → P.lam = lam → P.J = J → P.Z = Z → N₀ ≤ P.N →
      P.i+1 ≤ P.J → P.a₀ = P.a → P.t₀ = P.t → P.a+100*P.q < P.t →
      P.σ*(P.N:ℝ) ≤ P.q →
      2*policyDepth P.policy P.N P.q P.a P.t ≤ P.a+P.t →
      (∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
        2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side →
      ∀ (w₀ : Sphere (m+3)) (M : ℝ), 0 ≤ M →
      ((2:ℝ)^P.N)^(4*(((m+3:ℕ):ℝ)+1)*lam+ε) ≤ M →
      (∀ v ∈ Finset.Ioc P.a P.t, σ*P.N ≤ (P.t:ℝ)-v →
        ((2:ℝ)^P.N)^ε*(positiveCollisionCount w₀ P.Q P.ρ
          (fun u => P.profile (u/P.N)) P.policy P.N P.σ P.J (P.i+1) P.q P.a v P.X P.Y).toReal ≤ M) →
      (∀ v, ∀ hv : v ∈ Finset.Ioc P.a P.t, (P.t:ℝ)-v < σ*P.N →
        ∀ p, p = policyDepth P.policy P.N P.q P.a P.t → ∀ hap : P.a ≤ p,
        ∀ row, ∀ hrow : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a),
        P.directWeight p lam σ ε *
          ((P.atFrequency v ((Finset.mem_Ioc.mp hv).2.trans P.base_right)).child p hap row hrow).envelope K L Ψ ≤ M) →
      P.positiveCount w₀ ≤ 3*M+((2:ℝ)^P.N)^(-T) := by
  let δ : ℝ := 100*(((m+3:ℕ):ℝ)+1)
  let W : ℝ := 2002*(((m+3:ℕ):ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  obtain ⟨K,hminJet,hcommon⟩ := exists_policy_prefix_common_budgets
    hgnomonic hquadratic m hlam hσ hσ1 (half_pos hε) hJ (T+ε/2) δ W hδ hW
    φ Ψ hφ hΨ hpos hzero hone hV hΨV hsupp minJet
  refine ⟨K,hminJet,?_⟩
  intro minOrder
  obtain ⟨L,Z,Nshell,hL,hZ,hgraph,hshell⟩ := hcommon minOrder
  obtain ⟨C,hC,Nband,hband⟩ := exists_policy_positive_band_bound m hσ hJ
  obtain ⟨Ncost,hcost⟩ := PlanarFalconer.fixed_linear_subpower C hC.le (half_pos hε)
  refine ⟨L,Z,max Nshell (max Nband Ncost),hL,hZ,?_,?_⟩
  · intro P hLam hσP hJP hZP hN
    exact hgraph P hLam hσP hJP hZP ((le_max_left _ _).trans hN)
  · intro P hσP hLam hJP hZP hN hi hleft hright hwide hq hprefix hcover hlo hhi w₀ M hM hfloor hlow hchildren
    let := P.regular.probability
    let R : ℝ := (2:ℝ)^P.N
    let c : ℝ := R^(ε/2)
    have hc : 0 < c := by dsimp [c,R]; positivity
    have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
    have hRpos : 0 < R := zero_lt_one.trans_le hR
    have hsep : ∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (P.ρ.restrict (P.Q.descendant P.Y).carrier),
        δ ≤ dist z.1 z.2*(2:ℝ)^P.a ∧ dist z.1 z.2*(2:ℝ)^P.a ≤ W := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae
        (ae_restrict_mem (P.Q.descendant P.X).measurable),
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (P.Q.descendant P.Y).measurable)] with z hx hy
      exact separated_cell_distance_bounds P.Q P.unit P.a P.X P.Y
        P.X_length P.Y_length hlo hhi hx hy
    have hD : 0 ≤ M/c := div_nonneg hM hc.le
    have hlow' : ∀ v ∈ Finset.Ioc P.a P.t, σ*P.N ≤ (P.t:ℝ)-v →
        (positiveCollisionCount w₀ P.Q P.ρ (fun u => P.profile (u/P.N)) P.policy
          P.N P.σ P.J (P.i+1) P.q P.a v P.X P.Y).toReal ≤ M/c := by
      intro v hv hg
      apply (le_div_iff₀ hc).mpr
      have hp : c ≤ R^ε := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
      exact (mul_le_mul_of_nonneg_left hp ENNReal.toReal_nonneg).trans
        (by simpa only [mul_comm] using hlow v hv hg)
    have hhigh' : ∀ v ∈ Finset.Ioc P.a P.t, (P.t:ℝ)-v < σ*P.N →
        (2:ℝ)^(-(P.a:ℝ))*(∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^((v:ℝ)+1)),
          ‖charFun (P.maskedLaw w₀) r‖^2) ≤ M/c+R^(-(T+ε/2)) := by
      intro v hv hg
      let P' := P.atFrequency v ((Finset.mem_Ioc.mp hv).2.trans P.base_right)
      have hhigh : (P'.t₀:ℝ) ≤ P'.t+P'.σ*P'.N := by
        change (P.t₀:ℝ) ≤ (v:ℝ)+P.σ*P.N
        rw [hright,hσP]
        linarith
      have hwide' : P'.a+100*P'.q < P'.t₀ := by change P.a+100*P.q < P.t₀; rwa [hright]
      have hprefix' : 2*policyDepth P'.policy P'.N P'.q P'.a P'.t₀ ≤ P'.a+P'.t₀ := by
        change 2*policyDepth P.policy P.N P.q P.a P.t₀ ≤ P.a+P.t₀
        rwa [hright]
      let geometry := P'.prefixGeometry (by change 0 < P.σ; rwa [hσP]) hleft hwide' hq hhigh hprefix'
      have hh : ∀ row, ∀ hrow : row ∈
          (P'.Q.descendant P'.X).occupiedPaths P'.ρ (geometry.p-P'.a) ×ˢ
            (P'.Q.descendant P'.Y).occupiedPaths P'.ρ (geometry.p-P'.a),
          P'.directWeight geometry.p lam σ (ε/2)*
            (P'.child geometry.p geometry.ap row hrow).envelope K L Ψ ≤ M/c := by
        intro row hrow
        apply (le_div_iff₀ hc).mpr
        have hp : geometry.p = policyDepth P.policy P.N P.q P.a P.t := by
          change policyDepth P.policy P.N P.q P.a P.t₀ = _
          rw [hright]
        have hw : c*P'.directWeight geometry.p lam σ (ε/2) = P.directWeight geometry.p lam σ ε := by
          change ((2:ℝ)^P'.N)^(ε/2)*P'.directWeight geometry.p lam σ (ε/2) = _
          rw [P'.directWeight_shift]
          have he : ε/2+ε/2 = ε := by ring
          rw [he]
          rfl
        calc
          _ = (c*P'.directWeight geometry.p lam σ (ε/2))*
              (P'.child geometry.p geometry.ap row hrow).envelope K L Ψ := by ring
          _ ≤ M := by rw [hw]; exact hchildren v hv hg geometry.p hp geometry.ap row hrow
      exact hshell P' hσP hLam hJP hZP ((le_max_left _ _).trans hN) hi hcover hsep hlo
        hleft hwide' hq hhigh hprefix' (M/c) hD hh w₀
    have hF : R^(4*(((m+3:ℕ):ℝ)+1)*P.lam) ≤ M/c := by
      apply (le_div_iff₀ hc).mpr
      calc
        _ = R^(4*(((m+3:ℕ):ℝ)+1)*lam+ε/2) := by
          rw [hLam,← Real.rpow_add hRpos]
        _ ≤ R^(4*(((m+3:ℕ):ℝ)+1)*lam+ε) :=
          Real.rpow_le_rpow_of_exponent_le hR (by linarith)
        _ ≤ M := hfloor
    have hb := hband P hσP hJP ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
      hleft hright (by omega) hcover hlo hhi w₀ (M/c) (M/c+R^(-(T+ε/2))) hD
      (by positivity) hlow' hhigh'
    have hcost' := hcost P.N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
    have herr : c*R^(-(T+ε/2)) = R^(-T) := by
      dsimp [c]
      rw [← Real.rpow_add hRpos]
      congr 1
      ring
    calc
      _ ≤ C*(1+2*(P.N:ℝ))*(3*(M/c)+R^(-(T+ε/2))) := by
        apply hb.trans
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        change R^(4*(((m+3:ℕ):ℝ)+1)*P.lam)+M/c+(M/c+R^(-(T+ε/2))) ≤ _
        linarith
      _ ≤ c*(3*(M/c)+R^(-(T+ε/2))) :=
        mul_le_mul_of_nonneg_right hcost' (by positivity)
      _ = 3*M+R^(-T) := by
        rw [mul_add,herr]
        congr 1
        field_simp

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.exists_policy_positive_common_budgets_oai := @OAI.Falconer.exists_policy_positive_common_budgets_oai
