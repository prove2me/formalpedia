-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.formal_pair
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:49:49.581491+00:00
-- url     : https://prove2.me/submissions/4aa68574-880d-4b70-a206-d511fa02e064

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI007
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_CrosscapCoordinateStrip_normalized_defect_rectangle_framed

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveTransverseVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth curve in three-space admits one constant vector transverse
to every nonzero velocity.  This uses the proved two-dimensional image estimate. -/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma curve_transverse_vector_independent {v a : Fin 3 → ℝ}
    (hv : v ≠ 0) (ha : ∀ r : ℝ, r • v ≠ a) : LinearIndependent ℝ ![v,a] :=
  (LinearIndependent.pair_iff' hv).mpr ha

lemma curve_transverse_cross_ne_zero {v a : Fin 3 → ℝ}
    (hv : v ≠ 0) (ha : ∀ r : ℝ, r • v ≠ a) : v ⨯₃ a ≠ 0 :=
  crossProduct_ne_zero_iff_linearIndependent.mpr (curve_transverse_vector_independent hv ha)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveNormalFrame
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit invertible three-dimensional frame along a regular curve. -/
noncomputable section
open Set Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma curveNormalLinear_apply (v a : Fin 3 → ℝ) (z : Base × ℝ) :
    curveNormalLinear v a z = z.2 • v+z.1 0 • a+z.1 1 • (v ⨯₃ a) := rfl

lemma curveNormalLinear_bijective {v a : Fin 3 → ℝ}
    (hv : v ≠ 0) (ha : ∀ r : ℝ, r • v ≠ a) :
    Function.Bijective (curveNormalLinear v a) := by
  have hli := curve_transverse_vector_independent hv ha
  have hw := curve_transverse_cross_ne_zero hv ha
  have hwv : (v ⨯₃ a) ⬝ᵥ v = 0 := by rw [dotProduct_comm]; exact dot_self_cross v a
  have hwa : (v ⨯₃ a) ⬝ᵥ a = 0 := by rw [dotProduct_comm]; exact dot_cross_self v a
  have hww : (v ⨯₃ a) ⬝ᵥ (v ⨯₃ a) ≠ 0 := (dotProduct_self_eq_zero).not.mpr hw
  have hz : ∀ z : Base × ℝ, curveNormalLinear v a z = 0 → z = 0 := by
    intro z h
    have hd := congrArg (fun w => (v ⨯₃ a) ⬝ᵥ w) h
    rw [curveNormalLinear_apply] at hd
    simp only [dotProduct_add,dotProduct_smul,hwv,hwa,smul_eq_mul,mul_zero,zero_add,dotProduct_zero] at hd
    have hz1 : z.1 1 = 0 := (mul_eq_zero.mp hd).resolve_right hww
    have hsum : z.2 • v+z.1 0 • a = 0 := by
      simpa only [curveNormalLinear_apply,hz1,zero_smul,add_zero] using h
    obtain ⟨hz2,hz0⟩ := (LinearIndependent.pair_iff.mp hli) z.2 (z.1 0) hsum
    apply Prod.ext
    · ext i
      fin_cases i
      · exact hz0
      · exact hz1
    · exact hz2
  have hi : Function.Injective (curveNormalLinear v a) := by
    intro z w h
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub,h,sub_self]
  refine ⟨hi,?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (curveNormalLinear v a).toLinearMap) _).mp hi
  simp [Base]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapAxisCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The kernel axis of an actual crosscap chart gives a smooth regular
source curve through the singular point, even though its image velocity vanishes. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma crosscapAxis_apply (t : ℝ) : crosscapAxis t = ![0,t] := by
  ext i
  fin_cases i <;> rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactAxisRectangle
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact axis segment in an open plane set has a uniform rectangular collar. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma open_interval_collar {a b : ℝ} (hab : a ≤ b) {U : Set ℝ}
    (hU : IsOpen U) (hI : Icc a b ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ Icc (a-δ) (b+δ) ⊆ U := by
  obtain ⟨δ,hδ,hsub⟩ := isCompact_Icc.exists_cthickening_subset_open hU hI
  refine ⟨δ,hδ,?_⟩
  intro x hx
  apply hsub
  by_cases hxa : x < a
  · apply mem_cthickening_of_dist_le x a δ (Icc a b) ⟨le_rfl,hab⟩
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxa.le)]
    linarith [hx.1]
  · by_cases hbx : b < x
    · apply mem_cthickening_of_dist_le x b δ (Icc a b) ⟨hab,le_rfl⟩
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hbx.le)]
      linarith [hx.2]
    · exact mem_cthickening_of_dist_le x x δ (Icc a b)
        ⟨le_of_not_gt hxa,le_of_not_gt hbx⟩ (by simpa using hδ.le)

theorem compact_axis_rectangle {a b : ℝ} (hab : a ≤ b) {U : Set Base}
    (hU : IsOpen U) (haxis : ∀ t ∈ Icc a b, (![0,t] : Base) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Icc (-δ) δ, ∀ t ∈ Icc (a-δ) (b+δ),
      (![x,t] : Base) ∈ U := by
  let T : ℝ × ℝ → Base := fun z => ![z.1,z.2]
  have hT : Continuous T := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  have hTU : ({0} : Set ℝ) ×ˢ Icc a b ⊆ T ⁻¹' U := by
    rintro ⟨x,t⟩ ⟨hx,ht⟩
    obtain rfl : x = 0 := hx
    exact haxis t ht
  obtain ⟨V,W,hV,hW,h0V,hIW,hVW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc (hU.preimage hT) hTU
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (by simp))
  obtain ⟨η,hη,hηW⟩ := open_interval_collar hab hW hIW
  let δ := min (r/2) η
  have hδ : 0 < δ := lt_min (half_pos hr) hη
  refine ⟨δ,hδ,?_⟩
  intro x hx t ht
  change (x,t) ∈ T ⁻¹' U
  apply hVW
  constructor
  · apply hrV
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
    have hδr : δ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
    constructor <;> linarith [hx.1,hx.2]
  · apply hηW
    have hδη : δ ≤ η := min_le_right _ _
    constructor <;> linarith [ht.1,ht.2]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveFrameInverse
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth inverse frames and the exact normal-coordinate immersion criterion. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma curveNormalLinear_invertible {v a : Fin 3 → ℝ}
    (hv : v ≠ 0) (ha : ∀ r : ℝ, r • v ≠ a) : (curveNormalLinear v a).IsInvertible := by
  have hb := curveNormalLinear_bijective hv ha
  exact ⟨ContinuousLinearEquiv.ofBijective (curveNormalLinear v a)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2),rfl⟩

lemma curveNormalLinear_inverse_velocity {v a : Fin 3 → ℝ}
    (hv : v ≠ 0) (ha : ∀ r : ℝ, r • v ≠ a) :
    (curveNormalLinear v a).inverse v = ((0 : Base),1) := by
  apply ((curveNormalLinear_invertible hv ha).inverse_apply_eq).mpr
  simp [curveNormalLinear_apply]

lemma normal_coordinates_injective_iff (L : Base →L[ℝ] (Base × ℝ))
    (hL : L (![1,0] : Base) = ((0:Base),1)) :
    Function.Injective L ↔ (L (![0,1] : Base)).1 ≠ 0 := by
  have hsplit : ∀ x : Base, L x = (x 0) • L (![1,0] : Base) + (x 1) • L (![0,1] : Base) := by
    intro x
    have hx : x = (x 0) • (![1,0] : Base) + (x 1) • (![0,1] : Base) := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [hx]
    rw [map_add,map_smul,map_smul]
  constructor
  · intro h hz
    have hEq : L (![0,1] : Base) = L (((L (![0,1] : Base)).2) • (![1,0] : Base)) := by
      rw [map_smul,hL]
      apply Prod.ext
      · simpa using hz
      · simp
    have h0 := congrFun (h hEq) 1
    norm_num at h0
  · intro hn x y hxy
    have hd : L (x-y) = 0 := by rw [map_sub,hxy,sub_self]
    rw [hsplit,hL] at hd
    have hfst := congrArg Prod.fst hd
    have h1 : (x-y) 1 = 0 := by
      have hm : (x-y) 1 • (L (![0,1] : Base)).1 = 0 := by simpa using hfst
      exact (smul_eq_zero.mp hm).resolve_right hn
    have hsnd := congrArg Prod.snd hd
    have h0 : (x-y) 0 = 0 := by simpa [h1] using hsnd
    apply sub_eq_zero.mp
    ext i
    fin_cases i
    · exact h0
    · exact h1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NormalDefectCoordinates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine two-component normal defect for the derivative of a surface map. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma coordinateDifferential_smooth {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (coordinateDifferential φ) :=
  contDiff_const.clm_comp (hφ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

lemma transverseDerivative_smooth {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (transverseDerivative φ) :=
  (coordinateDifferential_smooth hφ).clm_apply contDiff_const

lemma normalDefect_immersion_iff (φ : Base → ProjectionTarget 3) (a : Fin 3 → ℝ) (x : Base)
    (hu : transverseDerivative φ x ≠ 0)
    (ha : ∀ r : ℝ, r • transverseDerivative φ x ≠ a) :
    Function.Injective (fderiv ℝ φ x) ↔ normalDefect φ a x ≠ 0 := by
  let L := (curveNormalLinear (transverseDerivative φ x) a).inverse.comp (coordinateDifferential φ x)
  have hframe := curveNormalLinear_invertible hu ha
  have hI : Function.Injective (curveNormalLinear (transverseDerivative φ x) a).inverse := by
    intro v w hvw
    have hh := congrArg (curveNormalLinear (transverseDerivative φ x) a) hvw
    simpa only [hframe.self_apply_inverse] using hh
  have hL : L (![1,0] : Base) = ((0:Base),1) := curveNormalLinear_inverse_velocity hu ha
  have hequiv : Function.Injective (fderiv ℝ φ x) ↔ Function.Injective L := by
    constructor
    · intro h v w hEq
      apply h
      apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
      apply hI
      exact hEq
    · intro h v w hEq
      apply h
      change (curveNormalLinear (transverseDerivative φ x) a).inverse
        (EuclideanSpace.equiv (Fin 3) ℝ (fderiv ℝ φ x v)) = _
      rw [hEq]
      rfl
  exact hequiv.trans (normal_coordinates_injective_iff L hL)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PlaneComplexFrame
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real coordinate frame from a nonzero vector in the normal plane. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma planeComplexFrame_apply (w v : Base) :
    planeComplexFrame w v = ![w 0*v 0-w 1*v 1,w 1*v 0+w 0*v 1] := by
  ext i
  fin_cases i <;> simp [planeComplexFrame] <;> ring

lemma planeComplexFrame_smooth : ContDiff ℝ ∞ planeComplexFrame := by
  have hJ : ContDiff ℝ ∞ (fun w : Base => (![-w 1,w 0] : Base)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact (contDiff_apply ℝ ℝ 1).neg
    · exact contDiff_apply ℝ ℝ 0
  exact (contDiff_const.smulRight contDiff_id).add (contDiff_const.smulRight hJ)

lemma planeComplexFrame_injective {w : Base} (hw : w ≠ 0) :
    Function.Injective (planeComplexFrame w) := by
  have hs : (w 0)^2+(w 1)^2 ≠ 0 := by
    intro hz
    have h0 : w 0 = 0 := by nlinarith [sq_nonneg (w 0),sq_nonneg (w 1)]
    have h1 : w 1 = 0 := by nlinarith [sq_nonneg (w 0),sq_nonneg (w 1)]
    apply hw
    ext i
    fin_cases i
    · exact h0
    · exact h1
  intro u v he
  have h0 : w 0*u 0-w 1*u 1 = w 0*v 0-w 1*v 1 := by
    simpa only [planeComplexFrame_apply,Matrix.cons_val_zero] using congrFun he 0
  have h1 : w 1*u 0+w 0*u 1 = w 1*v 0+w 0*v 1 := by
    simpa only [planeComplexFrame_apply,Matrix.cons_val_one,Matrix.cons_val_zero] using congrFun he 1
  have hd0 : ((w 0)^2+(w 1)^2)*(u 0-v 0) = 0 := by
    linear_combination w 0*h0+w 1*h1
  have hd1 : ((w 0)^2+(w 1)^2)*(u 1-v 1) = 0 := by
    linear_combination w 0*h1-w 1*h0
  ext i
  fin_cases i
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hd0).resolve_left hs)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hd1).resolve_left hs)

lemma planeComplexFrame_bijective {w : Base} (hw : w ≠ 0) :
    Function.Bijective (planeComplexFrame w) := by
  have hi := planeComplexFrame_injective hw
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (planeComplexFrame w).toLinearMap) rfl).mp hi⟩

lemma planeComplexFrame_invertible {w : Base} (hw : w ≠ 0) :
    (planeComplexFrame w).IsInvertible := by
  have hb := planeComplexFrame_bijective hw
  exact ⟨ContinuousLinearEquiv.ofBijective (planeComplexFrame w)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2),rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalDefectDomain
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal-defect coordinates exist on a genuine open neighborhood
of the entire compact crosscap strip axis. -/
noncomputable section
open Set Filter Matrix Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma normalFrameDomain_nonzero {φ : Base → ProjectionTarget 3} {a : Fin 3 → ℝ}
    {x : Base} (hx : x ∈ normalFrameDomain φ a) : transverseDerivative φ x ≠ 0 := by
  intro hz
  apply hx
  rw [hz]
  simp

lemma normalFrameDomain_transverse {φ : Base → ProjectionTarget 3} {a : Fin 3 → ℝ}
    {x : Base} (hx : x ∈ normalFrameDomain φ a) :
    ∀ r : ℝ, r • transverseDerivative φ x ≠ a := by
  exact (LinearIndependent.pair_iff' (normalFrameDomain_nonzero hx)).mp
    (crossProduct_ne_zero_iff_linearIndependent.mp hx)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_AxisNormalizedDefect
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal coordinates adapted to the two simple zeros on the axis. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma injective_second_column_nonzero (L : Base →L[ℝ] Base)
    (hL : Function.Surjective L) (haxis : (L (![0,1] : Base)) 1 = 0) :
    (L (![1,0] : Base)) 1 ≠ 0 := by
  intro hz
  obtain ⟨v,hv⟩ := hL (![0,1] : Base)
  have hsplit : v = v 0 • (![1,0] : Base)+v 1 • (![0,1] : Base) := by
    ext i
    fin_cases i <;> simp
  have he := congrFun hv 1
  rw [hsplit,map_add,map_smul,map_smul] at he
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hz,haxis,mul_zero,add_zero,
    Matrix.cons_val_one,Matrix.cons_val_zero] at he
  norm_num at he

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_AxisDefectJet
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized endpoint jets retain nonzero transverse normal components. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma normalized_axis_derivative {G : Base → Base} {p q t : ℝ}
    (hG : ContDiffAt ℝ ∞ G (crosscapAxis t)) {W : Set ℝ} (hW : IsOpen W) (ht : t ∈ W)
    (haxis : ∀ s ∈ W, G (crosscapAxis s) = ![(s-p)*(s-q),0]) :
    fderiv ℝ G (crosscapAxis t) (![0,1] : Base) = ![(t-p)+(t-q),0] := by
  have he : G ∘ crosscapAxis =ᶠ[𝓝 t] fun s => (![(s-p)*(s-q),0] : Base) := by
    filter_upwards [hW.mem_nhds ht] with s hs
    exact haxis s hs
  have hd := (hG.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    crosscapAxis.hasFDerivAt.hasDerivAt
  have hp : HasDerivAt (fun s : ℝ => (![(s-p)*(s-q),0] : Base))
      (![(t-p)+(t-q),0] : Base) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert ((hasDerivAt_id t).sub_const p).mul ((hasDerivAt_id t).sub_const q) using 1 <;> first | (with_reducible_and_instances rfl) | (simp [add_comm])
      rfl
    · exact hasDerivAt_const t 0
  have hj := he.deriv_eq.trans hp.deriv
  exact (by simpa only [crosscapAxis_apply] using hd.deriv.symm.trans hj)

lemma normalized_axis_transverse_nonzero {G : Base → Base} {p q t : ℝ}
    (hG : ContDiffAt ℝ ∞ G (crosscapAxis t)) {W : Set ℝ} (hW : IsOpen W) (ht : t ∈ W)
    (haxis : ∀ s ∈ W, G (crosscapAxis s) = ![(s-p)*(s-q),0])
    (hD : Function.Bijective (fderiv ℝ G (crosscapAxis t))) :
    (fderiv ℝ G (crosscapAxis t) (![1,0] : Base)) 1 ≠ 0 := by
  apply injective_second_column_nonzero _ hD.2
  rw [normalized_axis_derivative hG hW ht haxis]
  rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_NormalizedLinearModel
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual first-order transverse model in normalized coordinates. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma normalizedAxisPolynomial_smooth (p q : ℝ) :
    ContDiff ℝ ∞ (normalizedAxisPolynomial p q) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [normalizedAxisPolynomial] <;> fun_prop

lemma normalTransverse_smooth {G : Base → Base} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (normalTransverse G) :=
  ((hG.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp crosscapAxis.contDiff).clm_apply contDiff_const

lemma normalizedLinearModel_smooth {G : Base → Base} (hG : ContDiff ℝ ∞ G) (p q : ℝ) :
    ContDiff ℝ ∞ (normalizedLinearModel G p q) :=
  (normalizedAxisPolynomial_smooth p q).add ((contDiff_apply ℝ ℝ 0).smul
    ((normalTransverse_smooth hG).comp (contDiff_apply ℝ ℝ 1)))

lemma normalizedLinearModel_axis (G : Base → Base) (p q t : ℝ) :
    normalizedLinearModel G p q (crosscapAxis t) = ![(t-p)*(t-q),0] := by
  simp [normalizedLinearModel,normalizedAxisPolynomial,crosscapAxis_apply]

lemma normalizedAxisPolynomial_hasFDerivAt (p q : ℝ) (x : Base) :
    HasFDerivAt (normalizedAxisPolynomial p q)
      ((ContinuousLinearMap.proj 1 : Base →L[ℝ] ℝ).smulRight (![(x 1-p)+(x 1-q),0] : Base)) x := by
  have h := (((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x).sub_const p).mul
    ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x).sub_const q)).smul_const
      (![1,0] : Base)
  have hf : normalizedAxisPolynomial p q =
      fun y => (((fun x : Base => x 1 - p) * fun x : Base => x 1 - q) y) • (![1,0] : Base) := by
    funext y
    ext i
    fin_cases i <;> simp [normalizedAxisPolynomial]
  rw [hf]
  refine h.congr_fderiv ?_
  ext v i
  fin_cases i <;> simp
  ring

lemma normalizedLinearModel_fderiv_axis {G : Base → Base} (hG : ContDiff ℝ ∞ G)
    (p q t : ℝ) :
    fderiv ℝ (normalizedLinearModel G p q) (crosscapAxis t) =
      (ContinuousLinearMap.proj 1).smulRight (![(t-p)+(t-q),0] : Base)+
      (ContinuousLinearMap.proj 0).smulRight (normalTransverse G t) := by
  have hA := normalizedAxisPolynomial_hasFDerivAt p q (crosscapAxis t)
  have ha := ((normalTransverse_smooth hG).differentiable (by simp) t).hasFDerivAt.comp
    (crosscapAxis t) (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (crosscapAxis t))
  have hh := hA.add ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (crosscapAxis t)).smul ha)
  have he := hh.fderiv
  change fderiv ℝ (normalizedLinearModel G p q) (crosscapAxis t) = _ at he
  simpa [crosscapAxis_apply] using he

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactFixedJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact parameter family sharing a fixed jet has one common
neighborhood of quantitative injectivity. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma compact_fixed_value_neighborhood {E F : Type*} [TopologicalSpace E]
    [PseudoMetricSpace F] {K : Set ℝ} (hK : IsCompact K)
    {f : ℝ × E → F} (hf : Continuous f) (p : E) (v : F)
    (hfix : ∀ t ∈ K, f (t,p) = v) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧ ∀ t ∈ K, ∀ x ∈ U, dist (f (t,x)) v < ε := by
  let O : Set (ℝ × E) := f ⁻¹' ball v ε
  have hO : IsOpen O := isOpen_ball.preimage hf
  have hsub : K ×ˢ {p} ⊆ O := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    have he : x = p := hx
    subst x
    change f (t,p) ∈ ball v ε
    simpa [hfix t ht] using hε
  obtain ⟨V,U,hV,hU,hKV,hpU,hVU⟩ := generalized_tube_lemma hK isCompact_singleton hO hsub
  refine ⟨U,hU,hpU (by simp),?_⟩
  intro t ht x hx
  exact hVU ⟨hKV ht,hx⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PlaneDerivativeInjectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative local injectivity for a two-dimensional map. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma near_plane_equiv_derivative_injOn (L : Base ≃L[ℝ] Base)
    {g : Base → Base} {S : Set Base} (hg : ∀ x ∈ S, DifferentiableAt ℝ g x)
    (hS : Convex ℝ S) {c : ℝ}
    (hsmall : ‖L.symm.toContinuousLinearMap‖*c < 1)
    (hbound : ∀ x ∈ S, ‖fderiv ℝ g x-L.toContinuousLinearMap‖ ≤ c) :
    S.InjOn g := by
  intro x hx y hy heq
  have hd : ∀ z ∈ S, DifferentiableAt ℝ (fun z => g z-L z) z :=
    fun z hz => (hg z hz).sub L.differentiableAt
  have hb : ∀ z ∈ S, ‖fderiv ℝ (fun z => g z-L z) z‖ ≤ c := by
    intro z hz
    rw [fderiv_fun_sub (hg z hz) L.differentiableAt,L.fderiv]
    exact hbound z hz
  have herr := hS.norm_image_sub_le_of_norm_fderiv_le hd hb hx hy
  have hL : ‖L (y-x)‖ ≤ c*‖y-x‖ := by
    have he : (g y-L y)-(g x-L x) = -L (y-x) := by
      rw [←heq,map_sub]
      abel
    rw [he,norm_neg] at herr
    exact herr
  have hback : ‖y-x‖ ≤ ‖L.symm.toContinuousLinearMap‖*‖L (y-x)‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe,L.symm_apply_apply] using
      L.symm.toContinuousLinearMap.le_opNorm (L (y-x))
  have hn : ‖y-x‖ = 0 := by
    have hh := hback.trans (mul_le_mul_of_nonneg_left hL (norm_nonneg _))
    nlinarith [norm_nonneg (y-x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactPlaneJet
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform isolation for a compact family of nondegenerate planar zeros.
The differential may vary with the homotopy parameter. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem compact_plane_jet_injectivity {K : Set ℝ} (hK : IsCompact K)
    (F : ℝ → Base → Base) (hF : ∀ t ∈ K, ContDiff ℝ ∞ (F t))
    (hD : Continuous (fun z : ℝ × Base => fderiv ℝ (F z.1) z.2)) (p : Base)
    (hI : ∀ t ∈ K, Function.Bijective (fderiv ℝ (F t) p)) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ K, (ball p r).InjOn (F t) := by
  have hJ : ContinuousOn (fun t => (fderiv ℝ (F t) p).inverse) K := by
    intro t ht
    let L := ContinuousLinearEquiv.ofBijective (fderiv ℝ (F t) p)
      (LinearMap.ker_eq_bot.mpr (hI t ht).1) (LinearMap.range_eq_top.mpr (hI t ht).2)
    have hi : (fderiv ℝ (F t) p).IsInvertible := ⟨L,rfl⟩
    have hinv : ContDiffAt ℝ 0 ContinuousLinearMap.inverse (fderiv ℝ (F t) p) :=
      hi.contDiffAt_map_inverse
    have hP : Continuous (fun s : ℝ => fderiv ℝ (F s) p) :=
      hD.comp (continuous_id.prodMk continuous_const)
    have hJt : ContinuousAt (fun s : ℝ => (fderiv ℝ (F s) p).inverse) t :=
      ContinuousAt.comp (g := ContinuousLinearMap.inverse)
        (f := fun s : ℝ => fderiv ℝ (F s) p) hinv.continuousAt hP.continuousAt
    exact hJt.continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hJ
  let c : ℝ := (2*(|C|+1))⁻¹
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hdiff : Continuous (fun z : ℝ × Base =>
      fderiv ℝ (F z.1) z.2-fderiv ℝ (F z.1) p) :=
    hD.sub (hD.comp (continuous_fst.prodMk continuous_const))
  obtain ⟨U,hU,hpU,hnear⟩ := compact_fixed_value_neighborhood hK hdiff p
    (0 : Base →L[ℝ] Base) (fun _ _ => sub_self _) hc
  obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hU p hpU
  refine ⟨r,hr,?_⟩
  intro t ht
  let L := ContinuousLinearEquiv.ofBijective (fderiv ℝ (F t) p)
    (LinearMap.ker_eq_bot.mpr (hI t ht).1) (LinearMap.range_eq_top.mpr (hI t ht).2)
  have hLI : (fderiv ℝ (F t) p).inverse = L.symm.toContinuousLinearMap := by
    change (L.toContinuousLinearMap).inverse = _
    exact ContinuousLinearMap.inverse_equiv L
  have hLn : ‖L.symm.toContinuousLinearMap‖ ≤ |C| := by
    rw [←hLI]
    exact (hC t ht).trans (le_abs_self C)
  apply near_plane_equiv_derivative_injOn L
    (fun x _ => (hF t ht).differentiable (by simp) x) (convex_ball p r) (c := c)
  · calc
      _ ≤ |C| * c := mul_le_mul_of_nonneg_right hLn hc.le
      _ < 1 := by
        dsimp [c]
        rw [←div_eq_mul_inv]
        apply (div_lt_iff₀ (by positivity)).mpr
        linarith [abs_nonneg C]
  · intro x hx
    have hh : ‖fderiv ℝ (F t) x-fderiv ℝ (F t) p‖ < c := by
      simpa only [dist_zero_right] using hnear t ht x (hrU hx)
    exact hh.le

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactPlaneZero
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform zero isolation along the normalized connecting axis. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma compact_nonzero_locus_open {K : Set ℝ} (hK : IsCompact K)
    {F : ℝ → Base → Base} (hF : Continuous (fun z : ℝ × Base => F z.1 z.2)) :
    IsOpen {x | ∀ t ∈ K, F t x ≠ 0} := by
  let O := {z : ℝ × Base | F z.1 z.2 ≠ 0}
  have hO : IsOpen O := isOpen_ne.preimage hF
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hsub : K ×ˢ {x} ⊆ O := by
    rintro ⟨t,y⟩ ⟨ht,hy⟩
    have he : y = x := hy
    subst y
    exact hx t ht
  obtain ⟨V,U,_hV,hU,hKV,hxU,hVU⟩ := generalized_tube_lemma hK isCompact_singleton hO hsub
  apply Filter.mem_of_superset (hU.mem_nhds (hxU (by simp)))
  intro y hy t ht
  exact hVU (show (t,y) ∈ V ×ˢ U from ⟨hKV ht,hy⟩)

theorem compact_plane_zero_isolation {K : Set ℝ} (hK : IsCompact K)
    (F : ℝ → Base → Base) (hF : ∀ t ∈ K, ContDiff ℝ ∞ (F t))
    (hD : Continuous (fun z : ℝ × Base => fderiv ℝ (F z.1) z.2)) (p : Base)
    (hI : ∀ t ∈ K, Function.Bijective (fderiv ℝ (F t) p))
    (hz : ∀ t ∈ K, F t p = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ K, ∀ x ∈ ball p r, F t x = 0 ↔ x = p := by
  obtain ⟨r,hr,hri⟩ := compact_plane_jet_injectivity hK F hF hD p hI
  refine ⟨r,hr,?_⟩
  intro t ht x hx
  constructor
  · intro he
    exact hri t ht hx (mem_ball_self hr) (he.trans (hz t ht).symm)
  · rintro rfl
    exact hz t ht

theorem compact_two_zero_rectangle {K : Set ℝ} (hK : IsCompact K)
    (F : ℝ → Base → Base) (hF : ∀ t ∈ K, ContDiff ℝ ∞ (F t))
    (hFc : Continuous (fun z : ℝ × Base => F z.1 z.2))
    (hD : Continuous (fun z : ℝ × Base => fderiv ℝ (F z.1) z.2))
    {p q : ℝ} (hpq : p < q)
    (haxis : ∀ t ∈ K, ∀ s ∈ Icc p q, F t (crosscapAxis s) = ![(s-p)*(s-q),0])
    (hIp : ∀ t ∈ K, Function.Bijective (fderiv ℝ (F t) (crosscapAxis p)))
    (hIq : ∀ t ∈ K, Function.Bijective (fderiv ℝ (F t) (crosscapAxis q))) :
    ∃ (r : ℝ) (O : Set Base), 0 < r ∧ IsOpen O ∧
      (∀ x ∈ Icc (-r) r, ∀ s ∈ Icc (p-r) (q+r), (![x,s] : Base) ∈ O) ∧
      ∀ t ∈ K, ∀ x ∈ O, F t x = 0 ↔ x = crosscapAxis p ∨ x = crosscapAxis q := by
  have hzp : ∀ t ∈ K, F t (crosscapAxis p) = 0 := by
    intro t ht
    rw [haxis t ht p (left_mem_Icc.mpr hpq.le)]
    ext i
    fin_cases i <;> simp
  have hzq : ∀ t ∈ K, F t (crosscapAxis q) = 0 := by
    intro t ht
    rw [haxis t ht q (right_mem_Icc.mpr hpq.le)]
    ext i
    fin_cases i <;> simp
  obtain ⟨rp,hrp,hp⟩ := compact_plane_zero_isolation hK F hF hD _ hIp hzp
  obtain ⟨rq,hrq,hq⟩ := compact_plane_zero_isolation hK F hF hD _ hIq hzq
  let U : Set Base := {x | ∀ t ∈ K, F t x ≠ 0}
  let O := (ball (crosscapAxis p) rp ∪ ball (crosscapAxis q) rq) ∪ U
  have hO : IsOpen O := (isOpen_ball.union isOpen_ball).union (compact_nonzero_locus_open hK hFc)
  have hAO : ∀ s ∈ Icc p q, crosscapAxis s ∈ O := by
    intro s hs
    by_cases hsp : s = p
    · subst s
      exact Or.inl (Or.inl (mem_ball_self hrp))
    by_cases hsq : s = q
    · subst s
      exact Or.inl (Or.inr (mem_ball_self hrq))
    apply Or.inr
    intro t ht he
    have he0 := congrFun he 0
    rw [haxis t ht s hs] at he0
    have hmul : (s-p)*(s-q) = 0 := he0
    rcases mul_eq_zero.mp hmul with hh | hh
    · exact hsp (sub_eq_zero.mp hh)
    · exact hsq (sub_eq_zero.mp hh)
  obtain ⟨r,hr,hrect⟩ := compact_axis_rectangle hpq.le hO
    (by simpa only [crosscapAxis_apply] using hAO)
  refine ⟨r,O,hr,hO,hrect,?_⟩
  intro t ht x hx
  constructor
  · intro hz
    rcases hx with (hxp | hxq) | hxU
    · exact Or.inl ((hp t ht x hxp).mp hz)
    · exact Or.inr ((hq t ht x hxq).mp hz)
    · exact False.elim (hxU t ht hz)
  · rintro (rfl | rfl)
    · exact hzp t ht
    · exact hzq t ht

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_NormalLinearizationHomotopy
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearizing only the transverse coordinate preserves exactly the two zeros
on a common thin rectangle throughout the homotopy. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma plane_map_columns (L : Base →L[ℝ] Base) :
    L = (ContinuousLinearMap.proj 0).smulRight (L (![1,0] : Base))+
      (ContinuousLinearMap.proj 1).smulRight (L (![0,1] : Base)) := by
  ext v : 1
  have hv : v = v 0 • (![1,0] : Base)+v 1 • (![0,1] : Base) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  rw [map_add,map_smul,map_smul]
  rfl

lemma normalizedLinearModel_fderiv_eq {G : Base → Base} (hG : ContDiff ℝ ∞ G)
    {p q t : ℝ} {W : Set ℝ} (hW : IsOpen W) (ht : t ∈ W)
    (haxis : ∀ s ∈ W, G (crosscapAxis s) = ![(s-p)*(s-q),0]) :
    fderiv ℝ (normalizedLinearModel G p q) (crosscapAxis t) = fderiv ℝ G (crosscapAxis t) := by
  rw [normalizedLinearModel_fderiv_axis hG]
  rw [←normalized_axis_derivative hG.contDiffAt hW ht haxis]
  change (ContinuousLinearMap.proj 1 : Base →L[ℝ] ℝ).smulRight (fderiv ℝ G (crosscapAxis t) (![0,1] : Base))+
    (ContinuousLinearMap.proj 0 : Base →L[ℝ] ℝ).smulRight (fderiv ℝ G (crosscapAxis t) (![1,0] : Base)) = _
  rw [add_comm]
  exact (plane_map_columns _).symm

lemma linearDefectHomotopy_smooth {G : Base → Base} (hG : ContDiff ℝ ∞ G) (p q : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × Base => linearDefectHomotopy G p q z.1 z.2) :=
  ((contDiff_const.sub contDiff_fst).smul (hG.comp contDiff_snd)).add
    (contDiff_fst.smul ((normalizedLinearModel_smooth hG p q).comp contDiff_snd))

lemma linearDefectHomotopy_fderiv {G : Base → Base} (hG : ContDiff ℝ ∞ G) (p q s : ℝ) (x : Base) :
    fderiv ℝ (linearDefectHomotopy G p q s) x =
      (1-s) • fderiv ℝ G x+s • fderiv ℝ (normalizedLinearModel G p q) x := by
  exact (((hG.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasFDerivAt.const_smul (1-s)).add
    (((normalizedLinearModel_smooth hG p q).differentiable (by simp) x).hasFDerivAt.const_smul s)).fderiv

lemma linearDefectHomotopy_axis {G : Base → Base} {p q t : ℝ}
    (he : G (crosscapAxis t) = ![(t-p)*(t-q),0]) (s : ℝ) :
    linearDefectHomotopy G p q s (crosscapAxis t) = ![(t-p)*(t-q),0] := by
  rw [linearDefectHomotopy,he,normalizedLinearModel_axis,←add_smul]
  simp

lemma linearDefectHomotopy_jet {G : Base → Base} (hG : ContDiff ℝ ∞ G)
    {p q t : ℝ} {W : Set ℝ} (hW : IsOpen W) (ht : t ∈ W)
    (haxis : ∀ s ∈ W, G (crosscapAxis s) = ![(s-p)*(s-q),0]) (s : ℝ) :
    fderiv ℝ (linearDefectHomotopy G p q s) (crosscapAxis t) = fderiv ℝ G (crosscapAxis t) := by
  rw [linearDefectHomotopy_fderiv hG,normalizedLinearModel_fderiv_eq hG hW ht haxis,
    ←add_smul]
  simp

theorem linearDefectHomotopy_two_zeros {G : Base → Base} (hG : ContDiff ℝ ∞ G)
    {p q : ℝ} (hpq : p < q) {W : Set ℝ} (hW : IsOpen W) (hKW : Icc p q ⊆ W)
    (haxis : ∀ t ∈ W, G (crosscapAxis t) = ![(t-p)*(t-q),0])
    (hIp : Function.Bijective (fderiv ℝ G (crosscapAxis p)))
    (hIq : Function.Bijective (fderiv ℝ G (crosscapAxis q))) :
    ∃ (r : ℝ) (O : Set Base), 0 < r ∧ IsOpen O ∧
      (∀ x ∈ Icc (-r) r, ∀ t ∈ Icc (p-r) (q+r), (![x,t] : Base) ∈ O) ∧
      ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ O, linearDefectHomotopy G p q s x = 0 ↔
        x = crosscapAxis p ∨ x = crosscapAxis q := by
  have hsmooth := linearDefectHomotopy_smooth hG p q
  have hFs : ∀ s ∈ Icc (0:ℝ) 1, ContDiff ℝ ∞ (linearDefectHomotopy G p q s) := by
    intro s _
    exact hsmooth.comp (contDiff_const.prodMk contDiff_id)
  have hD : Continuous (fun z : ℝ × Base => fderiv ℝ (linearDefectHomotopy G p q z.1) z.2) := by
    simp_rw [linearDefectHomotopy_fderiv hG]
    exact ((continuous_const.sub continuous_fst).smul
      ((hG.continuous_fderiv (by simp)).comp continuous_snd)).add
      (continuous_fst.smul (((normalizedLinearModel_smooth hG p q).continuous_fderiv (by simp)).comp continuous_snd))
  apply compact_two_zero_rectangle isCompact_Icc _ hFs hsmooth.continuous hD hpq
  · intro s _ t ht
    exact linearDefectHomotopy_axis (haxis t (hKW ht)) s
  · intro s _
    rw [linearDefectHomotopy_jet hG hW (hKW (left_mem_Icc.mpr hpq.le)) haxis]
    exact hIp
  · intro s _
    rw [linearDefectHomotopy_jet hG hW (hKW (right_mem_Icc.mpr hpq.le)) haxis]
    exact hIq

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TransverseJetConvexity
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common vertical column and matching transverse signs preserve rank
under convex interpolation of the endpoint jets. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma triangularPlaneJet_bijective {a b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0) :
    Function.Bijective (triangularPlaneJet a b c) := by
  have hi : Function.Injective (triangularPlaneJet a b c) := by
    intro u v he
    have h1 : u 0 = v 0 := by
      have hh := congrFun he 1
      simp [triangularPlaneJet] at hh
      exact hh.resolve_right hb
    have h0 := congrFun he 0
    simp only [triangularPlaneJet,add_apply,ContinuousLinearMap.smulRight_apply,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul,ContinuousLinearMap.proj_apply,
      Matrix.cons_val_zero] at h0
    rw [h1] at h0
    have h2 : u 1 = v 1 := mul_right_cancel₀ hc (add_left_cancel h0)
    ext i
    fin_cases i
    · exact h1
    · exact h2
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (triangularPlaneJet a b c).toLinearMap) rfl).mp hi⟩

lemma plane_jet_bijective_of_columns (L : Base →L[ℝ] Base) {c : ℝ}
    (hc : c ≠ 0) (he : L (![0,1] : Base) = ![c,0])
    (hb : (L (![1,0] : Base)) 1 ≠ 0) : Function.Bijective L := by
  have hL : L = triangularPlaneJet (L ![1,0] 0) (L ![1,0] 1) c := by
    rw [plane_map_columns L,he]
    ext v i
    fin_cases i <;> simp [triangularPlaneJet]
  rw [hL]
  exact triangularPlaneJet_bijective hb hc

lemma convex_same_sign_ne_zero {a b s : ℝ} (hab : 0 < a*b) (hs : s ∈ Icc (0:ℝ) 1) :
    (1-s)*a+s*b ≠ 0 := by
  rcases mul_pos_iff.mp hab with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have hpos : 0 < (1-s)*a+s*b := by
      rcases lt_or_eq_of_le hs.2 with hlt | rfl
      · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) ha) (mul_nonneg hs.1 hb.le)
      · simpa using hb
    exact hpos.ne'
  · have hneg : (1-s)*a+s*b < 0 := by
      rcases lt_or_eq_of_le hs.2 with hlt | rfl
      · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg (by linarith) ha)
          (mul_nonpos_of_nonneg_of_nonpos hs.1 hb.le)
      · simpa using hb
    exact hneg.ne

lemma convex_plane_jets_bijective (L J : Base →L[ℝ] Base) {c s : ℝ}
    (hc : c ≠ 0) (hL : L (![0,1] : Base) = ![c,0])
    (hJ : J (![0,1] : Base) = ![c,0])
    (hprod : 0 < (L (![1,0] : Base) 1)*(J (![1,0] : Base) 1))
    (hs : s ∈ Icc (0:ℝ) 1) : Function.Bijective ((1-s) • L+s • J) := by
  apply plane_jet_bijective_of_columns _ hc
  · simp only [add_apply,smul_apply,hL,hJ]
    rw [←add_smul]
    simp
  · change (1-s)*(L (![1,0] : Base) 1)+s*(J (![1,0] : Base) 1) ≠ 0
    exact convex_same_sign_ne_zero hprod hs

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_EndpointSignModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The simplest affine coefficient with the two prescribed endpoint signs. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma nonzeroSign_mul_pos {r : ℝ} (hr : r ≠ 0) : 0 < r*nonzeroSign r := by
  by_cases hp : 0 < r
  · simp [nonzeroSign,hp]
  · have hn : r < 0 := lt_of_le_of_ne (le_of_not_gt hp) hr
    simp [nonzeroSign,hp,hn]

lemma endpointSignModel_left {p q a b : ℝ} (hpq : p ≠ q) :
    endpointSignModel p q a b p = nonzeroSign a := by
  simp [endpointSignModel,sub_ne_zero.mpr hpq.symm]

lemma endpointSignModel_right {p q a b : ℝ} (hpq : p ≠ q) :
    endpointSignModel p q a b q = nonzeroSign b := by
  simp [endpointSignModel,sub_ne_zero.mpr hpq.symm]

lemma endpointSignModel_smooth (p q a b : ℝ) :
    ContDiff ℝ ∞ (endpointSignModel p q a b) := by
  unfold endpointSignModel
  fun_prop

lemma endpointSignModel_left_mul_pos {p q a b : ℝ} (hpq : p ≠ q) (ha : a ≠ 0) :
    0 < a*endpointSignModel p q a b p := by
  rw [endpointSignModel_left hpq]
  exact nonzeroSign_mul_pos ha

lemma endpointSignModel_right_mul_pos {p q a b : ℝ} (hpq : p ≠ q) (hb : b ≠ 0) :
    0 < b*endpointSignModel p q a b q := by
  rw [endpointSignModel_right hpq]
  exact nonzeroSign_mul_pos hb

lemma endpointSignModel_same {p q a b : ℝ} (hpq : p ≠ q)
    (hsame : nonzeroSign a = nonzeroSign b) (t : ℝ) :
    endpointSignModel p q a b t = nonzeroSign a := by
  unfold endpointSignModel
  rw [←hsame]
  field_simp [sub_ne_zero.mpr hpq.symm]
  ring

lemma endpointSignModel_opposite {p q a b : ℝ} (hpq : p ≠ q)
    (hopp : nonzeroSign b = -nonzeroSign a) (t : ℝ) :
    endpointSignModel p q a b t = ((p+q-2*t)/(q-p))*nonzeroSign a := by
  unfold endpointSignModel
  rw [hopp]
  field_simp [sub_ne_zero.mpr hpq.symm]
  ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_DiagonalDefectModel
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal transverse models retain the two prescribed axial zeros. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma diagonalDefectModel_smooth {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (p q : ℝ) :
    ContDiff ℝ ∞ (diagonalDefectModel b p q) := by
  unfold diagonalDefectModel
  exact (normalizedAxisPolynomial_smooth p q).add
    (((contDiff_apply ℝ ℝ 0).mul (hb.comp (contDiff_apply ℝ ℝ 1))).smul contDiff_const)

lemma diagonalDefectModel_apply (b : ℝ → ℝ) (p q : ℝ) (x : Base) :
    diagonalDefectModel b p q x = ![(x 1-p)*(x 1-q),x 0*b (x 1)] := by
  ext i
  fin_cases i <;> simp [diagonalDefectModel,normalizedAxisPolynomial]

lemma diagonalDefectModel_axis (b : ℝ → ℝ) (p q t : ℝ) :
    diagonalDefectModel b p q (crosscapAxis t) = ![(t-p)*(t-q),0] := by
  simp [diagonalDefectModel_apply,crosscapAxis_apply]

lemma diagonalDefectModel_fderiv_axis {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (p q t : ℝ) :
    fderiv ℝ (diagonalDefectModel b p q) (crosscapAxis t) =
      triangularPlaneJet 0 (b t) ((t-p)+(t-q)) := by
  have hb' := (hb.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t).hasFDerivAt.comp
    (crosscapAxis t) (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) (crosscapAxis t))
  have hh := (normalizedAxisPolynomial_hasFDerivAt p q (crosscapAxis t)).add
    (((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) (crosscapAxis t)).mul hb').smul_const
      (![0,1] : Base))
  change HasFDerivAt (diagonalDefectModel b p q) _ _ at hh
  rw [hh.fderiv]
  ext v i
  fin_cases i <;> simp [triangularPlaneJet,crosscapAxis_apply]
  ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PlaneDefectInterpolation
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex interpolation with matching transverse signs retains the simple
axial zeros on one common rectangle. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma planeDefectInterpolation_smooth {F G : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun z : ℝ × Base => planeDefectInterpolation F G z.1 z.2) :=
  ((contDiff_const.sub contDiff_fst).smul (hF.comp contDiff_snd)).add
    (contDiff_fst.smul (hG.comp contDiff_snd))

lemma planeDefectInterpolation_fderiv {F G : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (s : ℝ) (x : Base) :
    fderiv ℝ (planeDefectInterpolation F G s) x =
      (1-s) • fderiv ℝ F x+s • fderiv ℝ G x :=
  (((hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasFDerivAt.const_smul (1-s)).add
    ((hG.differentiable (by simp) x).hasFDerivAt.const_smul s)).fderiv

lemma planeDefectInterpolation_axis {F G : Base → Base} {p q t : ℝ}
    (hF : F (crosscapAxis t) = ![(t-p)*(t-q),0])
    (hG : G (crosscapAxis t) = ![(t-p)*(t-q),0]) (s : ℝ) :
    planeDefectInterpolation F G s (crosscapAxis t) = ![(t-p)*(t-q),0] := by
  rw [planeDefectInterpolation,hF,hG,←add_smul]
  simp

theorem planeDefectInterpolation_two_zeros {F G : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    {p q : ℝ} (hpq : p < q) {W : Set ℝ} (hW : IsOpen W) (hKW : Icc p q ⊆ W)
    (hFa : ∀ t ∈ W, F (crosscapAxis t) = ![(t-p)*(t-q),0])
    (hGa : ∀ t ∈ W, G (crosscapAxis t) = ![(t-p)*(t-q),0])
    (hsp : 0 < (fderiv ℝ F (crosscapAxis p) ![1,0] 1)*
      (fderiv ℝ G (crosscapAxis p) ![1,0] 1))
    (hsq : 0 < (fderiv ℝ F (crosscapAxis q) ![1,0] 1)*
      (fderiv ℝ G (crosscapAxis q) ![1,0] 1)) :
    ∃ (r : ℝ) (O : Set Base), 0 < r ∧ IsOpen O ∧
      (∀ x ∈ Icc (-r) r, ∀ t ∈ Icc (p-r) (q+r), (![x,t] : Base) ∈ O) ∧
      ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ O, planeDefectInterpolation F G s x = 0 ↔
        x = crosscapAxis p ∨ x = crosscapAxis q := by
  have hsm := planeDefectInterpolation_smooth hF hG
  have hFs : ∀ s ∈ Icc (0:ℝ) 1, ContDiff ℝ ∞ (planeDefectInterpolation F G s) := by
    intro s _
    exact hsm.comp (contDiff_const.prodMk contDiff_id)
  have hD : Continuous (fun z : ℝ × Base => fderiv ℝ (planeDefectInterpolation F G z.1) z.2) := by
    simp_rw [planeDefectInterpolation_fderiv hF hG]
    exact ((continuous_const.sub continuous_fst).smul
      ((hF.continuous_fderiv (by simp)).comp continuous_snd)).add
      (continuous_fst.smul ((hG.continuous_fderiv (by simp)).comp continuous_snd))
  apply compact_two_zero_rectangle isCompact_Icc _ hFs hsm.continuous hD hpq
  · intro s _ t ht
    exact planeDefectInterpolation_axis (hFa t (hKW ht)) (hGa t (hKW ht)) s
  · intro s hs
    rw [planeDefectInterpolation_fderiv hF hG]
    apply convex_plane_jets_bijective _ _ (c := (p-p)+(p-q)) (by linarith)
      (normalized_axis_derivative hF.contDiffAt hW (hKW (left_mem_Icc.mpr hpq.le)) hFa)
      (normalized_axis_derivative hG.contDiffAt hW (hKW (left_mem_Icc.mpr hpq.le)) hGa) hsp hs
  · intro s hs
    rw [planeDefectInterpolation_fderiv hF hG]
    apply convex_plane_jets_bijective _ _ (c := (q-p)+(q-q)) (by linarith)
      (normalized_axis_derivative hF.contDiffAt hW (hKW (right_mem_Icc.mpr hpq.le)) hFa)
      (normalized_axis_derivative hG.contDiffAt hW (hKW (right_mem_Icc.mpr hpq.le)) hGa) hsq hs

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialRotationFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial rotation columns from a three-coordinate quaternion.
They fill a twice-winding planar frame by allowing its first column to move. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma polynomialRotationFrame_apply (a b c : ℝ) (v : Base) :
    polynomialRotationFrame a b c v =
      v 0 • rotationFirst a b c + v 1 • rotationSecond a b c := by
  rfl

lemma rotationFirst_sq (a b c : ℝ) :
    (rotationFirst a b c 0)^2+(rotationFirst a b c 1)^2+
      (rotationFirst a b c 2)^2 = (a^2+b^2+c^2)^2 := by
  dsimp [rotationFirst]
  ring
lemma rotationSecond_sq (a b c : ℝ) :
    (rotationSecond a b c 0)^2+(rotationSecond a b c 1)^2+
      (rotationSecond a b c 2)^2 = (a^2+b^2+c^2)^2 := by
  dsimp [rotationSecond]
  ring
lemma rotation_columns_orthogonal (a b c : ℝ) :
    rotationFirst a b c 0 * rotationSecond a b c 0+
      rotationFirst a b c 1 * rotationSecond a b c 1+
      rotationFirst a b c 2 * rotationSecond a b c 2 = 0 := by
  dsimp [rotationFirst,rotationSecond]
  ring

lemma polynomialRotationFrame_injective {a b c : ℝ} (hq : 0 < a^2+b^2+c^2) :
    Function.Injective (polynomialRotationFrame a b c) := by
  intro u v huv
  have he (i : Fin 3) :
      (u 0-v 0)*rotationFirst a b c i+(u 1-v 1)*rotationSecond a b c i = 0 := by
    have hi := congrFun huv i
    simp only [polynomialRotationFrame_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hi
    linear_combination hi
  have hd0 : (u 0-v 0)*(a^2+b^2+c^2)^2 = 0 := by
    rw [←rotationFirst_sq a b c]
    linear_combination (rotationFirst a b c 0)*he 0+
      (rotationFirst a b c 1)*he 1+(rotationFirst a b c 2)*he 2-
      (u 1-v 1)*rotation_columns_orthogonal a b c
  have hd1 : (u 1-v 1)*(a^2+b^2+c^2)^2 = 0 := by
    rw [←rotationSecond_sq a b c]
    linear_combination (rotationSecond a b c 0)*he 0+
      (rotationSecond a b c 1)*he 1+(rotationSecond a b c 2)*he 2-
      (u 0-v 0)*rotation_columns_orthogonal a b c
  have hn : (a^2+b^2+c^2)^2 ≠ 0 := (sq_pos_of_pos hq).ne'
  have h0 := sub_eq_zero.mp ((mul_eq_zero.mp hd0).resolve_right hn)
  have h1 := sub_eq_zero.mp ((mul_eq_zero.mp hd1).resolve_right hn)
  ext i
  fin_cases i
  · exact h0
  · exact h1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ShiftedRotationFrame
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rotation columns with an exterior constant shift. This allows the
twice-winding frame to have two separated simple zeros before filling. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma axisNormalFrame_injective {r y z : ℝ} (hr : r ≠ 0) (hn : y ≠ 0 ∨ z ≠ 0) :
    Function.Injective (axisNormalFrame r y z) := by
  intro u v he
  have h0 : u 0 = v 0 := by
    have hh := congrFun he 0
    simp [axisNormalFrame] at hh
    exact hh.resolve_right hr
  have h1 : u 1 = v 1 := by
    rcases hn with hn | hn
    · have hh := congrFun he 1
      simp [axisNormalFrame] at hh
      exact hh.resolve_right hn
    · have hh := congrFun he 2
      simp [axisNormalFrame] at hh
      exact hh.resolve_right hn
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma shiftedRotationFrame_zero_c (a b e : ℝ) :
    shiftedRotationFrame a b 0 e = axisNormalFrame (a^2+b^2) (a^2-b^2-e) (2*a*b) := by
  ext v i
  fin_cases i <;> simp [shiftedRotationFrame,axisNormalFrame,polynomialRotationFrame,
    rotationFirst,rotationSecond]
  all_goals ring

lemma shiftedRotationFrame_injective_exterior {a b e : ℝ} (hr : 1 < a^2+b^2)
    (he : e ∈ Icc (0:ℝ) 1) : Function.Injective (shiftedRotationFrame a b 0 e) := by
  rw [shiftedRotationFrame_zero_c]
  apply axisNormalFrame_injective (by linarith)
  by_contra hn
  push Not at hn
  have hab : a*b = 0 := by nlinarith [hn.2]
  rcases mul_eq_zero.mp hab with ha | hb
  · rw [ha] at hr hn
    simp only [zero_mul,mul_zero] at hr hn
    nlinarith [he.1,sq_nonneg b]
  · rw [hb] at hr hn
    simp only [mul_zero] at hr hn
    linarith [he.2]

lemma shiftedRotationFrame_injective {a b c e : ℝ} (hq : 0 < a^2+b^2+c^2)
    (hcase : e = 0 ∨ c = 0 ∧ 1 < a^2+b^2 ∧ e ∈ Icc (0:ℝ) 1) :
    Function.Injective (shiftedRotationFrame a b c e) := by
  rcases hcase with rfl | ⟨rfl,hr,he⟩
  · have hz : (ContinuousLinearMap.proj 1 : Base →L[ℝ] ℝ).smulRight
        (![0,(0:ℝ),0] : FrameTarget) = 0 := by
      ext v i
      fin_cases i <;> simp
    rw [shiftedRotationFrame,hz,sub_zero]
    exact polynomialRotationFrame_injective hq
  · exact shiftedRotationFrame_injective_exterior hr he

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalizeFrameColumn
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive normalization of the first column of a smooth rank-two frame. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma scaleFirstInput_apply (r : ℝ) (v : Base) :
    scaleFirstInput r v = ![r*v 0,v 1] := by
  ext i
  fin_cases i <;> simp [scaleFirstInput,mul_comm]

lemma scaleFirstInput_injective {r : ℝ} (hr : r ≠ 0) :
    Function.Injective (scaleFirstInput r) := by
  intro u v he
  rw [scaleFirstInput_apply,scaleFirstInput_apply] at he
  have h0 : u 0 = v 0 := mul_left_cancel₀ hr (congrFun he 0)
  have h1 : u 1 = v 1 := congrFun he 1
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma scaleFirstInput_smooth : ContDiff ℝ ∞ scaleFirstInput := by
  have hV : ContDiff ℝ ∞ (fun r : ℝ => (![r,0] : Base)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_id
    · exact contDiff_const
  exact (contDiff_const.smulRight hV).add contDiff_const

lemma firstColumnLength_pos {L : Base →L[ℝ] FrameTarget} (hL : Function.Injective L) :
    0 < firstColumnLength L := by
  apply Real.sqrt_pos.mpr
  by_contra hn
  have hs : (L (![1,0] : Base) 0)^2+(L (![1,0] : Base) 1)^2+(L (![1,0] : Base) 2)^2 ≤ 0 :=
    le_of_not_gt hn
  have h0 : L (![1,0] : Base) 0 = 0 := by nlinarith [sq_nonneg (L ![1,0] 0),sq_nonneg (L ![1,0] 1),sq_nonneg (L ![1,0] 2)]
  have h1 : L (![1,0] : Base) 1 = 0 := by nlinarith [sq_nonneg (L ![1,0] 0),sq_nonneg (L ![1,0] 1),sq_nonneg (L ![1,0] 2)]
  have h2 : L (![1,0] : Base) 2 = 0 := by nlinarith [sq_nonneg (L ![1,0] 0),sq_nonneg (L ![1,0] 1),sq_nonneg (L ![1,0] 2)]
  have hz : L (![1,0] : Base) = L 0 := by
    rw [map_zero]
    ext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have he := congrFun (hL hz) 0
  norm_num at he

lemma normalizeFrameColumn_injective {L : Base →L[ℝ] FrameTarget} (hL : Function.Injective L) :
    Function.Injective (normalizeFrameColumn L) :=
  hL.comp (scaleFirstInput_injective (inv_ne_zero (firstColumnLength_pos hL).ne'))

lemma firstColumnLength_smooth {A : Base → Base →L[ℝ] FrameTarget} (hA : ContDiff ℝ ∞ A)
    (hI : ∀ x, Function.Injective (A x)) : ContDiff ℝ ∞ (fun x => firstColumnLength (A x)) := by
  have hv := hA.clm_apply (contDiff_const (c := (![1,0] : Base)))
  have h0 : ContDiff ℝ ∞ (fun x => (A x) (![1,0] : Base) 0) := (contDiff_apply ℝ ℝ 0).comp hv
  have h1 : ContDiff ℝ ∞ (fun x => (A x) (![1,0] : Base) 1) := (contDiff_apply ℝ ℝ 1).comp hv
  have h2 : ContDiff ℝ ∞ (fun x => (A x) (![1,0] : Base) 2) := (contDiff_apply ℝ ℝ 2).comp hv
  apply ((h0.pow 2).add (h1.pow 2) |>.add (h2.pow 2)).sqrt
  intro x
  exact (Real.sqrt_pos.mp (firstColumnLength_pos (hI x))).ne'

lemma normalizeFrameColumn_smooth {A : Base → Base →L[ℝ] FrameTarget} (hA : ContDiff ℝ ∞ A)
    (hI : ∀ x, Function.Injective (A x)) : ContDiff ℝ ∞ (fun x => normalizeFrameColumn (A x)) :=
  hA.clm_comp (scaleFirstInput_smooth.comp
    ((firstColumnLength_smooth hA hI).inv (fun x => (firstColumnLength_pos (hI x)).ne')))

lemma firstColumnLength_axisNormalFrame (r y z : ℝ) (hr : 0 ≤ r) :
    firstColumnLength (axisNormalFrame r y z) = r := by
  simp [firstColumnLength,axisNormalFrame,Real.sqrt_sq hr]

lemma normalizeFrameColumn_axisNormalFrame (r y z : ℝ) (hr : 0 < r) :
    normalizeFrameColumn (axisNormalFrame r y z) = axisNormalFrame 1 y z := by
  rw [normalizeFrameColumn,firstColumnLength_axisNormalFrame r y z hr.le]
  ext v i
  fin_cases i <;> simp [ContinuousLinearMap.comp_apply,scaleFirstInput_apply,axisNormalFrame,
    hr.ne',mul_comm,mul_left_comm]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_DoubleRotationFilling
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit relative filling of the twice-winding planar frame.
The third quaternion coordinate is a compact bump; no square-root choice
or topological extension assumption is needed. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma filledDoubleRotation_smooth {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (filledDoubleRotation χ) := by
  have hu : ContDiff ℝ ∞ (fun x : Base => rotationFirst (x 0) (x 1) (χ x)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [rotationFirst] <;> fun_prop
  have hv : ContDiff ℝ ∞ (fun x : Base => rotationSecond (x 0) (x 1) (χ x)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [rotationSecond] <;> fun_prop
  exact (contDiff_const.smulRight hu).add (contDiff_const.smulRight hv)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ShiftedRotationFilling
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact explicit filling of the frame for two equal-index zeros. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma filledShiftedRotation_smooth {χ ψ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (filledShiftedRotation χ ψ) := by
  have hV : ContDiff ℝ ∞ (fun x => (![0,1-ψ x,0] : FrameTarget)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_const.sub hψ
    · exact contDiff_const
  exact (filledDoubleRotation_smooth hχ).sub (contDiff_const.smulRight hV)

lemma norm_large_square_sum_radius {x : Base} {r : ℝ} (hr : 1 < r)
    (hx : x ∉ closedBall (0:Base) r) :
    1 < (x 0)^2+(x 1)^2 := by
  by_contra hh
  have hs : (x 0)^2+(x 1)^2 ≤ 1 := le_of_not_gt hh
  have hn : ‖x‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro i
    rw [Real.norm_eq_abs,abs_le]
    fin_cases i
    · change -1 ≤ x 0 ∧ x 0 ≤ 1
      constructor <;> nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
    · change -1 ≤ x 1 ∧ x 1 ≤ 1
      constructor <;> nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
  apply hx
  simpa only [mem_closedBall,dist_zero_right] using hn.trans hr.le

theorem compact_shifted_double_filling_radius {R : ℝ} (hR : 1 < R) :
    ∃ (A : Base → Base →L[ℝ] FrameTarget) (K : Set Base),
      ContDiff ℝ ∞ A ∧ (∀ x, Function.Injective (A x)) ∧ IsCompact K ∧
      K ⊆ ball (0:Base) R ∧ ∀ x ∉ K, A =ᶠ[𝓝 x] shiftedDoubleFrame := by
  let r : ℝ := (1+R)/2
  have hr : 1 < r := by dsimp [r] <;> linarith
  have hrR : r < R := by dsimp [r] <;> linarith
  obtain ⟨χ,hχ,hχc,_hχr,hχs,hχone⟩ := CollarVelocity.compact_cutoff
    (isCompact_singleton (x := (0:Base))) isOpen_ball
    (singleton_subset_iff.mpr (mem_ball_self (by linarith : (0:ℝ) < r)))
  obtain ⟨ψ,hψ,hψc,hψr,hψs,hψone⟩ := CollarVelocity.compact_cutoff
    (isCompact_closedBall (0:Base) r) isOpen_ball
    (closedBall_subset_ball hrR)
  let A := filledShiftedRotation χ ψ
  let K := tsupport χ ∪ tsupport ψ
  refine ⟨A,K,filledShiftedRotation_smooth hχ hψ,?_,hχc.union hψc,?_,?_⟩
  · intro x
    change Function.Injective (shiftedRotationFrame (x 0) (x 1) (χ x) (1-ψ x))
    apply shiftedRotationFrame_injective
    · by_cases hx : x = 0
      · subst x
        rw [hχone 0 (mem_singleton 0)]
        norm_num
      · have hn : 0 < (x 0)^2+(x 1)^2 := by
          by_contra hh
          have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
          have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
          apply hx
          ext i
          fin_cases i
          · exact h0
          · exact h1
        exact add_pos_of_pos_of_nonneg hn (sq_nonneg _)
    · by_cases he : 1-ψ x = 0
      · exact Or.inl he
      · have hx : x ∉ closedBall (0:Base) r := by
          intro hx
          exact he (by rw [hψone x hx]; ring)
        have hc : χ x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hh => hx (ball_subset_closedBall (hχs hh)))
        exact Or.inr ⟨hc,norm_large_square_sum_radius hr hx,by
          constructor <;> linarith [(hψr x).1,(hψr x).2]⟩
  · intro x hx
    rcases hx with hx | hx
    · exact (ball_subset_ball hrR.le) (hχs hx)
    · exact hψs hx
  · intro x hx
    have hxc : x ∉ tsupport χ := fun h => hx (Or.inl h)
    have hxp : x ∉ tsupport ψ := fun h => hx (Or.inr h)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxc,
      notMem_tsupport_iff_eventuallyEq.mp hxp] with y hyc hyp
    change χ y = 0 at hyc
    change ψ y = 0 at hyp
    change shiftedRotationFrame (y 0) (y 1) (χ y) (1-ψ y) = shiftedDoubleFrame y
    simp only [hyc,hyp,sub_zero,shiftedDoubleFrame]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_EqualIndexFrameFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The equal-index polynomial pair has a genuine compact relative frame filling. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem compact_equal_index_frame_filling_radius {R : ℝ} (hR : 1 < R) :
    ∃ (B : Base → Base →L[ℝ] FrameTarget) (K : Set Base),
      ContDiff ℝ ∞ B ∧ (∀ x, Function.Injective (B x)) ∧ IsCompact K ∧
      K ⊆ ball (0:Base) R ∧ ∀ x ∉ K, B =ᶠ[𝓝 x] equalIndexFrame := by
  obtain ⟨A,K,hA,hAI,hK,hKB,hAe⟩ := compact_shifted_double_filling_radius hR
  refine ⟨fun x => normalizeFrameColumn (A x),K,normalizeFrameColumn_smooth hA hAI,
    fun x => normalizeFrameColumn_injective (hAI x),hK,hKB,?_⟩
  intro x hx
  filter_upwards [hAe x hx] with y hy
  have he : shiftedDoubleFrame y =
      axisNormalFrame ((y 0)^2+(y 1)^2) ((y 0)^2-(y 1)^2-1) (2*y 0*y 1) :=
    shiftedRotationFrame_zero_c _ _ _
  have hr : 0 < (y 0)^2+(y 1)^2 := by
    have hp := firstColumnLength_pos (hAI y)
    rwa [hy,he,firstColumnLength_axisNormalFrame _ _ _ (by positivity)] at hp
  change normalizeFrameColumn (A y) = _
  rw [hy,he,normalizeFrameColumn_axisNormalFrame _ _ _ hr]
  rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RelativeDefectFilling
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact frame fillings are preserved by a homotopy whose only zeros stay
inside the fixed compact core. The pasting retains exact exterior values. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma defectFrame_smooth {N : Base → Base} (hN : ContDiff ℝ ∞ N) :
    ContDiff ℝ ∞ (defectFrame N) := by
  have h : ContDiff ℝ ∞ (fun x => (![0,N x 0,N x 1] : FrameTarget)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact (contDiff_apply ℝ ℝ 0).comp hN
    · exact (contDiff_apply ℝ ℝ 1).comp hN
  exact contDiff_const.add (contDiff_const.smulRight h)

lemma defectFrame_injective {N : Base → Base} {x : Base} (hN : N x ≠ 0) :
    Function.Injective (defectFrame N x) := by
  apply axisNormalFrame_injective (by norm_num)
  by_contra hn
  push Not at hn
  apply hN
  ext i
  fin_cases i
  · exact hn.1
  · exact hn.2

theorem relativeDefectFilling_homotopy
    {H : ℝ → Base → Base} (hH : ContDiff ℝ ∞ (fun z : ℝ × Base => H z.1 z.2))
    {U Z : Set Base} (hU : IsOpen U) (hZ : IsCompact Z) (hZU : Z ⊆ U)
    (hz : ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ U, x ∉ Z → H s x ≠ 0)
    (hfill : HasRelativeDefectFilling (H 1) U) :
    HasRelativeDefectFilling (H 0) U := by
  obtain ⟨B,K,hB,hK,hKU,hBI,hBe⟩ := hfill
  obtain ⟨χ,hχ,hχc,hχr,hχs,hχone⟩ :=
    CollarVelocity.compact_cutoff (hK.union hZ) hU (union_subset hKU hZU)
  let Q := fun s x => defectFrame (H s) x
  let A := fun x => B x+Q (χ x) x-Q 1 x
  have hQc : ContDiff ℝ ∞ (fun x => Q (χ x) x) :=
    defectFrame_smooth (hH.comp (hχ.prodMk contDiff_id))
  have hQ1 : ContDiff ℝ ∞ (Q 1) :=
    defectFrame_smooth (hH.comp (contDiff_const.prodMk contDiff_id))
  refine ⟨A,K ∪ tsupport χ,(hB.add hQc).sub hQ1,hK.union hχc,
    union_subset hKU hχs,?_,?_⟩
  · intro x hx
    by_cases he : χ x = 1
    · have hAB : A x = B x := by simp [A,he]
      rw [hAB]
      exact hBI x hx
    · have hxK : x ∉ K := fun hk => he (hχone x (Or.inl hk))
      have hxZ : x ∉ Z := fun hz' => he (hχone x (Or.inr hz'))
      have hAQ : A x = Q (χ x) x := by
        dsimp only [A]
        rw [hBe x hxK]
        dsimp [Q]
        abel
      rw [hAQ]
      exact defectFrame_injective (hz (χ x) (hχr x) x hx hxZ)
  · intro x hx
    have hxK : x ∉ K := fun h => hx (Or.inl h)
    have hxχ : x ∉ tsupport χ := fun h => hx (Or.inr h)
    have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hxχ
    dsimp only [A]
    rw [hχ0,hBe x hxK]
    dsimp [Q]
    abel

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_OppositeIndexFrameFilling
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The opposite-index pair can be filled while keeping its first column fixed. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma filledOppositeIndex_smooth {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (filledOppositeIndex χ) := by
  have hy : ContDiff ℝ ∞ (fun x : Base =>
      (![0,(x 0)^2-1+2*χ (x 0)*χ (x 1),x 1] : FrameTarget)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact (((contDiff_apply ℝ ℝ 0).pow 2).sub contDiff_const).add
        ((contDiff_const.mul (hχ.comp (contDiff_apply ℝ ℝ 0))).mul
          (hχ.comp (contDiff_apply ℝ ℝ 1)))
    · exact contDiff_apply ℝ ℝ 1
  exact contDiff_const.add (contDiff_const.smulRight hy)

theorem compact_opposite_index_frame_filling_radius {R : ℝ} (hR : 1 < R) :
    ∃ (B : Base → Base →L[ℝ] FrameTarget) (K : Set Base),
      ContDiff ℝ ∞ B ∧ (∀ x, Function.Injective (B x)) ∧ IsCompact K ∧
      K ⊆ ball (0:Base) R ∧ ∀ x ∉ K, B =ᶠ[𝓝 x] oppositeIndexFrame := by
  let u : ℝ := (1+R)/2
  let v : ℝ := (u+R)/2
  have hu : 1 < u := by dsimp [u] <;> linarith
  have huv : u < v := by dsimp [u,v] <;> linarith
  have hvR : v < R := by dsimp [u,v] <;> linarith
  have hv : 0 < v := by linarith
  obtain ⟨χ,hχ,_hχc,hχrange,hχsupp,hχone⟩ := CollarVelocity.compact_cutoff
    (isCompact_closedBall (0:ℝ) u) isOpen_ball (closedBall_subset_ball huv)
  have hχ0 : χ 0 = 1 := hχone 0 (mem_closedBall_self (by linarith))
  let B := filledOppositeIndex χ
  let K := closedBall (0:Base) v
  have hz : ∀ x ∉ K, χ (x 0)*χ (x 1) = 0 := by
    intro x hx
    by_contra hh
    obtain ⟨h0,h1⟩ := mul_ne_zero_iff.mp hh
    have hb0 := hχsupp (subset_tsupport χ h0)
    have hb1 := hχsupp (subset_tsupport χ h1)
    have hn : ‖x‖ ≤ v := by
      apply (pi_norm_le_iff_of_nonneg hv.le).mpr
      intro i
      fin_cases i
      · change ‖x 0‖ ≤ v
        have hb : ‖x 0‖ < v := by simpa only [mem_ball,dist_zero_right] using hb0
        exact hb.le
      · change ‖x 1‖ ≤ v
        have hb : ‖x 1‖ < v := by simpa only [mem_ball,dist_zero_right] using hb1
        exact hb.le
    exact hx (by simpa only [K,mem_closedBall,dist_zero_right] using hn)
  refine ⟨B,K,filledOppositeIndex_smooth hχ,?_,isCompact_closedBall _ _,
    closedBall_subset_ball hvR,?_⟩
  · intro x
    apply axisNormalFrame_injective (by norm_num)
    by_cases hx1 : x 1 = 0
    · left
      rw [hx1,hχ0,mul_one]
      have hp : 0 < (x 0)^2-1+2*χ (x 0) := by
        by_cases hxu : x 0 ∈ closedBall (0:ℝ) u
        · rw [hχone _ hxu]
          nlinarith [sq_nonneg (x 0)]
        · have ha : u < |x 0| := by
            simpa only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,not_le] using hxu
          have hs := (one_lt_sq_iff_one_lt_abs (x 0)).mpr (hu.trans ha)
          nlinarith [(hχrange (x 0)).1]
      exact hp.ne'
    · exact Or.inr hx1
  · intro x hx
    filter_upwards [(isClosed_closedBall.isOpen_compl).mem_nhds hx] with y hy
    have he := hz y hy
    change axisNormalFrame 1 ((y 0)^2-1+2*χ (y 0)*χ (y 1)) (y 1) = _
    have hzero : 2*χ (y 0)*χ (y 1) = 0 := by rw [mul_assoc,he,mul_zero]
    simp only [hzero,add_zero,oppositeIndexFrame]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PairModelCoordinates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine coordinates and invertible normal rescalings for the model pair. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma normalPairScale_apply (a b : ℝ) (v : FrameTarget) :
    normalPairScale a b v = ![v 0,a*v 1,b*v 2] := by
  ext i
  fin_cases i <;> simp [normalPairScale,mul_comm]

lemma normalPairScale_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Injective (normalPairScale a b) := by
  intro u v he
  rw [normalPairScale_apply,normalPairScale_apply] at he
  ext i
  fin_cases i
  · exact congrFun he 0
  · exact mul_left_cancel₀ ha (congrFun he 1)
  · exact mul_left_cancel₀ hb (congrFun he 2)

lemma normalPairScale_axis (a b r y z : ℝ) :
    (normalPairScale a b).comp (axisNormalFrame r y z) = axisNormalFrame r (a*y) (b*z) := by
  ext v i
  fin_cases i <;> simp [normalPairScale,axisNormalFrame] <;> ring

/-- Pull a compact model filling back by an affine chart and rescale its two
normal coordinates. The support is the actual inverse image of the model support. -/
theorem pullback_model_filling {Q : Base → Base →L[ℝ] FrameTarget}
    {B : Base → Base →L[ℝ] FrameTarget} (hB : ContDiff ℝ ∞ B)
    (hBI : ∀ x, Function.Injective (B x)) {K : Set Base} (hK : IsCompact K)
    (hBe : ∀ x ∉ K, B =ᶠ[𝓝 x] Q)
    (c h k a b : ℝ) (hh : h ≠ 0) (hk : k ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ A : Base → Base →L[ℝ] FrameTarget,
      ContDiff ℝ ∞ A ∧ (∀ x, Function.Injective (A x)) ∧
      IsCompact ((pairCoordinates c h k hh hk) ⁻¹' K) ∧
      ∀ x ∉ (pairCoordinates c h k hh hk) ⁻¹' K,
        A x = (normalPairScale a b).comp (Q (pairCoordinateMap c h k x)) := by
  let e := pairCoordinates c h k hh hk
  let A := fun x => (normalPairScale a b).comp (B (e x))
  refine ⟨A,contDiff_const.clm_comp (hB.comp (pairCoordinateMap_smooth c h k)),?_,?_,?_⟩
  · intro x
    exact (normalPairScale_injective ha hb).comp (hBI (e x))
  · exact e.isCompact_preimage.mpr hK
  · intro x hx
    have he : B (e x) = Q (e x) := (hBe (e x) hx).eq_of_nhds
    dsimp [A]
    rw [he]
    rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ThinPairCoordinates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Model fillings can be made arbitrarily thin around the connecting interval. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma thin_pair_coordinates {c h : ℝ} (hh : 0 < h) {U : Set Base} (hU : IsOpen U)
    (haxis : ∀ t ∈ Icc (c-h) (c+h), crosscapAxis t ∈ U) :
    ∃ R k : ℝ, 1 < R ∧ 0 < k ∧
      (pairCoordinateMap c h k) ⁻¹' ball (0:Base) R ⊆ U := by
  obtain ⟨r,hr,hrect⟩ := compact_axis_rectangle (show c-h ≤ c+h by linarith) hU
    (by simpa only [crosscapAxis_apply] using haxis)
  let R := 1+r/(2*h)
  let k := 2*R/r
  have hR : 1 < R := by
    have hp : 0 < r/(2*h) := div_pos hr (mul_pos (by norm_num) hh)
    dsimp [R]
    linarith
  have hk : 0 < k := by dsimp [k] <;> positivity
  have hRh : R*h = h+r/2 := by dsimp [R]; field_simp
  have hkhalf : k*(r/2) = R := by dsimp [k]; field_simp
  refine ⟨R,k,hR,hk,?_⟩
  intro x hx
  have hn : ‖pairCoordinateMap c h k x‖ < R := by simpa only [mem_preimage,mem_ball,dist_zero_right] using hx
  have hu : |(x 1-c)/h| < R := by
    exact (norm_le_pi_norm (pairCoordinateMap c h k x) 0).trans_lt hn
  have hv : |k*x 0| < R := by
    exact (norm_le_pi_norm (pairCoordinateMap c h k x) 1).trans_lt hn
  have hxt : -r ≤ x 0 ∧ x 0 ≤ r := by
    rw [abs_lt] at hv
    constructor <;> nlinarith
  have htt : c-h-r ≤ x 1 ∧ x 1 ≤ c+h+r := by
    rw [abs_lt] at hu
    have hl : -R*h < x 1-c := (lt_div_iff₀ hh).mp hu.1
    have hu' : x 1-c < R*h := (div_lt_iff₀ hh).mp hu.2
    constructor <;> linarith
  have he : (![x 0,x 1] : Base) = x := by ext i; fin_cases i <;> rfl
  rw [←he]
  exact hrect (x 0) hxt (x 1) htt

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CenteredPairModels
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed canonical normal fields and their scaled frame fillings. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma centeredEqualHomotopy_smooth (c h k s : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × Base => centeredEqualHomotopy c h k s z.1 z.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [centeredEqualHomotopy] <;> fun_prop

lemma centeredEqualHomotopy_zero_iff {c h k s v : ℝ} (hh : 0 < h) (hs : s ≠ 0)
    (hv : 0 ≤ v) (x : Base) :
    centeredEqualHomotopy c h k s v x = 0 ↔
      x = crosscapAxis (c-h) ∨ x = crosscapAxis (c+h) := by
  constructor
  · intro he
    have h0 : (x 1-c)^2-h^2-v*(h*k*x 0)^2 = 0 := congrFun he 0
    have h1 : s*((x 1-c)/h)*x 0 = 0 := congrFun he 1
    have hx0 : x 0 = 0 := by
      by_contra hn
      have hc : x 1 = c := by
        have hc' := (mul_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hn)).resolve_left hs
        exact sub_eq_zero.mp ((div_eq_zero_iff).mp hc' |>.resolve_right hh.ne')
      rw [hc] at h0
      have := mul_nonneg hv (sq_nonneg (h*k*x 0))
      nlinarith [sq_pos_of_pos hh]
    rw [hx0] at h0
    have hf : (x 1-(c-h))*(x 1-(c+h)) = 0 := by nlinarith [h0]
    rcases mul_eq_zero.mp hf with hl | hr
    · left
      ext i
      fin_cases i <;> simp [crosscapAxis_apply,hx0,sub_eq_zero.mp hl]
    · right
      ext i
      fin_cases i <;> simp [crosscapAxis_apply,hx0,sub_eq_zero.mp hr]
  · rintro (rfl | rfl) <;> ext i <;> fin_cases i <;>
      simp [centeredEqualHomotopy,crosscapAxis_apply]

lemma centeredOppositeNormal_scaled (c h k s : ℝ) (hh : h ≠ 0) (hk : k ≠ 0) (x : Base) :
    (normalPairScale (h^2) (s/k)).comp (oppositeIndexFrame (pairCoordinateMap c h k x)) =
      defectFrame (centeredOppositeNormal c h s) x := by
  rw [oppositeIndexFrame,normalPairScale_axis]
  congr 1 <;> dsimp [pairCoordinateMap,defectFrame,centeredOppositeNormal]
  · field_simp
  · field_simp

lemma centeredEqualNormal_scaled (c h k s : ℝ) (hh : h ≠ 0) (hk : k ≠ 0) (x : Base) :
    (normalPairScale (h^2) (s/(2*k))).comp (equalIndexFrame (pairCoordinateMap c h k x)) =
      defectFrame (centeredEqualNormal c h k s) x := by
  rw [equalIndexFrame,normalPairScale_axis]
  congr 1 <;> dsimp [pairCoordinateMap,defectFrame,centeredEqualNormal]
  · field_simp
    ring
  · field_simp

theorem centeredOppositeNormal_filling {c h s : ℝ} (hh : 0 < h) (hs : s ≠ 0)
    {U : Set Base} (hU : IsOpen U)
    (haxis : ∀ t ∈ Icc (c-h) (c+h), crosscapAxis t ∈ U) :
    HasRelativeDefectFilling (centeredOppositeNormal c h s) U := by
  obtain ⟨R,k,hR,hk,hbox⟩ := thin_pair_coordinates hh hU haxis
  obtain ⟨B,K,hB,hBI,hK,hKR,hBe⟩ := compact_opposite_index_frame_filling_radius hR
  obtain ⟨A,hA,hAI,hK',hAe⟩ := pullback_model_filling hB hBI hK hBe c h k (h^2) (s/k)
    hh.ne' hk.ne' (pow_ne_zero _ hh.ne') (div_ne_zero hs hk.ne')
  refine ⟨A,(pairCoordinates c h k hh.ne' hk.ne') ⁻¹' K,hA,hK',?_,fun x _ => hAI x,?_⟩
  · intro x hx
    exact hbox (hKR hx)
  · intro x hx
    rw [hAe x hx]
    exact centeredOppositeNormal_scaled c h k s hh.ne' hk.ne' x

theorem centeredEqualNormal_filling {c h k s R : ℝ} (hh : 0 < h) (hk : 0 < k)
    (hs : s ≠ 0) (hR : 1 < R) {U : Set Base}
    (hbox : (pairCoordinateMap c h k) ⁻¹' ball (0:Base) R ⊆ U) :
    HasRelativeDefectFilling (centeredEqualNormal c h k s) U := by
  obtain ⟨B,K,hB,hBI,hK,hKR,hBe⟩ := compact_equal_index_frame_filling_radius hR
  obtain ⟨A,hA,hAI,hK',hAe⟩ := pullback_model_filling hB hBI hK hBe c h k (h^2) (s/(2*k))
    hh.ne' hk.ne' (pow_ne_zero _ hh.ne') (div_ne_zero hs (mul_ne_zero (by norm_num) hk.ne'))
  refine ⟨A,(pairCoordinates c h k hh.ne' hk.ne') ⁻¹' K,hA,hK',?_,fun x _ => hAI x,?_⟩
  · intro x hx
    exact hbox (hKR hx)
  · intro x hx
    rw [hAe x hx]
    exact centeredEqualNormal_scaled c h k s hh.ne' hk.ne' x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_RelativeFramePatching
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth field specified near its compact modification extends by the
original field, with no change to the support. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem compact_relative_field {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D A : Base → E} (hD : ContDiff ℝ ∞ D) {V K : Set Base}
    (hV : IsOpen V) (hA : ContDiffOn ℝ ∞ A V) (hK : IsCompact K) (hKV : K ⊆ V)
    (he : ∀ x ∈ V, x ∉ K → A x = D x) :
    ∃ B : Base → E, ContDiff ℝ ∞ B ∧ tsupport (B-D) ⊆ K ∧
      EqOn B A V ∧ ∀ x ∉ K, B x = D x := by
  obtain ⟨χ,hχ,_hc,_hr,hχV,hχone⟩ := CollarVelocity.compact_cutoff hK hV hKV
  let B := fun x => D x+χ x • (A x-D x)
  have hB : ContDiff ℝ ∞ B := hD.add
    (CollarVelocity.supported_local_smul hV hχ (hA.sub hD.contDiffOn) hχV)
  have hext : ∀ x ∉ K, B x = D x := by
    intro x hx
    by_cases hxV : x ∈ V
    · simp [B,he x hxV hx]
    · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hxV (hχV ht))
      simp [B,hz]
  refine ⟨B,hB,?_,?_,hext⟩
  · apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    exact hx (by simp only [Pi.sub_apply,hext x hxK,sub_self])
  · intro x hx
    by_cases hxK : x ∈ K
    · simp only [B,hχone x hxK,one_smul,add_sub_cancel]
    · rw [hext x hxK,he x hx hxK]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalFrameTransport
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact algebra transporting a filled normalized frame to the derivative
of the original surface map. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma longitudinalShear_injective (c : ℝ) : Function.Injective (longitudinalShear c) := by
  intro u v he
  have h1 : u 1 = v 1 := by simpa [longitudinalShear] using congrFun he 1
  have h0 : u 0+u 1*c = v 0+v 1*c := congrFun he 0
  rw [h1] at h0
  ext i
  fin_cases i
  · exact add_right_cancel h0
  · exact h1

lemma longitudinalShear_smooth : ContDiff ℝ ∞ longitudinalShear := by
  have h : ContDiff ℝ ∞ (fun c : ℝ => (![c,0] : Base)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  exact contDiff_const.add (contDiff_const.smulRight h)

lemma defectFrame_shear_apply (N : Base → Base) (x : Base) (c : ℝ) (v : Base) :
    defectFrame N x (longitudinalShear c v) = ![v 0+v 1*c,v 1*N x 0,v 1*N x 1] := by
  ext i
  fin_cases i <;> simp [defectFrame,axisNormalFrame,longitudinalShear,Matrix.vecHead,Matrix.vecTail]

lemma normalOutput_apply (d : Base) (v : FrameTarget) :
    normalOutput d v = (planeComplexFrame d ![v 1,v 2],v 0) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [normalOutput,planeComplexFrame_apply] <;> ring
  · simp [normalOutput]

lemma normalOutput_injective {d : Base} (hd : d ≠ 0) : Function.Injective (normalOutput d) := by
  intro u v he
  rw [normalOutput_apply,normalOutput_apply] at he
  have h12 := (planeComplexFrame_invertible hd).injective (congrArg Prod.fst he)
  ext i
  fin_cases i
  · exact congrArg Prod.snd he
  · exact congrFun h12 0
  · exact congrFun h12 1

lemma normalOutput_smooth : ContDiff ℝ ∞ normalOutput := by
  exact (contDiff_const.add (contDiff_const.smulRight
    ((planeComplexFrame_smooth.clm_apply contDiff_const).prodMk contDiff_const))).add
    (contDiff_const.smulRight
      ((planeComplexFrame_smooth.clm_apply contDiff_const).prodMk contDiff_const))

lemma frameTarget_plane_columns (L : Base →L[ℝ] FrameTarget) :
    L = (ContinuousLinearMap.proj 0).smulRight (L (![1,0] : Base))+
      (ContinuousLinearMap.proj 1).smulRight (L (![0,1] : Base)) := by
  ext v : 1
  have hv : v = v 0 • (![1,0] : Base)+v 1 • (![0,1] : Base) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  rw [map_add,map_smul,map_smul]
  rfl

lemma transportedNormalFrame_injective {φ : Base → ProjectionTarget 3} {a : FrameTarget}
    {d : ℝ → Base} {B : Base → Base →L[ℝ] FrameTarget} {x : Base}
    (hu : transverseDerivative φ x ≠ 0) (ha : ∀ r : ℝ, r • transverseDerivative φ x ≠ a)
    (hd : d (x 1) ≠ 0) (hB : Function.Injective (B x)) :
    Function.Injective (transportedNormalFrame φ a d B x) :=
  (curveNormalLinear_bijective hu ha).1.comp ((normalOutput_injective hd).comp
    (hB.comp (longitudinalShear_injective _)))

lemma transportedNormalFrame_exact (φ : Base → ProjectionTarget 3) (a : FrameTarget)
    (d : ℝ → Base) (x : Base) (hu : transverseDerivative φ x ≠ 0)
    (ha : ∀ r : ℝ, r • transverseDerivative φ x ≠ a) (hd : d (x 1) ≠ 0) :
    transportedNormalFrame φ a d (defectFrame (axisNormalizedDefect d (normalDefect φ a))) x =
      coordinateDifferential φ x := by
  let T := curveNormalLinear (transverseDerivative φ x) a
  have hT := curveNormalLinear_invertible hu ha
  have hP := planeComplexFrame_invertible hd
  have hL := frameTarget_plane_columns (coordinateDifferential φ x)
  rw [hL]
  ext v : 1
  change T (normalOutput (d (x 1))
    (defectFrame (axisNormalizedDefect d (normalDefect φ a)) x (longitudinalShear (longitudinalCoefficient φ a x) v))) = _
  rw [defectFrame_shear_apply,normalOutput_apply]
  have he : planeComplexFrame (d (x 1)) (axisNormalizedDefect d (normalDefect φ a) x) = normalDefect φ a x :=
    hP.self_apply_inverse _
  have hz : (![v 1 * axisNormalizedDefect d (normalDefect φ a) x 0,
      v 1 * axisNormalizedDefect d (normalDefect φ a) x 1] : Base) =
      v 1 • axisNormalizedDefect d (normalDefect φ a) x := by ext i; fin_cases i <;> rfl
  change T (planeComplexFrame (d (x 1))
    ![v 1 * axisNormalizedDefect d (normalDefect φ a) x 0,
      v 1 * axisNormalizedDefect d (normalDefect φ a) x 1],
    v 0+v 1*longitudinalCoefficient φ a x) = _
  rw [hz,map_smul,he]
  have hepair : (v 1 • normalDefect φ a x,v 0+v 1*longitudinalCoefficient φ a x) =
      v 0 • ((0:Base),1)+v 1 • T.inverse (coordinateDifferential φ x ![0,1]) := by
    apply Prod.ext
    · simp [normalDefect,T]
    · simp [longitudinalCoefficient,T]
  rw [hepair,map_add,map_smul,map_smul,hT.self_apply_inverse]
  have hvel : T ((0:Base),1) = coordinateDifferential φ x ![1,0] := by
    simp [T,curveNormalLinear_apply,transverseDerivative]
  rw [hvel]
  rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SignedDiagonalFilling
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Either possible pair of transverse endpoint signs admits a compact
relative frame filling in every neighborhood of the whole connecting interval. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma nonzeroSign_ne_zero (a : ℝ) : nonzeroSign a ≠ 0 := by
  unfold nonzeroSign
  split <;> norm_num

lemma nonzeroSign_cases (a b : ℝ) :
    nonzeroSign a = nonzeroSign b ∨ nonzeroSign b = -nonzeroSign a := by
  unfold nonzeroSign
  split <;> split <;> norm_num

theorem signed_diagonal_filling {p q a b : ℝ} (hpq : p < q)
    {U : Set Base} (hU : IsOpen U)
    (haxis : ∀ t ∈ Icc p q, crosscapAxis t ∈ U) :
    HasRelativeDefectFilling (diagonalDefectModel (endpointSignModel p q a b) p q) U := by
  let c := (p+q)/2
  let h := (q-p)/2
  have hh : 0 < h := by dsimp [h] <;> linarith
  have hleft : c-h = p := by dsimp [c,h] <;> ring
  have hright : c+h = q := by dsimp [c,h] <;> ring
  have hax : ∀ t ∈ Icc (c-h) (c+h), crosscapAxis t ∈ U := by
    simpa only [hleft,hright] using haxis
  rcases nonzeroSign_cases a b with hsame | hopp
  · have hmodel : diagonalDefectModel (endpointSignModel p q a b) p q =
        centeredOppositeNormal c h (nonzeroSign a) := by
      funext x
      rw [diagonalDefectModel_apply,endpointSignModel_same hpq.ne hsame]
      ext i
      fin_cases i
      · dsimp [centeredOppositeNormal,c,h]
        ring
      · dsimp [centeredOppositeNormal]
        ring
    rw [hmodel]
    exact centeredOppositeNormal_filling hh (nonzeroSign_ne_zero a) hU hax
  · obtain ⟨R,k,hR,hk,hbox⟩ := thin_pair_coordinates hh hU hax
    let H := centeredEqualHomotopy c h k (-nonzeroSign a)
    have h1 : H 1 = centeredEqualNormal c h k (-nonzeroSign a) := by
      funext x
      ext i
      fin_cases i <;> simp [H,centeredEqualHomotopy,centeredEqualNormal]
    have h0 : H 0 = diagonalDefectModel (endpointSignModel p q a b) p q := by
      funext x
      rw [diagonalDefectModel_apply,endpointSignModel_opposite hpq.ne hopp]
      ext i
      fin_cases i
      · dsimp [H,centeredEqualHomotopy,c,h]
        ring
      · dsimp [H,centeredEqualHomotopy,c,h]
        field_simp
        ring
    have hfill : HasRelativeDefectFilling (H 1) U := by
      rw [h1]
      exact centeredEqualNormal_filling hh hk (neg_ne_zero.mpr (nonzeroSign_ne_zero a)) hR hbox
    have hz : ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ U,
        x ∉ ({crosscapAxis p,crosscapAxis q} : Set Base) → H s x ≠ 0 := by
      intro s hs x _ hx he
      have hr := (centeredEqualHomotopy_zero_iff hh
        (neg_ne_zero.mpr (nonzeroSign_ne_zero a)) hs.1 x).mp he
      rw [hleft,hright] at hr
      exact hx (by simpa only [mem_insert_iff,mem_singleton_iff] using hr)
    have hzU : ({crosscapAxis p,crosscapAxis q} : Set Base) ⊆ U := by
      intro x hx
      rcases hx with (rfl | rfl)
      · exact haxis p (left_mem_Icc.mpr hpq.le)
      · exact haxis q (right_mem_Icc.mpr hpq.le)
    have hres := relativeDefectFilling_homotopy (centeredEqualHomotopy_smooth c h k (-nonzeroSign a))
      hU (isCompact_singleton.insert _) hzU hz hfill
    change HasRelativeDefectFilling (H 0) U at hres
    rwa [h0] at hres

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ActualRelativeFrame
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth transport and exact exterior pasting produce a genuine formal
differential for the original Euclidean surface map. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma transportedNormalFrame_smoothOn {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) (a : FrameTarget) {d : ℝ → Base} (hd : ContDiff ℝ ∞ d)
    {B : Base → Base →L[ℝ] FrameTarget} (hB : ContDiff ℝ ∞ B)
    {V : Set Base} (hV : V ⊆ normalFrameDomain φ a) :
    ContDiffOn ℝ ∞ (transportedNormalFrame φ a d B) V := by
  have hu := transverseDerivative_smooth hφ
  have hcross : ContDiff ℝ ∞ (fun x => transverseDerivative φ x ⨯₃ a) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [cross_apply] <;> fun_prop
  have hframe : ContDiff ℝ ∞ (fun x => curveNormalLinear (transverseDerivative φ x) a) :=
    ((contDiff_const.smulRight hu).add contDiff_const).add (contDiff_const.smulRight hcross)
  have hc : ContDiffOn ℝ ∞ (longitudinalCoefficient φ a) V := by
    intro x hx
    have hi := (curveNormalLinear_invertible (normalFrameDomain_nonzero (hV hx))
      (normalFrameDomain_transverse (hV hx))).contDiffAt_map_inverse.comp x hframe.contDiffAt
    exact (hi.clm_apply ((coordinateDifferential_smooth hφ).clm_apply contDiff_const).contDiffAt).snd.contDiffWithinAt
  exact hframe.contDiffOn.clm_comp
    (((normalOutput_smooth.comp (hd.comp (contDiff_apply ℝ ℝ 1))).contDiffOn).clm_comp
      (hB.contDiffOn.clm_comp (longitudinalShear_smooth.comp_contDiffOn hc)))

theorem actual_relative_frame {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ)
    (a : FrameTarget) {d : ℝ → Base} (hd : ContDiff ℝ ∞ d)
    {V : Set Base} (hV : IsOpen V) (hVF : V ⊆ normalFrameDomain φ a)
    (hdn : ∀ x ∈ V, d (x 1) ≠ 0) {G : Base → Base}
    (hG : EqOn G (axisNormalizedDefect d (normalDefect φ a)) V)
    (hfill : HasRelativeDefectFilling G V) :
    ∃ (A : Base → Base →L[ℝ] ProjectionTarget 3) (K : Set Base),
      ContDiff ℝ ∞ A ∧ IsCompact K ∧ K ⊆ V ∧
      tsupport (A-fderiv ℝ φ) ⊆ K ∧ (∀ x ∈ V, Function.Injective (A x)) := by
  obtain ⟨B,K,hB,hK,hKV,hBI,hBe⟩ := hfill
  let C := transportedNormalFrame φ a d B
  have hC : ContDiffOn ℝ ∞ C V := transportedNormalFrame_smoothOn hφ a hd hB hVF
  have hCI : ∀ x ∈ V, Function.Injective (C x) := by
    intro x hx
    exact transportedNormalFrame_injective (normalFrameDomain_nonzero (hVF hx))
      (normalFrameDomain_transverse (hVF hx)) (hdn x hx) (hBI x hx)
  have hCe : ∀ x ∈ V, x ∉ K → C x = coordinateDifferential φ x := by
    intro x hx hxK
    have hb : B x = defectFrame (axisNormalizedDefect d (normalDefect φ a)) x := by
      rw [hBe x hxK]
      unfold defectFrame
      rw [hG hx]
    change (curveNormalLinear (transverseDerivative φ x) a).comp
      ((normalOutput (d (x 1))).comp ((B x).comp (longitudinalShear (longitudinalCoefficient φ a x)))) = _
    rw [hb]
    exact transportedNormalFrame_exact φ a d x (normalFrameDomain_nonzero (hVF hx))
      (normalFrameDomain_transverse (hVF hx)) (hdn x hx)
  obtain ⟨D,hD,hDs,hDC,hDe⟩ := compact_relative_field (coordinateDifferential_smooth hφ)
    hV hC hK hKV hCe
  let E := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap
  let A := fun x => E.comp (D x)
  have hA : ContDiff ℝ ∞ A := contDiff_const.clm_comp hD
  have hAe : ∀ x ∉ K, A x = fderiv ℝ φ x := by
    intro x hx
    dsimp [A,E]
    rw [hDe x hx]
    ext v
    simp [coordinateDifferential]
  refine ⟨A,K,hA,hK,hKV,?_,?_⟩
  · apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    exact hx (by simp only [Pi.sub_apply,hAe x hxK,sub_self])
  · intro x hx
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.injective.comp
    rw [hDC hx]
    exact hCI x hx

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_NormalizedPairFilling
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual normalized two-zero field, rather than an assumed standard
model, admits a relative rank-two frame filling near its connecting interval. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem normalized_pair_frame_filling {G : Base → Base} (hG : ContDiff ℝ ∞ G)
    {p q : ℝ} (hpq : p < q) {W : Set ℝ} (hW : IsOpen W) (hKW : Icc p q ⊆ W)
    (haxis : ∀ t ∈ W, G (crosscapAxis t) = ![(t-p)*(t-q),0])
    (hIp : Function.Bijective (fderiv ℝ G (crosscapAxis p)))
    (hIq : Function.Bijective (fderiv ℝ G (crosscapAxis q)))
    {U : Set Base} (hU : IsOpen U) (hAU : ∀ t ∈ Icc p q, crosscapAxis t ∈ U) :
    ∃ V : Set Base, IsOpen V ∧ V ⊆ U ∧
      (∀ t ∈ Icc p q, crosscapAxis t ∈ V) ∧ HasRelativeDefectFilling G V := by
  let a := fderiv ℝ G (crosscapAxis p) (![1,0] : Base) 1
  let b := fderiv ℝ G (crosscapAxis q) (![1,0] : Base) 1
  let F := normalizedLinearModel G p q
  let D := diagonalDefectModel (endpointSignModel p q a b) p q
  have hF : ContDiff ℝ ∞ F := normalizedLinearModel_smooth hG p q
  have hD : ContDiff ℝ ∞ D := diagonalDefectModel_smooth (endpointSignModel_smooth p q a b) p q
  have ha : a ≠ 0 := normalized_axis_transverse_nonzero hG.contDiffAt hW
    (hKW (left_mem_Icc.mpr hpq.le)) haxis hIp
  have hb : b ≠ 0 := normalized_axis_transverse_nonzero hG.contDiffAt hW
    (hKW (right_mem_Icc.mpr hpq.le)) haxis hIq
  have hprod : ∀ t, 0 < (fderiv ℝ G (crosscapAxis t) (![1,0] : Base) 1)*
      endpointSignModel p q a b t →
      0 < (fderiv ℝ F (crosscapAxis t) (![1,0] : Base) 1)*
        (fderiv ℝ D (crosscapAxis t) (![1,0] : Base) 1) := by
    intro t ht
    dsimp [F,D]
    rw [normalizedLinearModel_fderiv_axis hG,diagonalDefectModel_fderiv_axis
      (endpointSignModel_smooth p q a b)]
    simpa [normalTransverse,triangularPlaneJet] using ht
  obtain ⟨r₁,O₁,hr₁,hO₁,hrect₁,hz₁⟩ := linearDefectHomotopy_two_zeros hG hpq hW hKW haxis hIp hIq
  obtain ⟨r₂,O₂,hr₂,hO₂,hrect₂,hz₂⟩ := planeDefectInterpolation_two_zeros hF hD hpq
    isOpen_univ (subset_univ _) (fun t _ => normalizedLinearModel_axis G p q t)
    (fun t _ => diagonalDefectModel_axis _ p q t)
    (hprod p (endpointSignModel_left_mul_pos hpq.ne ha))
    (hprod q (endpointSignModel_right_mul_pos hpq.ne hb))
  let V := U ∩ O₁ ∩ O₂
  have hV : IsOpen V := (hU.inter hO₁).inter hO₂
  have hAV : ∀ t ∈ Icc p q, crosscapAxis t ∈ V := by
    intro t ht
    refine ⟨⟨hAU t ht,?_⟩,?_⟩ <;> rw [crosscapAxis_apply]
    · exact hrect₁ 0 ⟨by linarith,by linarith⟩ t ⟨by linarith [ht.1],by linarith [ht.2]⟩
    · exact hrect₂ 0 ⟨by linarith,by linarith⟩ t ⟨by linarith [ht.1],by linarith [ht.2]⟩
  let Z : Set Base := {crosscapAxis p,crosscapAxis q}
  have hZ : IsCompact Z := isCompact_singleton.insert _
  have hZV : Z ⊆ V := by
    rintro x (rfl | rfl)
    · exact hAV p (left_mem_Icc.mpr hpq.le)
    · exact hAV q (right_mem_Icc.mpr hpq.le)
  have hDF : HasRelativeDefectFilling D V := signed_diagonal_filling hpq hV hAV
  have hP1 : planeDefectInterpolation F D 1 = D := by
    funext x
    simp [planeDefectInterpolation]
  have hP0 : planeDefectInterpolation F D 0 = F := by
    funext x
    simp [planeDefectInterpolation]
  have hL1 : linearDefectHomotopy G p q 1 = F := by
    funext x
    simp [linearDefectHomotopy,F]
  have hL0 : linearDefectHomotopy G p q 0 = G := by
    funext x
    simp [linearDefectHomotopy]
  have hFfill : HasRelativeDefectFilling F V := by
    have h := relativeDefectFilling_homotopy (planeDefectInterpolation_smooth hF hD) hV hZ hZV
      (fun s hs x hx hnot he => hnot (by
        have hz := (hz₂ s hs x hx.2).mp he
        simpa only [Z,mem_insert_iff,mem_singleton_iff] using hz))
      (by rw [hP1]; exact hDF)
    rwa [hP0] at h
  have hGfill : HasRelativeDefectFilling G V := by
    have h := relativeDefectFilling_homotopy (linearDefectHomotopy_smooth hG p q) hV hZ hZV
      (fun s hs x hx hnot he => hnot (by
        have hz := (hz₁ s hs x hx.1.2).mp he
        simpa only [Z,mem_insert_iff,mem_singleton_iff] using hz))
      (by rw [hL1]; exact hFfill)
    rwa [hL0] at h
  exact ⟨V,hV,fun _ hx => hx.1.1,hAV,hGfill⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapFormalPair
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact formal differential is constructed from the actual map and
its crosscap strip. All exterior derivatives remain exact. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

theorem CrosscapCoordinateStrip.formal_pair_oai (S : CrosscapCoordinateStrip A)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    ∃ (V : Set Base) (B : Base → Base →L[ℝ] ProjectionTarget 3) (K : Set Base),
      IsOpen V ∧ V ⊆ S.domain ∧
      (∀ t ∈ Icc A.arc.start A.arc.finish, crosscapAxis t ∈ V) ∧
      ContDiff ℝ ∞ B ∧ IsCompact K ∧ K ⊆ V ∧ tsupport (B-fderiv ℝ S.model) ⊆ K ∧
      (∀ x ∈ V, Function.Injective (B x)) ∧
      ∀ x ∈ V, Function.Injective (fderiv ℝ S.model x) ↔
        x ≠ crosscapAxis A.arc.start ∧ x ≠ crosscapAxis A.arc.finish := by
  obtain ⟨a,d,r,O,hd,hr,hO,hOD,hrect,hN,haxis,hzeros,hIp,hIq,_hvp,_hvq,hdn,hOF⟩ :=
    S.normalized_defect_rectangle_framed hf
  let N := axisNormalizedDefect d (normalDefect S.model a)
  have hAO : ∀ t ∈ Icc A.arc.start A.arc.finish, crosscapAxis t ∈ O := by
    intro t ht
    rw [crosscapAxis_apply]
    exact hrect 0 ⟨by linarith,by linarith⟩ t ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hK : IsCompact (crosscapAxis '' Icc A.arc.start A.arc.finish) :=
    isCompact_Icc.image crosscapAxis.continuous
  obtain ⟨W,hW,hKW,hWO,G,hG,hGW⟩ := CollarVelocity.compact_smooth_extension hK hO
    (by rintro x ⟨t,ht,rfl⟩; exact hAO t ht) hN
  have hAW : ∀ t ∈ Icc A.arc.start A.arc.finish, crosscapAxis t ∈ W :=
    fun t ht => hKW ⟨t,ht,rfl⟩
  have hDG : ∀ x ∈ W, fderiv ℝ G x = fderiv ℝ N x :=
    fun x hx => (hGW.eventuallyEq_of_mem (hW.mem_nhds hx)).fderiv_eq
  have hIpG : Function.Bijective (fderiv ℝ G (crosscapAxis A.arc.start)) := by
    rw [hDG _ (hAW _ (left_mem_Icc.mpr A.arc.start_lt_finish.le))]
    exact hIp
  have hIqG : Function.Bijective (fderiv ℝ G (crosscapAxis A.arc.finish)) := by
    rw [hDG _ (hAW _ (right_mem_Icc.mpr A.arc.start_lt_finish.le))]
    exact hIq
  obtain ⟨V,hV,hVW,hAV,hfill⟩ := normalized_pair_frame_filling hG A.arc.start_lt_finish
    (hW.preimage crosscapAxis.continuous) hAW
    (fun t ht => (hGW ht).trans (haxis t (hWO ht))) hIpG hIqG hW hAW
  have hVO : V ⊆ O := hVW.trans hWO
  obtain ⟨B,K,hB,hK,hKV,hBs,hBI⟩ := actual_relative_frame S.model_smooth a hd hV
    (hVO.trans hOF) (fun x hx => hdn x (hVO hx)) (hGW.mono hVW) hfill
  refine ⟨V,B,K,hV,hVO.trans hOD,hAV,hB,hK,hKV,hBs,hBI,?_⟩
  intro x hx
  have hF := hOF (hVO hx)
  have hbase := normalDefect_immersion_iff S.model a x (normalFrameDomain_nonzero hF)
    (normalFrameDomain_transverse hF)
  have he : N x = 0 ↔ normalDefect S.model a x = 0 := by
    change (planeComplexFrame (d (x 1))).inverse (normalDefect S.model a x) = 0 ↔ _
    constructor
    · intro he
      exact (planeComplexFrame_invertible (hdn x (hVO hx))).inverse.injective
        (he.trans (map_zero _).symm)
    · intro he
      rw [he,map_zero]
  exact hbase.trans ((not_congr he).symm.trans ((not_congr (hzeros x (hVO hx))).trans not_or))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.formal_pair_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.formal_pair_oai.{u_1}
