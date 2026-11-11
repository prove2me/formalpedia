-- Prove2me | solution 1 for OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T18:10:40.897213+00:00
-- url     : https://prove2.me/submissions/b751bec4-ecd2-472f-8bc8-697c0fd061cb

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.List.Count
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Countable
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Encodable.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Order.Interval.Set.Pi
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Closure
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_IsometricImmersion
import Definitions.Def_Q226II019

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_FiniteHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SmoothLocal

theorem det_two_smul (B : Matrix (Fin 2) (Fin 2) ℝ) (ν : ℝ) :
    (ν • B).det = ν ^ 2 * B.det := by
  simp

section Inner
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem normal_tangent_identity (e n : V) (hn : inner ℝ n n = 1) :
    inner ℝ (e - (inner ℝ n e) • n) (e - (inner ℝ n e) • n) +
      (inner ℝ n e) ^ 2 = inner ℝ e e := by
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hn]
  rw [real_inner_comm e n]
  ring

end Inner
end SmoothLocal

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_CoordinateDerivatives
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators
open Filter

namespace SmoothLocal.Geometry

section Height
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {F : Coord → V} {p : Coord} {U : Set Coord}

theorem partial_height (hF : DifferentiableAt ℝ F p) (e : V) (i : Fin 2) :
    coordPartial i (fun q => inner ℝ (F q) e) p = inner ℝ (coordPartial i F p) e := by
  simpa [coordPartial] using
    (fderiv_inner_apply ℝ hF (differentiableAt_const (c := e)) (Pi.single i 1))

theorem second_partial_height (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hp : p ∈ U) (e : V) (i j : Fin 2) :
    coordPartial i (coordPartial j (fun q => inner ℝ (F q) e)) p =
      inner ℝ (coordPartial i (coordPartial j F) p) e := by
  have hlocal : coordPartial j (fun q => inner ℝ (F q) e) =ᶠ[𝓝 p]
      (fun q => inner ℝ (coordPartial j F q) e) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact partial_height
      (((hF q hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) e j
  have hd : DifferentiableAt ℝ (coordPartial j F) p :=
    (((partial_contDiffOn hF hU j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  change fderiv ℝ (coordPartial j (fun q => inner ℝ (F q) e)) p (Pi.single i 1) = _
  rw [hlocal.fderiv_eq]
  exact partial_height hd e i

theorem height_differential_zero (hF : DifferentiableAt ℝ F p) (e : V)
    (he : ∀ v, inner ℝ (fderiv ℝ F p v) e = 0) :
    fderiv ℝ (fun q => inner ℝ (F q) e) p = 0 := by
  ext v
  simpa [he v] using
    (fderiv_inner_apply ℝ hF (differentiableAt_const (c := e)) v)

theorem hessian_height_eq_residual_inner (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hp : p ∈ U) (e : V) (Γ : Fin 2 → Fin 2 → Fin 2 → ℝ) (i j : Fin 2) :
    coordPartial i (coordPartial j (fun q => inner ℝ (F q) e)) p -
      ∑ k, Γ k i j * coordPartial k (fun q => inner ℝ (F q) e) p =
    inner ℝ (coordPartial i (coordPartial j F) p - ∑ k, Γ k i j • coordPartial k F p) e := by
  have hd : DifferentiableAt ℝ F p :=
    ((hF p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  simp only [second_partial_height hF hU hp, partial_height hd,
    inner_sub_left, sum_inner, real_inner_smul_left]

end Height
end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metric
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix ContDiff
namespace SmoothLocal.Geometry

theorem isometricOn_injective_differential {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    {p : Coord} (hp : p ∈ U) : Function.Injective (fderiv ℝ F p) := by
  intro v w hvw
  have hL : fderiv ℝ F p (v - w) = 0 := by simp [map_sub, hvw]
  have hv : v - w = 0 := by
    by_contra hne
    have hpos := (hg.2 p hp).dotProduct_mulVec_pos hne
    have heq := hF.2 p hp (v - w) (v - w)
    rw [hL, inner_zero_left] at heq
    have hpos' : 0 < (v - w) ⬝ᵥ (g p *ᵥ (v - w)) := by simpa using hpos
    exact (ne_of_gt hpos') heq.symm
  exact sub_eq_zero.mp hv

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_ActualHeight
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff BigOperators
namespace SmoothLocal.Geometry

theorem height_smooth {F : Coord → Ambient} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (e : Ambient) :
    ContDiffOn ℝ ∞ (height F e) U :=
  hF.inner ℝ contDiffOn_const

theorem height_derivative_at_normal {F : Coord → Ambient} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    {e : Ambient} (he : IsUnitNormalAt F e p) :
    fderiv ℝ (height F e) p = 0 := by
  exact height_differential_zero
    (((hF p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) e he.2

theorem covHessian_height_at_normal (g : MetricField) {F : Coord → Ambient}
    {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) {e : Ambient} (he : IsUnitNormalAt F e p) :
    covHessian g (height F e) p = secondFundamental F e p := by
  have hz : ∀ k, coordPartial k (height F e) p = 0 := by
    intro k
    simp only [coordPartial, height_derivative_at_normal hF hU hp he,
      zero_apply]
  ext i j
  simp only [covHessian, hz, mul_zero, Finset.sum_const_zero, sub_zero,
    secondFundamental]
  exact second_partial_height hF hU hp e i j

theorem covHessian_height_eq_residual (g : MetricField) {F : Coord → Ambient}
    {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (e : Ambient) (i j : Fin 2) :
    covHessian g (height F e) p i j = inner ℝ (normalResidual g F p i j) e := by
  exact hessian_height_eq_residual_inner hF hU hp e (fun k i j => christoffel g k i j p) i j

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_InducedMetric
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter
namespace SmoothLocal.Geometry

theorem inducedMetric_eq_of_isometric {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hF : IsometricOn g F U) {p : Coord} (hp : p ∈ U) :
    inducedMetric F p = g p := by
  ext i j
  simpa [inducedMetric, coordPartial, Matrix.mulVec_single_one,
    dotProduct, Pi.single_apply] using hF.2 p hp (Pi.single i 1) (Pi.single j 1)

theorem metric_partial_eq {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j k : Fin 2) :
    coordPartial k (fun q => g q i j) p =
      inner ℝ (coordPartial k (coordPartial i F) p) (coordPartial j F p) +
      inner ℝ (coordPartial i F p) (coordPartial k (coordPartial j F) p) := by
  have hl : (fun q => g q i j) =ᶠ[𝓝 p] (fun q => inducedMetric F q i j) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact congrFun (congrFun (inducedMetric_eq_of_isometric hF hq).symm i) j
  have hd (l : Fin 2) : DifferentiableAt ℝ (coordPartial l F) p :=
    (((partial_contDiffOn hF.1 hU l) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  unfold coordPartial
  rw [hl.fderiv_eq]
  change fderiv ℝ (fun q => inner ℝ (coordPartial i F q) (coordPartial j F q)) p
    (Pi.single k 1) = _
  rw [fderiv_inner_apply ℝ (hd i) (hd j)]
  change inner ℝ (coordPartial i F p) (coordPartial k (coordPartial j F) p) +
    inner ℝ (coordPartial k (coordPartial i F) p) (coordPartial j F p) = _
  exact add_comm _ _

theorem second_partial_inner_tangent {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j l : Fin 2) :
    inner ℝ (coordPartial i (coordPartial j F) p) (coordPartial l F p) =
      (coordPartial i (fun q => g q j l) p +
        coordPartial j (fun q => g q i l) p -
        coordPartial l (fun q => g q i j) p) / 2 := by
  rw [metric_partial_eq hF hU hp, metric_partial_eq hF hU hp,
    metric_partial_eq hF hU hp]
  rw [coordPartial_comm hF.1 hU hp j i,
    coordPartial_comm hF.1 hU hp l i, coordPartial_comm hF.1 hU hp l j]
  rw [real_inner_comm (coordPartial j F p) (coordPartial i (coordPartial l F) p)]
  ring

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_GaussConnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff BigOperators Matrix
namespace SmoothLocal.Geometry

theorem normalResidual_orthogonal_tangent {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (i j l : Fin 2) :
    inner ℝ (normalResidual g F p i j) (coordPartial l F p) = 0 := by
  have hind (a b : Fin 2) :
      inner ℝ (coordPartial a F p) (coordPartial b F p) = g p b a := by
    rw [real_inner_comm (coordPartial b F p) (coordPartial a F p)]
    exact congrFun (congrFun (inducedMetric_eq_of_isometric hF hp) b) a
  have hc := congrFun (metric_mul_christoffel hg hp i j) l
  have hc' : ∑ k, christoffel g k i j p * g p l k = christoffelFirstKind g i j p l := by
    simpa only [Matrix.mulVec, dotProduct, mul_comm] using hc
  simp only [normalResidual, inner_sub_left, sum_inner, real_inner_smul_left, hind]
  rw [hc', second_partial_inner_tangent hF hU hp]
  exact sub_self _

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_NormalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Matrix

namespace SmoothLocal.Geometry

theorem mem_orthogonal_span_range_of_inner_eq_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} (t : ι → V) (w : V) (hw : ∀ i, inner ℝ (t i) w = 0) :
    w ∈ (Submodule.span ℝ (Set.range t))ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro x ⟨i, rfl⟩
    exact hw i
  · simp
  · intro a b ha hb hia hib
    simp only [inner_add_left, hia, hib, add_zero]
  · intro c a ha hia
    simp only [real_inner_smul_left, hia, mul_zero]

theorem normalSpace_finrank
    (t : Fin 2 → EuclideanSpace ℝ (Fin 3)) (ht : LinearIndependent ℝ t) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range t))ᗮ = 1 := by
  apply Submodule.finrank_add_finrank_orthogonal'
  simp [finrank_span_eq_card ht]

theorem exists_unit_normal_of_independent_tangents
    (t : Fin 2 → EuclideanSpace ℝ (Fin 3)) (ht : LinearIndependent ℝ t) :
    ∃ n : EuclideanSpace ℝ (Fin 3),
      inner ℝ n n = 1 ∧ ∀ i, inner ℝ (t i) n = 0 := by
  let T := Submodule.span ℝ (Set.range t)
  have hdim : Module.finrank ℝ Tᗮ = 1 := normalSpace_finrank t ht
  have hbot : Tᗮ ≠ ⊥ := by
    intro heq
    have hzero : Module.finrank ℝ Tᗮ = 0 := by rw [heq, finrank_bot]
    exact Nat.zero_ne_one (hzero.symm.trans hdim)
  obtain ⟨n, hnT, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨‖n‖⁻¹ • n, ?_, ?_⟩
  · have hnorm : ‖(‖n‖⁻¹ : ℝ) • n‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hn0
    rw [real_inner_self_eq_norm_sq, hnorm, one_pow]
  · intro i
    rw [real_inner_smul_right]
    have hi : t i ∈ T := Submodule.subset_span (Set.mem_range_self i)
    rw [Submodule.inner_right_of_mem_orthogonal hi hnT, mul_zero]

theorem normal_eq_inner_smul_of_independent_tangents
    (t : Fin 2 → EuclideanSpace ℝ (Fin 3)) (ht : LinearIndependent ℝ t)
    (n w : EuclideanSpace ℝ (Fin 3)) (hn : inner ℝ n n = 1)
    (hnt : ∀ i, inner ℝ (t i) n = 0)
    (hwt : ∀ i, inner ℝ (t i) w = 0) :
    w = (inner ℝ n w) • n := by
  let T := Submodule.span ℝ (Set.range t)
  have hnT : n ∈ Tᗮ := mem_orthogonal_span_range_of_inner_eq_zero t n hnt
  have hwT : w ∈ Tᗮ := mem_orthogonal_span_range_of_inner_eq_zero t w hwt
  have hn0 : n ≠ 0 := by
    intro heq
    simp [heq] at hn
  have hdim : Module.finrank ℝ Tᗮ = 1 := normalSpace_finrank t ht
  have hspan : Tᗮ = ℝ ∙ n :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim hnT hn0
  rw [hspan] at hwT
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwT
  rw [← hc, real_inner_smul_right, hn, mul_one]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_GaussFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff BigOperators
namespace SmoothLocal.Geometry

theorem isometric_tangents_independent {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    {p : Coord} (hp : p ∈ U) : LinearIndependent ℝ (fun i => coordPartial i F p) := by
  simpa only [Function.comp_def, Pi.basisFun_apply, coordPartial,
    ContinuousLinearMap.coe_coe] using
    (Pi.basisFun ℝ (Fin 2)).linearIndependent.map' (fderiv ℝ F p).toLinearMap
      (LinearMap.ker_eq_bot_of_injective (isometricOn_injective_differential hg hF hp))

theorem normalResidual_eq_secondFundamental_smul {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) {n : Ambient}
    (hn : IsUnitNormalAt F n p) (i j : Fin 2) :
    normalResidual g F p i j = secondFundamental F n p i j • n := by
  have hnt (k : Fin 2) : inner ℝ (coordPartial k F p) n = 0 := hn.2 _
  have hwt (k : Fin 2) : inner ℝ (coordPartial k F p) (normalResidual g F p i j) = 0 := by
    rw [real_inner_comm]
    exact normalResidual_orthogonal_tangent hg hF hU hp i j k
  have hline := normal_eq_inner_smul_of_independent_tangents
    (fun k => coordPartial k F p) (isometric_tangents_independent hg hF hp)
    n (normalResidual g F p i j) hn.1 hnt hwt
  have hcoef : inner ℝ n (normalResidual g F p i j) = secondFundamental F n p i j := by
    rw [real_inner_comm]
    simp only [normalResidual, inner_sub_left, sum_inner, real_inner_smul_left,
      hnt, mul_zero, Finset.sum_const_zero, sub_zero, secondFundamental]
  rw [hcoef] at hline
  exact hline

theorem covHessian_height_eq_normal_mul_secondFundamental
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) {n : Ambient} (hn : IsUnitNormalAt F n p) (e : Ambient) :
    covHessian g (height F e) p = (inner ℝ n e) • secondFundamental F n p := by
  ext i j
  rw [covHessian_height_eq_residual g hF.1 hU hp,
    normalResidual_eq_secondFundamental_smul hg hF hU hp hn,
    real_inner_smul_left]
  change secondFundamental F n p i j * inner ℝ n e =
    inner ℝ n e * secondFundamental F n p i j
  exact mul_comm _ _

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_NormalField
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open WithLp

namespace SmoothLocal.Geometry

theorem ambientCross_inner_left (u v : Ambient) : inner ℝ u (ambientCross u v) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change crossProduct (ofLp u) (ofLp v) ⬝ᵥ star (ofLp u) = 0
  rw [star_trivial, dotProduct_comm, dot_self_cross]

theorem ambientCross_inner_right (u v : Ambient) : inner ℝ v (ambientCross u v) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change crossProduct (ofLp u) (ofLp v) ⬝ᵥ star (ofLp v) = 0
  rw [star_trivial, dotProduct_comm, dot_cross_self]

theorem ambientCross_ne_zero_of_independent (t : Fin 2 → Ambient)
    (ht : LinearIndependent ℝ t) : ambientCross (t 0) (t 1) ≠ 0 := by
  let e : Ambient ≃ₗ[ℝ] (Fin 3 → ℝ) := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  have hm : LinearIndependent ℝ (fun i => e (t i)) := by
    exact ht.map' e.toLinearMap (LinearMap.ker_eq_bot_of_injective e.injective)
  have heq : (fun i => e (t i)) = ![ofLp (t 0), ofLp (t 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [heq] at hm
  have hc := crossProduct_ne_zero_iff_linearIndependent.mpr hm
  simpa only [ambientCross, ne_eq, WithLp.toLp_eq_zero] using hc

theorem ambientCross_contDiffOn {a b : Coord → Ambient} {U : Set Coord}
    (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) :
    ContDiffOn ℝ ∞ (fun p => ambientCross (a p) (b p)) U := by
  have ha' := (contDiffOn_piLp 2).mp ha
  have hb' := (contDiffOn_piLp 2).mp hb
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiffOn ℝ ∞ (fun p => a p 1 * b p 2 - a p 2 * b p 1) U
    exact ((ha' 1).mul (hb' 2)).sub ((ha' 2).mul (hb' 1))
  · change ContDiffOn ℝ ∞ (fun p => a p 2 * b p 0 - a p 0 * b p 2) U
    exact ((ha' 2).mul (hb' 0)).sub ((ha' 0).mul (hb' 2))
  · change ContDiffOn ℝ ∞ (fun p => a p 0 * b p 1 - a p 1 * b p 0) U
    exact ((ha' 0).mul (hb' 1)).sub ((ha' 1).mul (hb' 0))

variable {g : MetricField} {F : Coord → Ambient} {U : Set Coord} {p : Coord}

theorem tangentCross_ne_zero (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hp : p ∈ U) : tangentCross F p ≠ 0 :=
  ambientCross_ne_zero_of_independent (fun i => coordPartial i F p)
    (isometric_tangents_independent hg hF hp)

theorem tangentCross_contDiffOn (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (tangentCross F) U :=
  ambientCross_contDiffOn (partial_contDiffOn hF hU 0) (partial_contDiffOn hF hU 1)

theorem unitNormalField_norm (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hp : p ∈ U) : ‖unitNormalField F p‖ = 1 :=
  norm_smul_inv_norm (𝕜 := ℝ) (tangentCross_ne_zero hg hF hp)

theorem unitNormalField_inner_self (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hp : p ∈ U) : inner ℝ (unitNormalField F p) (unitNormalField F p) = 1 := by
  rw [real_inner_self_eq_norm_sq, unitNormalField_norm hg hF hp, one_pow]

theorem unitNormalField_inner_coordPartial (F : Coord → Ambient) (p : Coord) (i : Fin 2) :
    inner ℝ (coordPartial i F p) (unitNormalField F p) = 0 := by
  fin_cases i
  · rw [unitNormalField, real_inner_smul_right]
    change ‖tangentCross F p‖⁻¹ *
      inner ℝ (coordPartial 0 F p) (ambientCross (coordPartial 0 F p) (coordPartial 1 F p)) = 0
    rw [ambientCross_inner_left, mul_zero]
  · rw [unitNormalField, real_inner_smul_right]
    change ‖tangentCross F p‖⁻¹ *
      inner ℝ (coordPartial 1 F p) (ambientCross (coordPartial 0 F p) (coordPartial 1 F p)) = 0
    rw [ambientCross_inner_right, mul_zero]

theorem unitNormalField_isUnitNormalAt (hg : SmoothPositiveOn g U)
    (hF : IsometricOn g F U) (hp : p ∈ U) :
    IsUnitNormalAt F (unitNormalField F p) p := by
  refine ⟨unitNormalField_inner_self hg hF hp, ?_⟩
  intro v
  rw [← Finset.univ_sum_single v, map_sum, sum_inner]
  apply Finset.sum_eq_zero
  intro i _
  have hsingle : Pi.single i (v i) = v i • Pi.single i (1 : ℝ) := by
    ext j
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hsingle, map_smul, real_inner_smul_left]
  change v i * inner ℝ (coordPartial i F p) (unitNormalField F p) = 0
  rw [unitNormalField_inner_coordPartial, mul_zero]

theorem unitNormalField_contDiffOn (hg : SmoothPositiveOn g U)
    (hF : IsometricOn g F U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (unitNormalField F) U := by
  have hc := tangentCross_contDiffOn hF.1 hU
  have hn := hc.norm ℝ (fun p hp => tangentCross_ne_zero hg hF hp)
  exact (hn.inv (fun p hp => norm_ne_zero_iff.mpr (tangentCross_ne_zero hg hF hp))).smul hc

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_NormalDerivative
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

variable {g : MetricField} {F n : Coord → Ambient} {U : Set Coord} {p : Coord}

theorem normalField_derivative_inner_self (hn : ContDiffOn ℝ ∞ n U)
    (hunit : ∀ q ∈ U, inner ℝ (n q) (n q) = 1)
    (hU : IsOpen U) (hp : p ∈ U) (i : Fin 2) :
    inner ℝ (coordPartial i n p) (n p) = 0 := by
  have hd : DifferentiableAt ℝ n p :=
    (((hn p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have heq : (fun q => inner ℝ (n q) (n q)) =ᶠ[𝓝 p]
      (fun _ : Coord => (1 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hunit q hq
  have heq' := congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single i 1)) heq.fderiv_eq
  rw [fderiv_inner_apply ℝ hd hd] at heq'
  simp only [fderiv_const_apply, zero_apply] at heq'
  change inner ℝ (n p) (coordPartial i n p) +
    inner ℝ (coordPartial i n p) (n p) = 0 at heq'
  rw [← real_inner_comm (n p) (coordPartial i n p)] at heq'
  linarith

theorem normalField_derivative_inner_tangent (hF : ContDiffOn ℝ ∞ F U)
    (hn : ContDiffOn ℝ ∞ n U) (hnormal : ∀ q ∈ U, IsUnitNormalAt F (n q) q)
    (hU : IsOpen U) (hp : p ∈ U) (i j : Fin 2) :
    inner ℝ (coordPartial i n p) (coordPartial j F p) =
      -secondFundamental F (n p) p i j := by
  have hdN : DifferentiableAt ℝ n p :=
    (((hn p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hdT : DifferentiableAt ℝ (coordPartial j F) p :=
    ((((partial_contDiffOn hF hU j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have heq : (fun q => inner ℝ (n q) (coordPartial j F q)) =ᶠ[𝓝 p]
      (fun _ : Coord => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    rw [real_inner_comm]
    exact (hnormal q hq).2 (Pi.single j 1)
  have heq' := congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single i 1)) heq.fderiv_eq
  rw [fderiv_inner_apply ℝ hdN hdT] at heq'
  simp only [fderiv_const_apply, zero_apply] at heq'
  change inner ℝ (n p) (coordPartial i (coordPartial j F) p) +
    inner ℝ (coordPartial i n p) (coordPartial j F p) = 0 at heq'
  rw [← real_inner_comm (n p) (coordPartial i (coordPartial j F) p)] at heq'
  change secondFundamental F (n p) p i j +
    inner ℝ (coordPartial i n p) (coordPartial j F p) = 0 at heq'
  linarith

theorem coordPartial_normalField_eq_zero_of_secondFundamental_eq_zero
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hn : ContDiffOn ℝ ∞ n U) (hnormal : ∀ q ∈ U, IsUnitNormalAt F (n q) q)
    (hU : IsOpen U) (hp : p ∈ U)
    (hII : secondFundamental F (n p) p = 0) (i : Fin 2) :
    coordPartial i n p = 0 := by
  have hnt (j : Fin 2) : inner ℝ (coordPartial j F p) (n p) = 0 :=
    (hnormal p hp).2 (Pi.single j 1)
  have hwt (j : Fin 2) : inner ℝ (coordPartial j F p) (coordPartial i n p) = 0 := by
    rw [real_inner_comm, normalField_derivative_inner_tangent hF.1 hn hnormal hU hp i j]
    rw [hII]
    simp
  have hnw : inner ℝ (n p) (coordPartial i n p) = 0 := by
    rw [real_inner_comm]
    exact normalField_derivative_inner_self hn (fun q hq => (hnormal q hq).1) hU hp i
  have hspan := normal_eq_inner_smul_of_independent_tangents
    (fun j => coordPartial j F p) (isometric_tangents_independent hg hF hp)
    (n p) (coordPartial i n p) (hnormal p hp).1 hnt hwt
  simpa only [hnw, zero_smul] using hspan

theorem fderiv_normalField_eq_zero_of_secondFundamental_eq_zero
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hn : ContDiffOn ℝ ∞ n U) (hnormal : ∀ q ∈ U, IsUnitNormalAt F (n q) q)
    (hU : IsOpen U) (hp : p ∈ U)
    (hII : secondFundamental F (n p) p = 0) : fderiv ℝ n p = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [← Finset.univ_sum_single v, map_sum]
  change (∑ i : Fin 2, fderiv ℝ n p (Pi.single i (v i))) = 0
  apply Finset.sum_eq_zero
  intro i _
  have hsingle : Pi.single i (v i) = v i • Pi.single i (1 : ℝ) := by
    simpa only [smul_eq_mul, mul_one] using Pi.single_smul' i (v i) (1 : ℝ)
  rw [hsingle, map_smul]
  change v i • coordPartial i n p = 0
  rw [coordPartial_normalField_eq_zero_of_secondFundamental_eq_zero
    hg hF hn hnormal hU hp hII i, smul_zero]

theorem unitNormalField_fderiv_eq_zero_of_secondFundamental_eq_zero
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hU : IsOpen U) (hp : p ∈ U)
    (hII : secondFundamental F (unitNormalField F p) p = 0) :
    fderiv ℝ (unitNormalField F) p = 0 :=
  fderiv_normalField_eq_zero_of_secondFundamental_eq_zero hg hF
    (unitNormalField_contDiffOn hg hF hU)
    (fun _ hq => unitNormalField_isUnitNormalAt hg hF hq) hU hp hII

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_BoundaryNormal
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

theorem coordinateCircle_hasDerivAt (center : Coord) (radius t : ℝ) :
    HasDerivAt (coordinateCircle center radius) (coordinateCircleVelocity radius t) t := by
  have hpair : HasDerivAt (fun s : ℝ => (![Real.cos s, Real.sin s] : Coord))
      (![-Real.sin t, Real.cos t] : Coord) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · change HasDerivAt Real.cos (-Real.sin t) t
      exact Real.hasDerivAt_cos t
    · change HasDerivAt Real.sin (Real.cos t) t
      exact Real.hasDerivAt_sin t
  change HasDerivAt (fun s : ℝ => center + radius • (![Real.cos s, Real.sin s] : Coord))
    (radius • (![-Real.sin t, Real.cos t] : Coord)) t
  simpa only [Pi.add_def, Pi.smul_def, zero_add] using
    (hasDerivAt_const t center).add (HasDerivAt.const_smul radius hpair)

theorem coordinateCircle_equation (center : Coord) (radius t : ℝ) :
    (coordinateCircle center radius t 0 - center 0) ^ 2 +
      (coordinateCircle center radius t 1 - center 1) ^ 2 = radius ^ 2 := by
  calc
    _ = radius ^ 2 * (Real.cos t ^ 2 + Real.sin t ^ 2) := by
      simp only [coordinateCircle, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    _ = radius ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]

variable {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
variable {center : Coord} {radius : ℝ}

theorem unitNormalField_circle_hasDerivAt_zero
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hcircle : ∀ t, coordinateCircle center radius t ∈ U)
    (hII : ∀ t, secondFundamental F
      (unitNormalField F (coordinateCircle center radius t))
      (coordinateCircle center radius t) = 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unitNormalField F (coordinateCircle center radius s)) 0 t := by
  have hn := unitNormalField_contDiffOn hg hF hU
  have hd : DifferentiableAt ℝ (unitNormalField F) (coordinateCircle center radius t) :=
    (((hn _ (hcircle t)).contDiffAt (hU.mem_nhds (hcircle t))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hzero := unitNormalField_fderiv_eq_zero_of_secondFundamental_eq_zero
    hg hF hU (hcircle t) (hII t)
  simpa only [Function.comp_def, hzero, zero_apply] using
    hd.hasFDerivAt.comp_hasDerivAt t (coordinateCircle_hasDerivAt center radius t)

theorem unitNormalField_circle_constant
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hcircle : ∀ t, coordinateCircle center radius t ∈ U)
    (hII : ∀ t, secondFundamental F
      (unitNormalField F (coordinateCircle center radius t))
      (coordinateCircle center radius t) = 0) (s t : ℝ) :
    unitNormalField F (coordinateCircle center radius s) =
      unitNormalField F (coordinateCircle center radius t) := by
  have hd := unitNormalField_circle_hasDerivAt_zero hg hF hU hcircle hII
  exact is_const_of_deriv_eq_zero (fun a => (hd a).differentiableAt)
    (fun a => (hd a).deriv) s t

theorem height_circle_hasDerivAt_zero
    (hF : IsometricOn g F U) (hU : IsOpen U)
    (hcircle : ∀ t, coordinateCircle center radius t ∈ U) (e : Ambient)
    (he : ∀ t, IsUnitNormalAt F e (coordinateCircle center radius t)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => height F e (coordinateCircle center radius s)) 0 t := by
  have hh := height_smooth hF.1 e
  have hd : DifferentiableAt ℝ (height F e) (coordinateCircle center radius t) :=
    (((hh _ (hcircle t)).contDiffAt (hU.mem_nhds (hcircle t))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hzero := height_derivative_at_normal hF.1 hU (hcircle t) (he t)
  simpa only [Function.comp_def, hzero, zero_apply] using
    hd.hasFDerivAt.comp_hasDerivAt t (coordinateCircle_hasDerivAt center radius t)

theorem height_circle_constant
    (hF : IsometricOn g F U) (hU : IsOpen U)
    (hcircle : ∀ t, coordinateCircle center radius t ∈ U) (e : Ambient)
    (he : ∀ t, IsUnitNormalAt F e (coordinateCircle center radius t)) (s t : ℝ) :
    height F e (coordinateCircle center radius s) =
      height F e (coordinateCircle center radius t) := by
  have hd := height_circle_hasDerivAt_zero hF hU hcircle e he
  exact is_const_of_deriv_eq_zero (fun a => (hd a).differentiableAt)
    (fun a => (hd a).deriv) s t

theorem exists_circle_constant_normal_and_height
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hcircle : ∀ t, coordinateCircle center radius t ∈ U)
    (hII : ∀ t, secondFundamental F
      (unitNormalField F (coordinateCircle center radius t))
      (coordinateCircle center radius t) = 0) :
    ∃ e : Ambient, ∃ c : ℝ, inner ℝ e e = 1 ∧
      (∀ t, unitNormalField F (coordinateCircle center radius t) = e) ∧
      (∀ t, IsUnitNormalAt F e (coordinateCircle center radius t)) ∧
      (∀ t, height F e (coordinateCircle center radius t) = c) := by
  let e := unitNormalField F (coordinateCircle center radius 0)
  have hconst (t : ℝ) : unitNormalField F (coordinateCircle center radius t) = e :=
    unitNormalField_circle_constant hg hF hU hcircle hII t 0
  have he (t : ℝ) : IsUnitNormalAt F e (coordinateCircle center radius t) := by
    rw [← hconst t]
    exact unitNormalField_isUnitNormalAt hg hF (hcircle t)
  refine ⟨e, height F e (coordinateCircle center radius 0), (he 0).1, hconst, he, ?_⟩
  intro t
  exact height_circle_constant hF hU hcircle e he t 0

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_RoundDisk
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Metric

namespace SmoothLocal.Geometry

theorem roundOpenDisk_eq_preimage_ball (center : Coord) {radius : ℝ}
    (hr : 0 ≤ radius) :
    roundOpenDisk center radius = euclideanPlaneCoordinates ⁻¹'
      ball (euclideanPlaneCoordinates center) radius := by
  ext p
  change roundRadiusSq center p < radius ^ 2 ↔
    dist (euclideanPlaneCoordinates p) (euclideanPlaneCoordinates center) < radius
  rw [← euclideanPlaneCoordinates_dist_sq]
  exact sq_lt_sq₀ dist_nonneg hr

theorem interior_roundClosedDisk (center : Coord) {radius : ℝ} (hr : 0 < radius) :
    interior (roundClosedDisk center radius) = roundOpenDisk center radius := by
  rw [roundClosedDisk_eq_preimage_closedBall center hr.le]
  change interior (euclideanPlaneCoordinates.toHomeomorph ⁻¹'
    closedBall (euclideanPlaneCoordinates center) radius) = _
  rw [← euclideanPlaneCoordinates.toHomeomorph.preimage_interior,
    interior_closedBall _ hr.ne']
  exact (roundOpenDisk_eq_preimage_ball center hr.le).symm

theorem center_mem_interior_roundClosedDisk (center : Coord) {radius : ℝ}
    (hr : 0 < radius) : center ∈ interior (roundClosedDisk center radius) := by
  rw [interior_roundClosedDisk center hr]
  simpa [roundOpenDisk, roundRadiusSq] using sq_pos_of_pos hr

theorem interior_roundClosedDisk_nonempty (center : Coord) {radius : ℝ}
    (hr : 0 < radius) : (interior (roundClosedDisk center radius)).Nonempty :=
  ⟨center, center_mem_interior_roundClosedDisk center hr⟩

theorem coordinateCircle_mem_roundClosedDisk (center : Coord) (radius t : ℝ) :
    coordinateCircle center radius t ∈ roundClosedDisk center radius := by
  change roundRadiusSq center (coordinateCircle center radius t) ≤ radius ^ 2
  exact (coordinateCircle_equation center radius t).le

theorem coordinateCircle_mem_frontier_roundClosedDisk (center : Coord) {radius : ℝ}
    (hr : 0 < radius) (t : ℝ) :
    coordinateCircle center radius t ∈ frontier (roundClosedDisk center radius) := by
  rw [mem_frontier_roundClosedDisk_iff center _ hr]
  exact coordinateCircle_equation center radius t

theorem exists_coordinateCircle_of_roundRadiusSq_eq (center p : Coord) {radius : ℝ}
    (hr : 0 < radius) (hp : roundRadiusSq center p = radius ^ 2) :
    ∃ t : ℝ, coordinateCircle center radius t = p := by
  let z : ℂ := ⟨p 0 - center 0, p 1 - center 1⟩
  have hnorm : ‖z‖ = radius := by
    apply (sq_eq_sq₀ (norm_nonneg z) hr.le).mp
    rw [Complex.sq_norm]
    simpa only [Complex.normSq_apply, z, roundRadiusSq, pow_two] using hp
  have hcos : radius * Real.cos z.arg = p 0 - center 0 := by
    simpa only [hnorm, z] using Complex.norm_mul_cos_arg z
  have hsin : radius * Real.sin z.arg = p 1 - center 1 := by
    simpa only [hnorm, z] using Complex.norm_mul_sin_arg z
  refine ⟨z.arg, ?_⟩
  funext i
  fin_cases i
  · change center 0 + radius * Real.cos z.arg = p 0
    linarith
  · change center 1 + radius * Real.sin z.arg = p 1
    linarith

theorem exists_coordinateCircle_of_mem_frontier_roundClosedDisk (center p : Coord)
    {radius : ℝ} (hr : 0 < radius) (hp : p ∈ frontier (roundClosedDisk center radius)) :
    ∃ t : ℝ, coordinateCircle center radius t = p :=
  exists_coordinateCircle_of_roundRadiusSq_eq center p hr
    ((mem_frontier_roundClosedDisk_iff center p hr).mp hp)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_AccumulatingDisks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

theorem accumulatingDisk_subset_square (n : ℕ) : accumulatingDisk n ⊆ square :=
  (accumulatingDisk_subset_enlarged n).trans (enlargedAccumulatingDisk_subset_square n)

theorem tendsto_accumulatingScale : Tendsto accumulatingScale atTop (𝓝 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  convert hpow.mul (tendsto_const_nhds (x := (1 / 2 : ℝ))) using 1 <;>
    first | rfl | simp only [zero_mul]

theorem enlargedAccumulatingDisk_norm_le (n : ℕ) {p : Coord}
    (hp : p ∈ enlargedAccumulatingDisk n) : ‖p‖ ≤ (5 / 4 : ℝ) * accumulatingScale n := by
  have hb := enlargedAccumulatingDisk_bounds n hp
  have hpos := accumulatingScale_pos n
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · change |p 0| ≤ (5 / 4 : ℝ) * accumulatingScale n
    rw [abs_of_nonneg (by linarith : 0 ≤ p 0)]
    exact hb.2.1
  · change |p 1| ≤ (5 / 4 : ℝ) * accumulatingScale n
    linarith [hb.2.2]

theorem eventually_enlargedAccumulatingDisk_subset {V : Set Coord} (hV : V ∈ 𝓝 (0 : Coord)) :
    ∀ᶠ n in atTop, enlargedAccumulatingDisk n ⊆ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  have ht : Tendsto (fun n => (5 / 4 : ℝ) * accumulatingScale n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := (5 / 4 : ℝ))).mul tendsto_accumulatingScale
  filter_upwards [ht.eventually (Iio_mem_nhds hε)] with n hn
  intro p hp
  apply hball
  change dist p (0 : Coord) < ε
  simpa only [dist_zero_right] using lt_of_le_of_lt (enlargedAccumulatingDisk_norm_le n hp) hn

theorem eventually_accumulatingDisk_subset {V : Set Coord} (hV : V ∈ 𝓝 (0 : Coord)) :
    ∀ᶠ n in atTop, accumulatingDisk n ⊆ V :=
  (eventually_enlargedAccumulatingDisk_subset hV).mono
    (fun n hn => (accumulatingDisk_subset_enlarged n).trans hn)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_AffinePullback
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

theorem affinePullbackImmersion_isometric {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hF : IsometricOn g F U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    IsometricOn (affinePullbackMetric g b R) (affinePullbackImmersion F b R)
      (affineCoordinates b R ⁻¹' U) := by
  refine ⟨affine_comp_contDiffOn hF.1 b R, ?_⟩
  intro q hq v w
  have hd : DifferentiableAt ℝ F (affineCoordinates b R q) :=
    (((hF.1 _ hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  change inner ℝ (fderiv ℝ (F ∘ affineCoordinates b R) q v)
    (fderiv ℝ (F ∘ affineCoordinates b R) q w) = _
  rw [fderiv_affine_comp_apply b R q v hd, fderiv_affine_comp_apply b R q w hd,
    hF.2 (affineCoordinates b R q) hq]
  exact matrix_pullback_bilinear (g (affineCoordinates b R q)) R v w

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_DiskCurvatureProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set

namespace SmoothLocal.Geometry

theorem negativeDiskProfile_frontier_zero (c : Coord) {r : ℝ} (hr : 0 < r)
    {p : Coord} (hp : p ∈ frontier (roundClosedDisk c r)) :
    negativeDiskProfile c r p = 0 := by
  have heq := (mem_frontier_roundClosedDisk_iff c p hr).mp hp
  simp only [negativeDiskProfile, heq, sub_self, expNegInvGlue.zero, neg_zero]

theorem accumulatingDiskProfile_neg_interior (n : ℕ) {p : Coord}
    (hp : p ∈ interior (accumulatingDisk n)) : accumulatingDiskProfile n p < 0 := by
  apply negativeDiskProfile_neg_inside
  simpa only [accumulatingDisk,
    interior_roundClosedDisk _ (accumulatingRadius_pos n)] using hp

theorem accumulatingDiskProfile_frontier_zero (n : ℕ) {p : Coord}
    (hp : p ∈ frontier (accumulatingDisk n)) : accumulatingDiskProfile n p = 0 :=
  negativeDiskProfile_frontier_zero _ (accumulatingRadius_pos n) hp

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_AffinePushforward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

theorem affinePushforward_pullback (g : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    affinePushforwardMetric (affinePullbackMetric g b R) b R = g := by
  have hRS := Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  have hT : R⁻¹ᵀ * Rᵀ = 1 := by
    rw [← Matrix.transpose_mul, hRS, Matrix.transpose_one]
  funext p
  simp only [affinePullbackMetric, affinePushforwardMetric,
    affineCoordinates_affineInverseCoordinates b R hR]
  calc
    _ = (R⁻¹ᵀ * Rᵀ) * g p * (R * R⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g p := by rw [hT, hRS, Matrix.one_mul, Matrix.mul_one]

theorem affinePullback_add_pushforward (g η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    affinePullbackMetric (g + affinePushforwardMetric η b R) b R =
      affinePullbackMetric g b R + η := by
  rw [affinePullbackMetric_add, affinePullback_pushforward η b R hR]

theorem affinePushforwardMetric_tsupport_subset (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) {P : Set Coord}
    (hP : tsupport η ⊆ P) :
    tsupport (affinePushforwardMetric η b R) ⊆ affineCoordinates b R '' P := by
  rw [affinePushforwardMetric_tsupport η b R hR]
  exact Set.image_mono hP

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_ExteriorCenterNets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

theorem diskBoundaryNet_cover (n k : ℕ) {p : Coord} (hp : p ∈ frontier (accumulatingDisk n)) :
    ∃ q ∈ diskBoundaryNet n k, dist p q < accumulatingScale k :=
  (Classical.choose_spec (exists_finite_disk_boundary_net n k)).2 p hp

theorem roundClosedDisk_sub_norm_le (c : Coord) {r : ℝ} (hr : 0 ≤ r)
    {p : Coord} (hp : p ∈ roundClosedDisk c r) : ‖p - c‖ ≤ r := by
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro i
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using roundClosedDisk_coord_abs_le c hr hp i

theorem dist_radialLift_self (c p : Coord) (s : ℝ) :
    dist (radialLift c s p) p = |s - 1| * ‖p - c‖ := by
  rw [dist_eq_norm]
  have hv : radialLift c s p - p = (s - 1) • (p - c) := by
    funext i
    simp only [radialLift, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hv, norm_smul, Real.norm_eq_abs]

theorem exteriorMiddleLift_dist_le (n k : ℕ) {p : Coord}
    (hp : p ∈ frontier (accumulatingDisk n)) :
    dist (exteriorMiddleLift n k p) p ≤ accumulatingScale k * accumulatingRadius n := by
  have hdisk : p ∈ accumulatingDisk n := by
    have := (frontier_subset_closure : frontier (accumulatingDisk n) ⊆ closure (accumulatingDisk n)) hp
    simpa only [(accumulatingDisk_isCompact n).isClosed.closure_eq] using this
  have hnorm := roundClosedDisk_sub_norm_le (accumulatingCenter n)
    (accumulatingRadius_pos n).le hdisk
  have ha := accumulatingScale_pos k
  have hr := accumulatingRadius_pos n
  have hcoeff : 0 ≤ 1 + (7 / 8 : ℝ) * accumulatingScale k - 1 := by linarith
  rw [exteriorMiddleLift, dist_radialLift_self, abs_of_nonneg hcoeff]
  have hmul := mul_le_mul_of_nonneg_left hnorm hcoeff
  nlinarith [mul_pos ha hr]

theorem exteriorCenterNet_cover (n k : ℕ) {p : Coord}
    (hp : p ∈ frontier (accumulatingDisk n)) :
    ∃ q ∈ exteriorCenterNet n k,
      dist p q < (1 + accumulatingRadius n) * accumulatingScale k := by
  classical
  obtain ⟨v, hv, hpv⟩ := diskBoundaryNet_cover n k hp
  refine ⟨exteriorMiddleLift n k v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
  have hlift := exteriorMiddleLift_dist_le n k (diskBoundaryNet_mem_frontier n k hv)
  have htri := dist_triangle p v (exteriorMiddleLift n k v)
  rw [dist_comm v (exteriorMiddleLift n k v)] at htri
  nlinarith

theorem every_boundary_point_has_finite_net_sequence (n : ℕ) (p : Coord)
    (hp : p ∈ frontier (accumulatingDisk n)) :
    ∃ centers : ℕ → Coord, (∀ k, centers k ∈ exteriorCenterNet n k) ∧
      Tendsto centers atTop (𝓝 p) := by
  classical
  have hchoose (k : ℕ) : ∃ q ∈ exteriorCenterNet n k,
      dist p q < (1 + accumulatingRadius n) * accumulatingScale k :=
    exteriorCenterNet_cover n k hp
  choose centers hcenters hdist using hchoose
  refine ⟨centers, hcenters, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound (k : ℕ) : dist (centers k) p ≤
      (1 + accumulatingRadius n) * accumulatingScale k := by
    simpa only [dist_comm] using (hdist k).le
  apply squeeze_zero (fun _ => dist_nonneg) hbound
  simpa only [mul_zero] using
    (tendsto_const_nhds (x := 1 + accumulatingRadius n)).mul tendsto_accumulatingScale

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_OrientationNet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Matrix BigOperators
open Set Metric

namespace SmoothLocal.Geometry

theorem orientationAxes_cover (v : PlanarAxis) (hv : ‖v‖ = 1) :
    ∃ a ∈ orientationAxes, dist v a < (1 / 1000 : ℝ) :=
  (Classical.choose_spec exists_finite_unit_axis_net).2 v hv

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_OrientedCenterNets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

theorem orientedLayerIndex_ge_stage (k : ℕ) (R : OrientationLabel) : k ≤ orientedLayerIndex k R :=
  Nat.left_le_pair k (orientationLabelCode R)

theorem orientedLayerIndex_tendsto (R : OrientationLabel) :
    Tendsto (fun k => orientedLayerIndex k R) atTop atTop :=
  tendsto_atTop_mono (fun k => orientedLayerIndex_ge_stage k R) tendsto_id

theorem every_boundary_point_every_orientation_centers (n : ℕ) (p : Coord)
    (hp : p ∈ frontier (accumulatingDisk n)) (R : OrientationLabel) :
    ∃ centers : ℕ → Coord, (∀ k, centers k ∈ orientedExteriorCenters n k R) ∧
      Tendsto centers atTop (𝓝 p) := by
  obtain ⟨centers, hcenters, ht⟩ := every_boundary_point_has_finite_net_sequence n p hp
  exact ⟨fun k => centers (orientedLayerIndex k R),
    fun k => hcenters (orientedLayerIndex k R), ht.comp (orientedLayerIndex_tendsto R)⟩

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_AffinePatchSquares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

theorem closedPatchBox_eq_closedBall : closedPatchBox = Metric.closedBall 0 4 := by
  ext x
  simpa only [Metric.mem_closedBall, dist_zero_right] using mem_closedPatchBox_iff_norm_le x

theorem closedPatchBox_isCompact : IsCompact closedPatchBox := by
  rw [closedPatchBox_eq_closedBall]
  exact isCompact_closedBall 0 4

theorem closedAffineSquare_isCompact (c : Coord) (scale : ℝ)
    (R : Matrix (Fin 2) (Fin 2) ℝ) : IsCompact (closedAffineSquare c scale R) :=
  closedPatchBox_isCompact.image (affineCoordinates_contDiff c (scale • R)).continuous

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_OrientedPatchSquares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

theorem orientedClosedPatch_dist_le (n k : ℕ) (R : OrientationLabel)
    {c : Coord} (hc : c ∈ orientedExteriorCenters n k R)
    {p : Coord} (hp : p ∈ orientedClosedPatch n k R c) :
    dist p c ≤ accumulatingScale k :=
  (Classical.choose_spec (exists_orientedPatchScale n k R)).2.2.2.2 c hc p hp

theorem orientedClosedPatch_isCompact (n k : ℕ) (R : OrientationLabel) (c : Coord) :
    IsCompact (orientedClosedPatch n k R c) :=
  closedAffineSquare_isCompact c (orientedPatchScale n k R) R.val

theorem every_boundary_point_every_orientation_patch_neighborhoods (n : ℕ) (p : Coord)
    (hp : p ∈ frontier (accumulatingDisk n)) (R : OrientationLabel) :
    ∃ centers : ℕ → Coord,
      (∀ k, centers k ∈ orientedExteriorCenters n k R) ∧
      Tendsto centers atTop (𝓝 p) ∧
      ∀ V ∈ 𝓝 p, ∀ᶠ k in atTop, orientedClosedPatch n k R (centers k) ⊆ V := by
  obtain ⟨centers, hcenters, ht⟩ := every_boundary_point_every_orientation_centers n p hp R
  refine ⟨centers, hcenters, ht, ?_⟩
  intro V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hsmall : Tendsto (fun k => accumulatingScale k + dist (centers k) p) atTop (𝓝 0) := by
    simpa only [dist_self, add_zero] using tendsto_accumulatingScale.add
      (ht.dist (tendsto_const_nhds (x := p)))
  filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with k hk
  intro q hq
  apply hball
  exact lt_of_le_of_lt ((dist_triangle q (centers k) p).trans
    (add_le_add (orientedClosedPatch_dist_le n k R (hcenters k) hq) le_rfl)) hk

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_FlatPatchSum
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set

namespace SmoothLocal.Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem flatPatchSum_iteratedFDeriv (f : ℕ → Coord → V) (ε : ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hc : ∀ n, HasCompactSupport (f n))
    (hbound : ∀ n k : ℕ, k ≤ n → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (f n) p‖ ≤ patchSeriesWeight ε n)
    (k : ℕ) (p : Coord) :
    iteratedFDeriv ℝ k (flatPatchSum f) p = ∑' n, iteratedFDeriv ℝ k (f n) p := by
  obtain ⟨v, hv, hfv⟩ := exists_summable_derivative_majorant f ε hf hc hbound
  exact iteratedFDeriv_tsum_apply (N := ⊤) hf (fun k _ => hv k)
    (fun k n p _ => hfv k n p) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p

theorem flatPatchSum_all_jets_zero (f : ℕ → Coord → V) (ε : ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hc : ∀ n, HasCompactSupport (f n))
    (hbound : ∀ n k : ℕ, k ≤ n → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (f n) p‖ ≤ patchSeriesWeight ε n)
    {p : Coord} (hp : ∀ n, p ∉ tsupport (f n)) (k : ℕ) :
    iteratedFDeriv ℝ k (flatPatchSum f) p = 0 := by
  rw [flatPatchSum_iteratedFDeriv f ε hf hc hbound k p]
  have hz (n : ℕ) : iteratedFDeriv ℝ k (f n) p = 0 := by
    by_contra hne
    exact hp n ((support_iteratedFDeriv_subset (𝕜 := ℝ) k) hne)
  simp only [hz, tsum_zero]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_InitialCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter

namespace SmoothLocal.Geometry
open SmoothLocal.Model

theorem initialCurvature_negative_on_disk_interior (n : ℕ) {p : Coord}
    (hp : p ∈ interior (accumulatingDisk n)) : initialCurvature p < 0 := by
  rw [initialCurvature_eq_profile (Sum.inl n) (interior_subset hp)]
  exact mul_neg_of_pos_of_neg (initialCurvatureAmplitudes_pos _)
    (accumulatingDiskProfile_neg_interior n hp)

theorem initialCurvature_zero_on_disk_frontier (n : ℕ) {p : Coord}
    (hp : p ∈ frontier (accumulatingDisk n)) : initialCurvature p = 0 := by
  have hdisk : p ∈ accumulatingDisk n := by
    simpa only [(accumulatingDisk_isCompact n).isClosed.closure_eq] using frontier_subset_closure hp
  rw [initialCurvature_eq_profile (Sum.inl n) hdisk]
  change _ * accumulatingDiskProfile n p = 0
  rw [accumulatingDiskProfile_frontier_zero n hp, mul_zero]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_InitialAssemblyMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set

namespace SmoothLocal.Geometry
open SmoothLocal.ODE SmoothLocal.Model

theorem initialAssemblyMetric_negative_on_disk_interior (n : ℕ) {p : Coord}
    (hp : p ∈ interior (accumulatingDisk n)) : gaussianCurvature initialAssemblyMetric p < 0 := by
  rw [initialAssemblyMetric_gaussianCurvature
    (accumulatingDisk_subset_square n (interior_subset hp))]
  exact initialCurvature_negative_on_disk_interior n hp

theorem initialAssemblyMetric_zero_on_disk_frontier (n : ℕ) {p : Coord}
    (hp : p ∈ frontier (accumulatingDisk n)) : gaussianCurvature initialAssemblyMetric p = 0 := by
  have hdisk : p ∈ accumulatingDisk n := by
    simpa only [(accumulatingDisk_isCompact n).isClosed.closure_eq] using frontier_subset_closure hp
  rw [initialAssemblyMetric_gaussianCurvature (accumulatingDisk_subset_square n hdisk)]
  exact initialCurvature_zero_on_disk_frontier n hp

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open scoped Matrix.Norms.Elementwise
open Filter

namespace SmoothLocal.Geometry

theorem covHessian_eq_of_metric_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (z : Coord → ℝ) : covHessian g z p = covHessian h z p := by
  ext i j
  simp only [covHessian, christoffel_eq_of_eventuallyEq heq]

theorem heightEnergy_eq_of_metric_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (z : Coord → ℝ) : heightEnergy g z p = heightEnergy h z p := by
  simp only [heightEnergy, covectorNormSq, inverseMetric, heq.self_of_nhds]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_MetricTwoJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

theorem inverseMetric_coordPartial_eq_of_firstJet
    {g h : MetricField} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    (hp : p ∈ U) (hval : g p = h p)
    (hfirst : ∀ d i j, coordPartial d (fun q => g q i j) p =
      coordPartial d (fun q => h q i j) p) (d i j : Fin 2) :
    coordPartial d (fun q => inverseMetric g q i j) p =
      coordPartial d (fun q => inverseMetric h q i j) p := by
  have hinv : inverseMetric g p = inverseMetric h p := by simp only [inverseMetric, hval]
  have hvec : g p *ᵥ (fun a => coordPartial d (fun q => inverseMetric g q a j) p) =
      g p *ᵥ (fun a => coordPartial d (fun q => inverseMetric h q a j) p) := by
    ext a
    have hleft := metric_inverse_derivative_identity hg hU hp d a j
    have hright := metric_inverse_derivative_identity hh hU hp d a j
    simp only [hval, hfirst, hinv, Fin.sum_univ_two] at hleft
    simp only [Fin.sum_univ_two] at hright
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hval]
    linarith
  exact congrFun (Matrix.mulVec_injective_of_isUnit (hg.2 p hp).isUnit hvec) i

theorem christoffel_eq_of_firstJet {g h : MetricField} {p : Coord}
    (hval : g p = h p)
    (hfirst : ∀ d i j, coordPartial d (fun q => g q i j) p =
      coordPartial d (fun q => h q i j) p) (k i j : Fin 2) :
    christoffel g k i j p = christoffel h k i j p := by
  simp only [christoffel, inverseMetric, hval, hfirst]

theorem christoffel_coordPartial_eq_of_twoJet
    {g h : MetricField} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    (hp : p ∈ U) (hval : g p = h p)
    (hfirst : ∀ d i j, coordPartial d (fun q => g q i j) p =
      coordPartial d (fun q => h q i j) p)
    (hsecond : ∀ d e i j, coordPartial d (coordPartial e (fun q => g q i j)) p =
      coordPartial d (coordPartial e (fun q => h q i j)) p) (d k i j : Fin 2) :
    coordPartial d (christoffel g k i j) p = coordPartial d (christoffel h k i j) p := by
  have hInvD := inverseMetric_coordPartial_eq_of_firstJet hg hh hU hp hval hfirst
  simp only [inverseMetric] at hInvD
  rw [christoffel_coordPartial_formula hg hU hp d k i j,
    christoffel_coordPartial_formula hh hU hp d k i j]
  simp only [hInvD, hfirst, hsecond, inverseMetric, hval]

theorem gaussianCurvature_eq_of_twoJet
    {g h : MetricField} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    (hp : p ∈ U) (hval : g p = h p)
    (hfirst : ∀ d i j, coordPartial d (fun q => g q i j) p =
      coordPartial d (fun q => h q i j) p)
    (hsecond : ∀ d e i j, coordPartial d (coordPartial e (fun q => g q i j)) p =
      coordPartial d (coordPartial e (fun q => h q i j)) p) :
    gaussianCurvature g p = gaussianCurvature h p := by
  have hΓ := christoffel_eq_of_firstJet hval hfirst
  have hDΓ := christoffel_coordPartial_eq_of_twoJet hg hh hU hp hval hfirst hsecond
  simp only [gaussianCurvature, riemann, hΓ, hDΓ, hval]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_TensorSeriesLocality
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry

namespace TensorJetCalculus

theorem coefficient_contDiff {η : MetricField} (hη : ContDiff ℝ ∞ η) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun p => η p i j) :=
  (coefficient i j).contDiff.comp hη

theorem coefficient_iteratedFDeriv {η : MetricField} (hη : ContDiff ℝ ∞ η)
    (k : ℕ) (p : Coord) (v : Fin k → Coord) (i j : Fin 2) :
    iteratedFDeriv ℝ k (fun q => η q i j) p v =
      (iteratedFDeriv ℝ k η p v) i j := by
  change iteratedFDeriv ℝ k (coefficient i j ∘ η) p v =
    coefficient i j (iteratedFDeriv ℝ k η p v)
  have he := (coefficient i j).iteratedFDeriv_comp_left (x := p) (i := k)
    hη.contDiffAt (WithTop.coe_le_coe.mpr le_top)
  exact congrArg (fun L : Coord [×k]→L[ℝ] ℝ => L v) he

theorem coefficient_coord_word {η : MetricField} (hη : ContDiff ℝ ∞ η)
    (ds : List (Fin 2)) (p : Coord) (i j : Fin 2) :
    iteratedCoordPartial ds (fun q => η q i j) p =
      (iteratedFDeriv ℝ ds.length η p (coordinateDirections ds)) i j := by
  rw [iteratedCoordPartial_eq_jet (coefficient_contDiff hη i j).contDiffOn
    isOpen_univ ds (mem_univ p)]
  exact coefficient_iteratedFDeriv hη ds.length p (coordinateDirections ds) i j

end TensorJetCalculus

theorem tensorPatchSum_contDiff (η : ℕ → MetricField) (ε : ℝ)
    (hη : ∀ j, ContDiff ℝ ∞ (η j)) (hc : ∀ j, HasCompactSupport (η j))
    (hbound : ∀ j k : ℕ, k ≤ j → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (η j) p‖ ≤ patchSeriesWeight ε j) :
    ContDiff ℝ ∞ (tensorPatchSum η) :=
  flatPatchSum_contDiff η ε hη hc hbound

theorem tensorPatchSum_jets_zero_off_each_support
    (η : ℕ → MetricField) (ε : ℝ)
    (hη : ∀ j, ContDiff ℝ ∞ (η j)) (hc : ∀ j, HasCompactSupport (η j))
    (hbound : ∀ j k : ℕ, k ≤ j → ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (η j) p‖ ≤ patchSeriesWeight ε j)
    {p : Coord} (hp : ∀ j, p ∉ tsupport (η j)) (k : ℕ) :
    iteratedFDeriv ℝ k (tensorPatchSum η) p = 0 :=
  flatPatchSum_all_jets_zero η ε hη hc hbound hp k

theorem metric_add_coordinate_jets_eq_of_zero_tensor_jets
    {g τ : MetricField} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hτ : ContDiff ℝ ∞ τ) (hjets : ∀ k : ℕ, iteratedFDeriv ℝ k τ p = 0)
    (ds : List (Fin 2)) (i j : Fin 2) :
    iteratedCoordPartial ds (fun q => (g + τ) q i j) p =
      iteratedCoordPartial ds (fun q => g q i j) p := by
  change iteratedCoordPartial ds (fun q => g q i j + τ q i j) p = _
  rw [CoordinateBound.iterated_add (hg.1 i j)
    (TensorJetCalculus.coefficient_contDiff hτ i j).contDiffOn hU ds hp,
    TensorJetCalculus.coefficient_coord_word hτ ds p i j, hjets ds.length]
  simp

theorem smoothPositive_metric_add_of_tensor_contDiff
    {g τ : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U)
    (hτ : ContDiff ℝ ∞ τ) (hpos : ∀ p ∈ U, ((g + τ) p).PosDef) :
    SmoothPositiveOn (g + τ) U := by
  refine ⟨?_, hpos⟩
  intro i j
  exact (hg.1 i j).add (TensorJetCalculus.coefficient_contDiff hτ i j).contDiffOn

theorem gaussianCurvature_add_eq_of_zero_tensor_jets
    {g τ : MetricField} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hτ : ContDiff ℝ ∞ τ) (hpos : ∀ q ∈ U, ((g + τ) q).PosDef)
    (hjets : ∀ k : ℕ, iteratedFDeriv ℝ k τ p = 0) :
    gaussianCurvature (g + τ) p = gaussianCurvature g p := by
  have hwords := metric_add_coordinate_jets_eq_of_zero_tensor_jets hg hU hp hτ hjets
  apply gaussianCurvature_eq_of_twoJet
    (smoothPositive_metric_add_of_tensor_contDiff hg hτ hpos) hg hU hp
  · ext i j
    exact hwords [] i j
  · intro d i j
    exact hwords [d] i j
  · intro d e i j
    exact hwords [d, e] i j

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_DisjointTensorAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry

theorem tensorPatchSum_eq_single_on_disjoint_carrier
    (η : ℕ → MetricField) (C : ℕ → Set Coord)
    (hsupp : ∀ j, tsupport (η j) ⊆ C j)
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (i : ℕ) {p : Coord} (hp : p ∈ C i) : tensorPatchSum η p = η i p := by
  change (∑' j, η j p) = η i p
  apply tsum_eq_single i
  intro j hji
  by_contra hne
  exact Set.disjoint_left.mp (hdisjoint hji)
    (hsupp j (subset_tsupport (η j) hne)) hp

theorem tensorPatchSum_zero_off_carriers
    (η : ℕ → MetricField) (C : ℕ → Set Coord)
    (hsupp : ∀ j, tsupport (η j) ⊆ C j)
    {p : Coord} (hp : ∀ j, p ∉ C j) : tensorPatchSum η p = 0 := by
  have hz (j : ℕ) : η j p = 0 := by
    by_contra hne
    exact hp j (hsupp j (subset_tsupport (η j) hne))
  change (∑' j, η j p) = 0
  simp only [hz, tsum_zero]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_AffineTensorJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

theorem iteratedFDeriv_comp_affineInverse
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Coord → F} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) {p : Coord}
    (hp : affineInverseCoordinates b R p ∈ U) (n : ℕ) :
    iteratedFDeriv ℝ n (f ∘ affineInverseCoordinates b R) p =
      (iteratedFDeriv ℝ n f (affineInverseCoordinates b R p)).compContinuousLinearMap
        (fun _ : Fin n => matrixContinuousLinear R⁻¹) := by
  let L : Coord →L[ℝ] Coord := matrixContinuousLinear R⁻¹
  change iteratedFDeriv ℝ n (fun x => (f ∘ L) (x-b)) p = _
  rw [iteratedFDeriv_comp_sub]
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn hp
    (i := n) (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDerivWithin_of_isOpen n hpre hp,
    iteratedFDerivWithin_of_isOpen n hU (show L (p-b) ∈ U from hp)] at he
  exact he

theorem iteratedFDeriv_affinePushforwardMetric
    {η : MetricField} {U : Set Coord} (hη : ContDiffOn ℝ ∞ η U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) {p : Coord}
    (hp : affineInverseCoordinates b R p ∈ U) (n : ℕ) :
    iteratedFDeriv ℝ n (affinePushforwardMetric η b R) p =
      (affineTensorCongruence R).compContinuousMultilinearMap
        ((iteratedFDeriv ℝ n η (affineInverseCoordinates b R p)).compContinuousLinearMap
          (fun _ : Fin n => matrixContinuousLinear R⁻¹)) := by
  have hinv := affineInverseCoordinates_contDiff b R
  have hcomp : ContDiffOn ℝ ∞ (η ∘ affineInverseCoordinates b R)
      (affineInverseCoordinates b R ⁻¹' U) :=
    hη.comp hinv.contDiffOn (fun _ hq => hq)
  have hpre := hU.preimage hinv.continuous
  change iteratedFDeriv ℝ n ((affineTensorCongruence R) ∘
    (η ∘ affineInverseCoordinates b R)) p = _
  calc
    _ = (affineTensorCongruence R).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (η ∘ affineInverseCoordinates b R) p) :=
      (affineTensorCongruence R).iteratedFDeriv_comp_left
        (hcomp.contDiffAt (hpre.mem_nhds hp)) (WithTop.coe_le_coe.mpr le_top)
    _ = _ := congrArg (affineTensorCongruence R).compContinuousMultilinearMap
      (iteratedFDeriv_comp_affineInverse hη hU b R hp n)

theorem affineTensorJetFactor_nonneg (R : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) :
    0 ≤ affineTensorJetFactor R n := by
  unfold affineTensorJetFactor
  positivity

theorem norm_iteratedFDeriv_affinePushforwardMetric_le
    {η : MetricField} {U : Set Coord} (hη : ContDiffOn ℝ ∞ η U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) {p : Coord}
    (hp : affineInverseCoordinates b R p ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (affinePushforwardMetric η b R) p‖ ≤
      affineTensorJetFactor R n * ‖iteratedFDeriv ℝ n η (affineInverseCoordinates b R p)‖ := by
  rw [iteratedFDeriv_affinePushforwardMetric hη hU b R hp n]
  have hright := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n η (affineInverseCoordinates b R p))
    (fun _ : Fin n => matrixContinuousLinear R⁻¹)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hright
  calc
    _ ≤ ‖affineTensorCongruence R‖ *
      ‖(iteratedFDeriv ℝ n η (affineInverseCoordinates b R p)).compContinuousLinearMap
        (fun _ : Fin n => matrixContinuousLinear R⁻¹)‖ :=
      (affineTensorCongruence R).norm_compContinuousMultilinearMap_le _
    _ ≤ ‖affineTensorCongruence R‖ *
        (‖iteratedFDeriv ℝ n η (affineInverseCoordinates b R p)‖ *
          ‖matrixContinuousLinear R⁻¹‖^n) :=
      mul_le_mul_of_nonneg_left hright (norm_nonneg _)
    _ = _ := by unfold affineTensorJetFactor; ring

theorem supported_affine_tensor_jet_le_seminorm
    (η : SymmetricPerturbation) (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (n : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ n (affinePushforwardMetric (perturbationTensor η) b R) p‖ ≤
      affineTensorJetFactor R n * perturbationSeminorm n η := by
  exact (norm_iteratedFDeriv_affinePushforwardMetric_le
    (perturbationTensor_contDiff η).contDiffOn isOpen_univ b R (mem_univ _) n).trans
      (mul_le_mul_of_nonneg_left (perturbation_derivative_norm_le η n _)
        (affineTensorJetFactor_nonneg R n))

theorem affineTensorJetFactor_le_orderFactor
    (R : Matrix (Fin 2) (Fin 2) ℝ) {n N : ℕ} (hn : n ≤ N) :
    affineTensorJetFactor R n ≤ affineTensorOrderFactor R N := by
  have hpow : ‖matrixContinuousLinear R⁻¹‖^n ≤ (1+‖matrixContinuousLinear R⁻¹‖)^N :=
    (pow_le_pow_left₀ (norm_nonneg _) (by linarith :
      ‖matrixContinuousLinear R⁻¹‖ ≤ 1+‖matrixContinuousLinear R⁻¹‖) n).trans
        (pow_le_pow_right₀ (by linarith [norm_nonneg (matrixContinuousLinear R⁻¹)]) hn)
  have hmul := mul_le_mul_of_nonneg_left hpow (norm_nonneg (affineTensorCongruence R))
  unfold affineTensorJetFactor affineTensorOrderFactor
  linarith

theorem supported_affine_tensor_finite_jet_le
    (η : SymmetricPerturbation) (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    {n N : ℕ} (hn : n ≤ N) (p : Coord) :
    ‖iteratedFDeriv ℝ n (affinePushforwardMetric (perturbationTensor η) b R) p‖ ≤
      affineTensorOrderFactor R N * perturbationSeminorm n η := by
  have hsemi : 0 ≤ perturbationSeminorm n η :=
    (norm_nonneg _).trans (perturbation_derivative_norm_le η n (0 : Coord))
  exact (supported_affine_tensor_jet_le_seminorm η b R n p).trans
    (mul_le_mul_of_nonneg_right (affineTensorJetFactor_le_orderFactor R hn) hsemi)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_AffineTensorNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

theorem affineTensorJetNeighborhood_physical_bounds
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ) {epsilon : ℝ}
    {η : SymmetricPerturbation} (hη : η ∈ affineTensorJetNeighborhood R N epsilon)
    {k : ℕ} (hk : k ≤ N) (p : Coord) :
    ‖iteratedFDeriv ℝ k (affinePushforwardMetric (perturbationTensor η) b R) p‖ < epsilon := by
  have hsmall := hη ⟨k, Nat.lt_succ_of_le hk⟩
  change perturbationSeminorm k η < epsilon / affineTensorOrderFactor R N at hsmall
  calc
    _ ≤ affineTensorOrderFactor R N * perturbationSeminorm k η :=
      supported_affine_tensor_finite_jet_le η b R hk p
    _ = perturbationSeminorm k η * affineTensorOrderFactor R N := mul_comm _ _
    _ < epsilon := (lt_div_iff₀ (affineTensorOrderFactor_pos R N)).mp hsmall

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_EnumeratedPatchTensors
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

theorem patchTensorAddress_index (a : PatchAddress) :
    patchTensorAddress (patchTensorIndex a) = some a := by
  simp only [patchTensorAddress,patchTensorIndex,Encodable.decode₂_encode]

theorem patchTensorAddress_eq_some_iff {j : ℕ} {a : PatchAddress} :
    patchTensorAddress j = some a ↔ patchTensorIndex a = j := by
  constructor
  · intro h
    cases hd : Encodable.decode₂ AssemblyProfileIndex j with
    | none => simp only [patchTensorAddress,hd] at h; cases h
    | some i =>
      cases i with
      | inl n => simp only [patchTensorAddress,hd] at h; cases h
      | inr b =>
        have hba : b = a := by simpa only [patchTensorAddress,hd,Option.some.injEq] using h
        subst b
        exact Encodable.decode₂_eq_some.mp hd
  · intro h
    rw [← h]
    exact patchTensorAddress_index a

theorem patchAddressTensor_contDiff (eta : PatchAddress → SymmetricPerturbation) (a : PatchAddress) :
    ContDiff ℝ ∞ (patchAddressTensor eta a) :=
  (affineTensorCongruence (patchAddressMatrix a)).contDiff.comp
    ((perturbationTensor_contDiff (eta a)).comp
      (affineInverseCoordinates_contDiff (patchAddressCenter a) (patchAddressMatrix a)))

theorem patchAddressTensor_tsupport_subset (eta : PatchAddress → SymmetricPerturbation)
    (a : PatchAddress) : tsupport (patchAddressTensor eta a) ⊆ patchAddressCarrier a := by
  have hs := affinePushforwardMetric_tsupport_subset (perturbationTensor (eta a))
    (patchAddressCenter a) (patchAddressMatrix a) (patchAddressMatrix_isUnit a)
    (perturbationTensor_tsupport_subset (eta a))
  intro p hp
  obtain ⟨q,hq,rfl⟩ := hs hp
  refine ⟨q,?_,rfl⟩
  intro i
  exact ⟨by linarith [hq.1 i],by linarith [hq.2 i]⟩

theorem patchAddressCarrier_isCompact (a : PatchAddress) : IsCompact (patchAddressCarrier a) :=
  orientedClosedPatch_isCompact a.1 a.2.1 a.2.2.1 a.2.2.2.val

theorem enumeratedPatchTensor_index (eta : PatchAddress → SymmetricPerturbation) (a : PatchAddress) :
    enumeratedPatchTensor eta (patchTensorIndex a) = patchAddressTensor eta a := by
  simp only [enumeratedPatchTensor,patchTensorAddress_index]

theorem enumeratedPatchCarrier_index (a : PatchAddress) :
    enumeratedPatchCarrier (patchTensorIndex a) = patchAddressCarrier a := by
  simp only [enumeratedPatchCarrier,patchTensorAddress_index]

theorem enumeratedPatchTensor_contDiff (eta : PatchAddress → SymmetricPerturbation) (j : ℕ) :
    ContDiff ℝ ∞ (enumeratedPatchTensor eta j) := by
  cases h : patchTensorAddress j with
  | none =>
      simp only [enumeratedPatchTensor,h]
      change ContDiff ℝ ∞ (fun _ : Coord => (0 : Matrix (Fin 2) (Fin 2) ℝ))
      exact contDiff_const
  | some a => simpa only [enumeratedPatchTensor,h] using patchAddressTensor_contDiff eta a

theorem enumeratedPatchCarrier_isCompact (j : ℕ) : IsCompact (enumeratedPatchCarrier j) := by
  cases h : patchTensorAddress j with
  | none => simpa only [enumeratedPatchCarrier,h] using (isCompact_empty : IsCompact (∅ : Set Coord))
  | some a => simpa only [enumeratedPatchCarrier,h] using patchAddressCarrier_isCompact a

theorem enumeratedPatchTensor_tsupport_subset (eta : PatchAddress → SymmetricPerturbation) (j : ℕ) :
    tsupport (enumeratedPatchTensor eta j) ⊆ enumeratedPatchCarrier j := by
  cases h : patchTensorAddress j with
  | none => simp [enumeratedPatchTensor,enumeratedPatchCarrier,h]
  | some a => simpa only [enumeratedPatchTensor,enumeratedPatchCarrier,h] using
      patchAddressTensor_tsupport_subset eta a

theorem enumeratedPatchTensor_hasCompactSupport (eta : PatchAddress → SymmetricPerturbation) (j : ℕ) :
    HasCompactSupport (enumeratedPatchTensor eta j) :=
  (enumeratedPatchCarrier_isCompact j).of_isClosed_subset (isClosed_tsupport _)
    (enumeratedPatchTensor_tsupport_subset eta j)

theorem enumeratedPatchCarriers_pairwise_disjoint :
    Pairwise (fun i j => Disjoint (enumeratedPatchCarrier i) (enumeratedPatchCarrier j)) := by
  intro i j hij
  cases hi : patchTensorAddress i with
  | none => simp [enumeratedPatchCarrier,hi]
  | some a =>
    cases hj : patchTensorAddress j with
    | none => simp [enumeratedPatchCarrier,hj]
    | some b =>
      have hab : a ≠ b := by
        intro h
        subst b
        exact hij ((patchTensorAddress_eq_some_iff.mp hi).symm.trans
          (patchTensorAddress_eq_some_iff.mp hj))
      simpa only [enumeratedPatchCarrier,hi,hj] using patchAddressCarriers_pairwise_disjoint hab

theorem enumeratedPatchCarrier_disjoint_disk (j n : ℕ) :
    Disjoint (enumeratedPatchCarrier j) (accumulatingDisk n) := by
  cases h : patchTensorAddress j with
  | none => simp [enumeratedPatchCarrier,h]
  | some a =>
    simpa only [enumeratedPatchCarrier,h,patchAddressCarrier] using
      orientedClosedPatch_disjoint_every_disk a.1 a.2.1 a.2.2.1 a.2.2.2.property n

theorem enumeratedPatchTensor_diagonal_bound {epsilon : ℝ} (he : 0 < epsilon)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a)
    (j k : ℕ) (hkj : k ≤ j) (p : Coord) :
    ‖iteratedFDeriv ℝ k (enumeratedPatchTensor eta j) p‖ ≤ patchSeriesWeight epsilon j := by
  cases h : patchTensorAddress j with
  | none =>
    simpa only [enumeratedPatchTensor,h,iteratedFDeriv_zero,Pi.zero_apply,norm_zero] using
      (patchSeriesWeight_pos he j).le
  | some a =>
    have ha := patchTensorAddress_eq_some_iff.mp h
    have hb := affineTensorJetNeighborhood_physical_bounds
      (patchAddressCenter a) (patchAddressMatrix a) (patchTensorIndex a) (hsmall a)
        (show k ≤ patchTensorIndex a by omega) p
    simpa only [enumeratedPatchTensor,h,patchAddressTensor,ha] using hb.le

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_PatchTensorRestriction
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

theorem assembledPatchTensor_eq_single (eta : PatchAddress → SymmetricPerturbation)
    (a : PatchAddress) {p : Coord} (hp : p ∈ patchAddressCarrier a) :
    assembledPatchTensor eta p = patchAddressTensor eta a p := by
  have hh := tensorPatchSum_eq_single_on_disjoint_carrier
    (enumeratedPatchTensor eta) enumeratedPatchCarrier
    (enumeratedPatchTensor_tsupport_subset eta) enumeratedPatchCarriers_pairwise_disjoint
    (patchTensorIndex a) (by simpa only [enumeratedPatchCarrier_index] using hp)
  simpa only [assembledPatchTensor,enumeratedPatchTensor_index] using hh

theorem assembledPatchTensor_zero_off_carriers (eta : PatchAddress → SymmetricPerturbation)
    {p : Coord} (hp : ∀ a : PatchAddress, p ∉ patchAddressCarrier a) : assembledPatchTensor eta p = 0 := by
  apply tensorPatchSum_zero_off_carriers (enumeratedPatchTensor eta) enumeratedPatchCarrier
    (enumeratedPatchTensor_tsupport_subset eta)
  intro j
  cases h : patchTensorAddress j with
  | none => simp [enumeratedPatchCarrier,h]
  | some a => simpa only [enumeratedPatchCarrier,h] using hp a

theorem assembledPatchMetric_pullback_eq_on_closedPatchBox
    (g : MetricField) (eta : PatchAddress → SymmetricPerturbation) (a : PatchAddress)
    {q : Coord} (hq : q ∈ closedPatchBox) :
    affinePullbackMetric (assembledPatchMetric g eta) (patchAddressCenter a) (patchAddressMatrix a) q =
      localPatchMetric g eta a q := by
  have hp : affineCoordinates (patchAddressCenter a) (patchAddressMatrix a) q ∈ patchAddressCarrier a :=
    ⟨q,hq,rfl⟩
  calc
    _ = affinePullbackMetric (g + patchAddressTensor eta a)
        (patchAddressCenter a) (patchAddressMatrix a) q := by
      unfold affinePullbackMetric assembledPatchMetric
      simp only [Pi.add_apply,assembledPatchTensor_eq_single eta a hp]
    _ = _ := congrFun (affinePullback_add_pushforward g (perturbationTensor (eta a))
      (patchAddressCenter a) (patchAddressMatrix a) (patchAddressMatrix_isUnit a)) q

theorem assembledPatchTensor_contDiff {epsilon : ℝ} (he : 0 < epsilon)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a) :
    ContDiff ℝ ∞ (assembledPatchTensor eta) :=
  tensorPatchSum_contDiff _ epsilon (enumeratedPatchTensor_contDiff eta)
    (enumeratedPatchTensor_hasCompactSupport eta) (enumeratedPatchTensor_diagonal_bound he eta hsmall)

theorem assembledPatchTensor_all_jets_zero_on_disk {epsilon : ℝ} (he : 0 < epsilon)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a)
    (n : ℕ) {p : Coord} (hp : p ∈ accumulatingDisk n) (k : ℕ) :
    iteratedFDeriv ℝ k (assembledPatchTensor eta) p = 0 := by
  apply tensorPatchSum_jets_zero_off_each_support _ epsilon (enumeratedPatchTensor_contDiff eta)
    (enumeratedPatchTensor_hasCompactSupport eta) (enumeratedPatchTensor_diagonal_bound he eta hsmall)
  intro j hj
  exact Set.disjoint_left.mp (enumeratedPatchCarrier_disjoint_disk j n)
    (enumeratedPatchTensor_tsupport_subset eta j hj) hp

theorem assembledPatchMetric_posDef
    {g : MetricField} {U : Set Coord} (hg : ∀ p ∈ U, (g p).PosDef)
    (eta : PatchAddress → SymmetricPerturbation)
    (hlocal : ∀ a, ∀ p ∈ U ∩ patchAddressCarrier a, ((g + patchAddressTensor eta a) p).PosDef) :
    ∀ p ∈ U, (assembledPatchMetric g eta p).PosDef := by
  intro p hp
  by_cases hex : ∃ a, p ∈ patchAddressCarrier a
  · obtain ⟨a,ha⟩ := hex
    change (g p + assembledPatchTensor eta p).PosDef
    rw [assembledPatchTensor_eq_single eta a ha]
    exact hlocal a p ⟨hp,ha⟩
  · have hout : ∀ a, p ∉ patchAddressCarrier a := fun a ha => hex ⟨a,ha⟩
    change (g p + assembledPatchTensor eta p).PosDef
    rw [assembledPatchTensor_zero_off_carriers eta hout,add_zero]
    exact hg p hp

theorem assembledPatchMetric_smoothPositive {epsilon : ℝ} (he : 0 < epsilon)
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a)
    (hlocal : ∀ a, ∀ p ∈ U ∩ patchAddressCarrier a, ((g + patchAddressTensor eta a) p).PosDef) :
    SmoothPositiveOn (assembledPatchMetric g eta) U :=
  smoothPositive_metric_add_of_tensor_contDiff hg (assembledPatchTensor_contDiff he eta hsmall)
    (assembledPatchMetric_posDef hg.2 eta hlocal)

theorem assembledPatchMetric_curvature_on_disk {epsilon : ℝ} (he : 0 < epsilon)
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a)
    (hlocal : ∀ a, ∀ p ∈ U ∩ patchAddressCarrier a, ((g + patchAddressTensor eta a) p).PosDef)
    (n : ℕ) {p : Coord} (hp : p ∈ accumulatingDisk n) (hpU : p ∈ U) :
    gaussianCurvature (assembledPatchMetric g eta) p = gaussianCurvature g p :=
  gaussianCurvature_add_eq_of_zero_tensor_jets hg hU hpU
    (assembledPatchTensor_contDiff he eta hsmall) (assembledPatchMetric_posDef hg.2 eta hlocal)
    (assembledPatchTensor_all_jets_zero_on_disk he eta hsmall n hp)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_PatchTensorPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

theorem patchAddress_inverse_mulVec_injective (a : PatchAddress) :
    Injective ((patchAddressMatrix a)⁻¹).mulVec := by
  intro v w hvw
  have h := congrArg (fun u : Coord => patchAddressMatrix a *ᵥ u) hvw
  have hR := Matrix.mul_nonsing_inv (patchAddressMatrix a)
    ((Matrix.isUnit_iff_isUnit_det _).mp (patchAddressMatrix_isUnit a))
  simpa only [Matrix.mulVec_mulVec,hR,Matrix.one_mulVec] using h

theorem patchAddress_local_inverse_congruence (g : MetricField)
    (eta : PatchAddress → SymmetricPerturbation) (a : PatchAddress) (p : Coord) :
    (patchAddressMatrix a)⁻¹ᵀ *
      localPatchMetric g eta a (affineInverseCoordinates (patchAddressCenter a) (patchAddressMatrix a) p) *
        (patchAddressMatrix a)⁻¹ = (g + patchAddressTensor eta a) p := by
  have h := congrFun (affinePushforward_pullback g (patchAddressCenter a)
    (patchAddressMatrix a) (patchAddressMatrix_isUnit a)) p
  change (patchAddressMatrix a)⁻¹ᵀ *
      affinePullbackMetric g (patchAddressCenter a) (patchAddressMatrix a)
        (affineInverseCoordinates (patchAddressCenter a) (patchAddressMatrix a) p) *
          (patchAddressMatrix a)⁻¹ = g p at h
  simp only [localPatchMetric,Pi.add_apply,Matrix.mul_add,Matrix.add_mul,h]
  rfl

theorem patchAddress_add_posDef_of_local_metric
    {g : MetricField} {U : Set Coord} (hg : ∀ p ∈ U, (g p).PosDef)
    (eta : PatchAddress → SymmetricPerturbation) (a : PatchAddress)
    (hlocal : ∀ q ∈ modelSquare, (localPatchMetric g eta a q).PosDef)
    {p : Coord} (hp : p ∈ U) : ((g + patchAddressTensor eta a) p).PosDef := by
  let q := affineInverseCoordinates (patchAddressCenter a) (patchAddressMatrix a) p
  by_cases hq : q ∈ patchBox
  · have hpos := (hlocal q (patchBox_subset_modelSquare hq)).conjTranspose_mul_mul_same
      (patchAddress_inverse_mulVec_injective a)
    simpa only [q, Matrix.conjTranspose_eq_transpose_of_trivial,
      patchAddress_local_inverse_congruence] using hpos
  · have hz : perturbationTensor (eta a) q = 0 := perturbationTensor_zero_off_patch (eta a) hq
    have hpzero : patchAddressTensor eta a p = 0 := by
      change (patchAddressMatrix a)⁻¹ᵀ * perturbationTensor (eta a) q * (patchAddressMatrix a)⁻¹ = 0
      rw [hz,Matrix.mul_zero,Matrix.zero_mul]
    change (g p + patchAddressTensor eta a p).PosDef
    rw [hpzero,add_zero]
    exact hg p hp

theorem assembledPatchMetric_smoothPositive_of_local_metrics {epsilon : ℝ} (he : 0 < epsilon)
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a)
    (hlocal : ∀ a, ∀ q ∈ modelSquare, (localPatchMetric g eta a q).PosDef) :
    SmoothPositiveOn (assembledPatchMetric g eta) U :=
  assembledPatchMetric_smoothPositive he hg eta hsmall
    (fun a _ hp => patchAddress_add_posDef_of_local_metric hg.2 eta a (hlocal a) hp.1)

theorem assembledPatchMetric_curvature_on_disk_of_local_metrics {epsilon : ℝ} (he : 0 < epsilon)
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a)
    (hlocal : ∀ a, ∀ q ∈ modelSquare, (localPatchMetric g eta a q).PosDef)
    (n : ℕ) {p : Coord} (hp : p ∈ accumulatingDisk n) (hpU : p ∈ U) :
    gaussianCurvature (assembledPatchMetric g eta) p = gaussianCurvature g p :=
  assembledPatchMetric_curvature_on_disk he hg hU eta hsmall
    (fun a _ hp => patchAddress_add_posDef_of_local_metric hg.2 eta a (hlocal a) hp.1) n hp hpU

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Obstructions_PatchAdmissibilityRestriction
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

theorem PatchAdmissibleHeight.congr_metric_on_open
    {g h : MetricField} {z : Coord → ℝ} (hadm : PatchAdmissibleHeight g z)
    {W : Set Coord} (hW : IsOpen W) (hSW : modelSquare ⊆ W) (heq : EqOn g h W) :
    PatchAdmissibleHeight h z := by
  obtain ⟨U,hU,hSU,hg,hz,hD,hE,hyy,hq⟩ := hadm
  have hevent (p : Coord) (hp : p ∈ modelSquare) : g =ᶠ[𝓝 p] h := by
    filter_upwards [hW.mem_nhds (hSW hp)] with q hq
    exact heq hq
  have hmetric : SmoothPositiveOn h (U ∩ W) := by
    constructor
    · intro i j
      apply ((hg.1 i j).mono inter_subset_left).congr
      intro p hp
      exact congrFun (congrFun (heq hp.2).symm i) j
    · intro p hp
      rw [← heq hp.2]
      exact hg.2 p hp.1
  refine ⟨U ∩ W,hU.inter hW,(fun p hp => ⟨hSU hp,hSW hp⟩),hmetric,
    hz.mono inter_subset_left,?_,?_,?_,?_⟩
  · intro p hp
    rw [← covHessian_eq_of_metric_eventuallyEq (hevent p hp) z,
      ← gaussianCurvature_eq_of_eventuallyEq (hevent p hp),
      ← heightEnergy_eq_of_metric_eventuallyEq (hevent p hp) z]
    exact hD p hp
  · intro p hp
    rw [← heightEnergy_eq_of_metric_eventuallyEq (hevent p hp) z]
    exact hE p hp
  · intro p hp
    rw [← covHessian_eq_of_metric_eventuallyEq (hevent p hp) z]
    exact hyy p hp
  · intro p hp
    unfold hessianQuotient
    rw [← covHessian_eq_of_metric_eventuallyEq (hevent p hp) z]
    exact hq p hp

theorem assembledPatchMetric_admissible_local
    (g : MetricField) (eta : PatchAddress → SymmetricPerturbation) (a : PatchAddress)
    {z : Coord → ℝ}
    (hadm : PatchAdmissibleHeight
      (affinePullbackMetric (assembledPatchMetric g eta) (patchAddressCenter a) (patchAddressMatrix a)) z) :
    PatchAdmissibleHeight (localPatchMetric g eta a) z := by
  apply hadm.congr_metric_on_open Metric.isOpen_ball (W := Metric.ball (0 : Coord) 4)
  · intro p hp
    have hnorm : ‖p‖ ≤ 3 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)).mpr
      intro i
      simpa only [Real.norm_eq_abs] using (abs_le.mpr ⟨hp.1 i,hp.2 i⟩)
    simpa only [Metric.mem_ball,dist_zero_right] using (lt_of_le_of_lt hnorm (by norm_num : (3 : ℝ) < 4))
  · intro p hp
    apply assembledPatchMetric_pullback_eq_on_closedPatchBox g eta a
    apply (mem_closedPatchBox_iff_norm_le p).mpr
    exact (by simpa only [Metric.mem_ball,dist_zero_right] using hp : ‖p‖ < 4).le

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_AffineCovariantHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

theorem heightEnergy_affinePullback_pos_iff {g : MetricField} {z : Coord → ℝ}
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hz : DifferentiableAt ℝ z (affineCoordinates b R q)) :
    0 < heightEnergy (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) q ↔
      0 < heightEnergy g z (affineCoordinates b R q) := by
  rw [heightEnergy_affinePullback b R hR q hz]
  exact mul_pos_iff_of_pos_left (sq_pos_of_ne_zero ((Matrix.isUnit_iff_isUnit_det _).mp hR).ne_zero)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_ExtremumHessian
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace ExtremumCalculus

theorem second_deriv_nonneg_of_localMin {f : ℝ → ℝ} {a : ℝ}
    (hm : IsLocalMin f a) (hc : ContinuousAt f a) :
    0 ≤ deriv (deriv f) a := by
  by_contra hn
  have hn' : deriv (deriv f) a < 0 := lt_of_not_ge hn
  have hM := isLocalMax_of_deriv_deriv_neg hn' hm.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 a] (fun _ => f a) := by
    filter_upwards [hm, hM] with x hx hy
    exact le_antisymm hy hx
  have hz : deriv (deriv f) a = 0 := by
    simpa using heq.deriv.deriv_eq
  exact (ne_of_lt hn') hz

theorem second_deriv_nonpos_of_localMax {f : ℝ → ℝ} {a : ℝ}
    (hM : IsLocalMax f a) (hc : ContinuousAt f a) :
    deriv (deriv f) a ≤ 0 := by
  by_contra hn
  have hn' : 0 < deriv (deriv f) a := lt_of_not_ge hn
  have hm := isLocalMin_of_deriv_deriv_pos hn' hM.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 a] (fun _ => f a) := by
    filter_upwards [hm, hM] with x hx hy
    exact le_antisymm hy hx
  have hz : deriv (deriv f) a = 0 := by
    simpa using heq.deriv.deriv_eq
  exact (ne_of_gt hn') hz

end ExtremumCalculus

variable {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem second_deriv_along_line (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hp : p ∈ U) (v : Coord) :
    deriv (deriv (fun t : ℝ => z (p + t • v))) 0 =
      fderiv ℝ (fderiv ℝ z) p v v := by
  have hL (t : ℝ) : HasDerivAt (fun s : ℝ => p + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have hLp : Tendsto (fun t : ℝ => p + t • v) (𝓝 0) (𝓝 p) := by
    have hc := (hL 0).continuousAt
    change Tendsto (fun t : ℝ => p + t • v) (𝓝 0) (𝓝 (p + (0 : ℝ) • v)) at hc
    simpa only [zero_smul, add_zero] using hc
  have heq : deriv (fun t : ℝ => z (p + t • v)) =ᶠ[𝓝 0]
      (fun t : ℝ => fderiv ℝ z (p + t • v) v) := by
    filter_upwards [hLp.eventually (hU.mem_nhds hp)] with t ht
    have hd := (((hz (p + t • v) ht).contDiffAt
      (hU.mem_nhds ht)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
    simpa [Function.comp_def] using (hd.comp_hasDerivAt t (hL t)).deriv
  have hs : ContDiffOn ℝ ∞ (fderiv ℝ z) U := hz.fderiv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd : HasFDerivAt (fderiv ℝ z) (fderiv ℝ (fderiv ℝ z) p) p :=
    (((hs p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => fderiv ℝ z (p + t • v))
      (fderiv ℝ (fderiv ℝ z) p v) 0 := by
    simpa [Function.comp_def] using
      (hd.comp_hasDerivAt_of_eq 0 (hL 0) (by simp))
  rw [heq.deriv_eq]
  simpa using (hcomp.clm_apply (hasDerivAt_const 0 v)).deriv

theorem secondFDeriv_nonneg_of_localMin (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hp : p ∈ U) (hm : IsLocalMin z p) (v : Coord) :
    0 ≤ fderiv ℝ (fderiv ℝ z) p v v := by
  have hL : ContinuousAt (fun t : ℝ => p + t • v) 0 := by fun_prop
  have hm' : IsLocalMin (fun t : ℝ => z (p + t • v)) 0 := by
    simpa [Function.comp_def] using
      (show IsLocalMin z (p + (0 : ℝ) • v) by simpa using hm).comp_continuous
        (g := fun t : ℝ => p + t • v) hL
  have hc : ContinuousAt (fun t : ℝ => z (p + t • v)) 0 := by
    exact (((hz p hp).contDiffAt (hU.mem_nhds hp)).continuousAt).comp_of_eq hL (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [← second_deriv_along_line hz hU hp v]
  exact ExtremumCalculus.second_deriv_nonneg_of_localMin hm' hc

theorem secondFDeriv_nonpos_of_localMax (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hp : p ∈ U) (hM : IsLocalMax z p) (v : Coord) :
    fderiv ℝ (fderiv ℝ z) p v v ≤ 0 := by
  have hL : ContinuousAt (fun t : ℝ => p + t • v) 0 := by fun_prop
  have hM' : IsLocalMax (fun t : ℝ => z (p + t • v)) 0 := by
    simpa [Function.comp_def] using
      (show IsLocalMax z (p + (0 : ℝ) • v) by simpa using hM).comp_continuous
        (g := fun t : ℝ => p + t • v) hL
  have hc : ContinuousAt (fun t : ℝ => z (p + t • v)) 0 := by
    exact (((hz p hp).contDiffAt (hU.mem_nhds hp)).continuousAt).comp_of_eq hL (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [← second_deriv_along_line hz hU hp v]
  exact ExtremumCalculus.second_deriv_nonpos_of_localMax hM' hc

theorem secondFDeriv_basis_quadratic (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hp : p ∈ U) (t : ℝ) :
    fderiv ℝ (fderiv ℝ z) p
        (t • Pi.single 0 1 + Pi.single 1 1)
        (t • Pi.single 0 1 + Pi.single 1 1) =
      ordinaryHessian z p 0 0 * (t * t) +
        (2 * ordinaryHessian z p 0 1) * t + ordinaryHessian z p 1 1 := by
  have hsym : fderiv ℝ (fderiv ℝ z) p (Pi.single 1 1) (Pi.single 0 1) =
      fderiv ℝ (fderiv ℝ z) p (Pi.single 0 1) (Pi.single 1 1) := by
    rw [← second_coordPartial_eq_fderiv hz hU hp,
      ← second_coordPartial_eq_fderiv hz hU hp]
    exact coordPartial_comm hz hU hp 1 0
  simp only [ordinaryHessian, second_coordPartial_eq_fderiv hz hU hp,
    map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul, hsym]
  ring

theorem ordinaryHessian_det_nonneg_of_localMin (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hp : p ∈ U) (hm : IsLocalMin z p) :
    0 ≤ (ordinaryHessian z p).det := by
  have hq : ∀ t : ℝ, 0 ≤ ordinaryHessian z p 0 0 * (t * t) +
      (2 * ordinaryHessian z p 0 1) * t + ordinaryHessian z p 1 1 := by
    intro t
    rw [← secondFDeriv_basis_quadratic hz hU hp t]
    exact secondFDeriv_nonneg_of_localMin hz hU hp hm _
  have hd := discrim_le_zero hq
  have hsym : ordinaryHessian z p 1 0 = ordinaryHessian z p 0 1 :=
    coordPartial_comm hz hU hp 1 0
  rw [Matrix.det_fin_two, hsym]
  dsimp [discrim] at hd
  nlinarith

theorem ordinaryHessian_det_nonneg_of_localMax (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hp : p ∈ U) (hM : IsLocalMax z p) :
    0 ≤ (ordinaryHessian z p).det := by
  have hq : ∀ t : ℝ, ordinaryHessian z p 0 0 * (t * t) +
      (2 * ordinaryHessian z p 0 1) * t + ordinaryHessian z p 1 1 ≤ 0 := by
    intro t
    rw [← secondFDeriv_basis_quadratic hz hU hp t]
    exact secondFDeriv_nonpos_of_localMax hz hU hp hM _
  have hd := discrim_le_zero_of_nonpos hq
  have hsym : ordinaryHessian z p 1 0 = ordinaryHessian z p 0 1 :=
    coordPartial_comm hz hU hp 1 0
  rw [Matrix.det_fin_two, hsym]
  dsimp [discrim] at hd
  nlinarith

theorem ordinaryHessian_det_nonneg_of_localExtr (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hp : p ∈ U) (he : IsLocalExtr z p) :
    0 ≤ (ordinaryHessian z p).det :=
  he.elim (ordinaryHessian_det_nonneg_of_localMin hz hU hp)
    (ordinaryHessian_det_nonneg_of_localMax hz hU hp)

theorem covHessian_eq_ordinaryHessian_of_localExtr (g : MetricField)
    (he : IsLocalExtr z p) : covHessian g z p = ordinaryHessian z p := by
  have hd : fderiv ℝ z p = 0 := he.fderiv_eq_zero
  ext i j
  simp [covHessian, ordinaryHessian, coordPartial, hd]

theorem covHessian_at_localExtr {g : MetricField} (_hg : SmoothPositiveOn g U)
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) (hp : p ∈ U)
    (he : IsLocalExtr z p) :
    fderiv ℝ z p = 0 ∧ covHessian g z p = ordinaryHessian z p ∧
      0 ≤ (covHessian g z p).det := by
  refine ⟨he.fderiv_eq_zero, covHessian_eq_ordinaryHessian_of_localExtr g he, ?_⟩
  rw [covHessian_eq_ordinaryHessian_of_localExtr g he]
  exact ordinaryHessian_det_nonneg_of_localExtr hz hU hp he

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_GaussEquation
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

theorem coordPartial_vector_sub {A B : Coord → Ambient} {p : Coord}
    (hA : DifferentiableAt ℝ A p) (hB : DifferentiableAt ℝ B p) (i : Fin 2) :
    coordPartial i (fun q => A q - B q) p = coordPartial i A p - coordPartial i B p := by
  simp only [coordPartial, fderiv_fun_sub hA hB, sub_apply]

theorem coordPartial_vector_sum (A : Fin 2 → Coord → Ambient) {p : Coord}
    (hA : ∀ r, DifferentiableAt ℝ (A r) p) (i : Fin 2) :
    coordPartial i (fun q => ∑ r, A r q) p = ∑ r, coordPartial i (A r) p := by
  simp only [Fin.sum_univ_two, coordPartial, fderiv_fun_add (hA 0) (hA 1),
    add_apply]

theorem coordPartial_scalar_vector {c : Coord → ℝ} {A : Coord → Ambient} {p : Coord}
    (hc : DifferentiableAt ℝ c p) (hA : DifferentiableAt ℝ A p) (i : Fin 2) :
    coordPartial i (fun q => c q • A q) p =
      coordPartial i c p • A p + c p • coordPartial i A p := by
  simp only [coordPartial, fderiv_fun_smul hc hA, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply]
  exact add_comm _ _

theorem normalResidual_contDiffOn {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) (a b : Fin 2) :
    ContDiffOn ℝ ∞ (fun q => normalResidual g F q a b) U := by
  have ht (r : Fin 2) := partial_contDiffOn hF hU r
  have hsecond := partial_contDiffOn (ht b) hU a
  exact hsecond.sub (ContDiffOn.sum fun r _ =>
    (christoffel_contDiffOn hg hU r a b).smul (ht r))

theorem coordPartial_normalResidual {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (d a b : Fin 2) :
    coordPartial d (fun q => normalResidual g F q a b) p =
      coordPartial d (coordPartial a (coordPartial b F)) p -
        ∑ r, (coordPartial d (christoffel g r a b) p • coordPartial r F p +
          christoffel g r a b p • coordPartial d (coordPartial r F) p) := by
  have ht (r : Fin 2) : ContDiffOn ℝ ∞ (coordPartial r F) U :=
    partial_contDiffOn hF hU r
  have hdT (r : Fin 2) : DifferentiableAt ℝ (coordPartial r F) p :=
    (((ht r) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdΓ (r : Fin 2) : DifferentiableAt ℝ (christoffel g r a b) p :=
    (((christoffel_contDiffOn hg hU r a b) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdSecond : DifferentiableAt ℝ (coordPartial a (coordPartial b F)) p :=
    (((partial_contDiffOn (ht b) hU a) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdTerm (r : Fin 2) : DifferentiableAt ℝ
      (fun q => christoffel g r a b q • coordPartial r F q) p :=
    (hdΓ r).smul (hdT r)
  change coordPartial d (fun q => coordPartial a (coordPartial b F) q -
    ∑ r, christoffel g r a b q • coordPartial r F q) p = _
  rw [coordPartial_vector_sub hdSecond (DifferentiableAt.fun_sum fun r _ => hdTerm r),
    coordPartial_vector_sum _ hdTerm]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  exact coordPartial_scalar_vector (hdΓ r) (hdT r) d

theorem residual_inner_second_eq_residual_inner_residual
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (a b c d : Fin 2) :
    inner ℝ (normalResidual g F p a b) (coordPartial c (coordPartial d F) p) =
      inner ℝ (normalResidual g F p a b) (normalResidual g F p c d) := by
  change inner ℝ (normalResidual g F p a b) (coordPartial c (coordPartial d F) p) =
    inner ℝ (normalResidual g F p a b)
      (coordPartial c (coordPartial d F) p -
        ∑ r, christoffel g r c d p • coordPartial r F p)
  simp only [inner_sub_right, inner_sum, real_inner_smul_right,
    normalResidual_orthogonal_tangent hg hF hU hp, mul_zero,
    Finset.sum_const_zero, sub_zero]

theorem residual_derivative_inner_tangent
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (d a b l : Fin 2) :
    inner ℝ (coordPartial d (fun q => normalResidual g F q a b) p)
        (coordPartial l F p) =
      -inner ℝ (normalResidual g F p a b) (normalResidual g F p d l) := by
  have hdS : DifferentiableAt ℝ (fun q => normalResidual g F q a b) p :=
    (((normalResidual_contDiffOn hg hF.1 hU a b) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdT : DifferentiableAt ℝ (coordPartial l F) p :=
    (((partial_contDiffOn hF.1 hU l) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hzero : (fun q => inner ℝ (normalResidual g F q a b) (coordPartial l F q))
      =ᶠ[𝓝 p] (fun _ : Coord => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact normalResidual_orthogonal_tangent hg hF hU hq a b l
  have hderiv := congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single d 1)) hzero.fderiv_eq
  rw [fderiv_inner_apply ℝ hdS hdT] at hderiv
  simp only [fderiv_const_apply, zero_apply] at hderiv
  change inner ℝ (normalResidual g F p a b) (coordPartial d (coordPartial l F) p) +
    inner ℝ (coordPartial d (fun q => normalResidual g F q a b) p)
      (coordPartial l F p) = 0 at hderiv
  rw [residual_inner_second_eq_residual_inner_residual hg hF hU hp] at hderiv
  linarith

theorem second_partial_inner_tangent_eq_christoffel_sum
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (a b l : Fin 2) :
    inner ℝ (coordPartial a (coordPartial b F) p) (coordPartial l F p) =
      ∑ r, christoffel g r a b p * g p l r := by
  have ht (r : Fin 2) : inner ℝ (coordPartial r F p) (coordPartial l F p) = g p l r := by
    rw [real_inner_comm]
    exact congrFun (congrFun (inducedMetric_eq_of_isometric hF hp) l) r
  have h := normalResidual_orthogonal_tangent hg hF hU hp a b l
  simp only [normalResidual, inner_sub_left, sum_inner, real_inner_smul_left, ht] at h
  exact sub_eq_zero.mp h

theorem riemann_contraction_eq_residual_products
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j k l : Fin 2) :
    (∑ r, g p l r * riemann g r k i j p) =
      inner ℝ (normalResidual g F p j k) (normalResidual g F p i l) -
        inner ℝ (normalResidual g F p i k) (normalResidual g F p j l) := by
  have hi := residual_derivative_inner_tangent hg hF hU hp i j k l
  have hj := residual_derivative_inner_tangent hg hF hU hp j i k l
  rw [coordPartial_normalResidual hg hF.1 hU hp] at hi hj
  have ht (r : Fin 2) : inner ℝ (coordPartial r F p) (coordPartial l F p) = g p l r := by
    rw [real_inner_comm]
    exact congrFun (congrFun (inducedMetric_eq_of_isometric hF hp) l) r
  simp only [inner_sub_left, sum_inner, inner_add_left, real_inner_smul_left, ht,
    second_partial_inner_tangent_eq_christoffel_sum hg hF hU hp] at hi hj
  have hcomm := coordPartial_comm (partial_contDiffOn hF.1 hU k) hU hp i j
  rw [hcomm] at hi
  simp only [riemann, Fin.sum_univ_two]
  simp only [Fin.sum_univ_two] at hi hj
  linear_combination hj - hi

theorem det_secondFundamental_eq_gaussianCurvature_mul_det
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) {n : Ambient} (hn : IsUnitNormalAt F n p) :
    (secondFundamental F n p).det = gaussianCurvature g p * (g p).det := by
  have hR := riemann_contraction_eq_residual_products hg hF hU hp 0 1 1 0
  simp only [normalResidual_eq_secondFundamental_smul hg hF hU hp hn,
    real_inner_smul_left, real_inner_smul_right, hn.1, mul_one] at hR
  calc
    (secondFundamental F n p).det = ∑ r, g p 0 r * riemann g r 1 0 1 p := by
      rw [hR, Matrix.det_fin_two]
      ring
    _ = gaussianCurvature g p * (g p).det := by
      unfold gaussianCurvature
      rw [div_mul_cancel₀ _ (metricDet_ne_zero hg hp)]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_HeightNorm
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff BigOperators Matrix
namespace SmoothLocal.Geometry

theorem height_normal_tangent_norm {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) {n : Ambient}
    (hn : IsUnitNormalAt F n p) (e : Ambient) :
    covectorNormSq g (height F e) p + (inner ℝ n e) ^ 2 = inner ℝ e e := by
  let d : Coord := fun i => coordPartial i (height F e) p
  let c : Coord := (g p)⁻¹ *ᵥ d
  let T : Ambient := fderiv ℝ F p c
  have hgc : g p *ᵥ c = d := by
    dsimp only [c]
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 p hp).isUnit),
      Matrix.one_mulVec]
  have hdF : DifferentiableAt ℝ F p :=
    ((hF.1 p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have horth (i : Fin 2) : inner ℝ (coordPartial i F p) (e - T) = 0 := by
    rw [inner_sub_right]
    have he : inner ℝ (coordPartial i F p) e = d i := (partial_height hdF e i).symm
    rw [he]
    have ht := hF.2 p hp (Pi.single i 1) c
    have ht' : inner ℝ (coordPartial i F p) T = d i := by
      simpa only [hgc, single_one_dotProduct, coordPartial, T] using ht
    rw [ht', sub_self]
  have hnT : inner ℝ n T = 0 := by
    rw [real_inner_comm]
    exact hn.2 c
  have hdecomp := normal_eq_inner_smul_of_independent_tangents
    (fun i => coordPartial i F p) (isometric_tangents_independent hg hF hp)
    n (e - T) hn.1 (fun i => hn.2 (Pi.single i 1)) horth
  rw [inner_sub_right, hnT, sub_zero] at hdecomp
  have hT : T = e - (inner ℝ n e) • n := by
    apply eq_sub_iff_add_eq.mpr
    have h := (sub_eq_iff_eq_add).mp hdecomp
    simpa only [add_comm] using h.symm
  have hnorm : inner ℝ T T = covectorNormSq g (height F e) p := by
    calc
      inner ℝ T T = c ⬝ᵥ (g p *ᵥ c) := hF.2 p hp c c
      _ = c ⬝ᵥ d := by rw [hgc]
      _ = covectorNormSq g (height F e) p := by
        simp only [c, d, Matrix.mulVec, dotProduct, covectorNormSq, inverseMetric,
          Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [← hnorm, hT]
  exact SmoothLocal.normal_tangent_identity e n hn.1

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_HeightEquation
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff BigOperators
namespace SmoothLocal.Geometry

theorem exists_isUnitNormalAt {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    {p : Coord} (hp : p ∈ U) : ∃ n, IsUnitNormalAt F n p := by
  obtain ⟨n, hn, hnt⟩ := exists_unit_normal_of_independent_tangents
    (fun i => coordPartial i F p) (isometric_tangents_independent hg hF hp)
  refine ⟨n, hn, ?_⟩
  intro v
  rw [← Finset.univ_sum_single v, map_sum, sum_inner]
  apply Finset.sum_eq_zero
  intro i _
  have hsingle : Pi.single i (v i) = v i • Pi.single i (1 : ℝ) := by
    ext j
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hsingle, map_smul, real_inner_smul_left]
  change v i * inner ℝ (coordPartial i F p) n = 0
  rw [hnt, mul_zero]

theorem geometric_height_equation {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hU : IsOpen U) (e : Ambient) (he : inner ℝ e e = 1)
    {p : Coord} (hp : p ∈ U) :
    (covHessian g (height F e) p).det =
      gaussianCurvature g p * (g p).det * (1 - covectorNormSq g (height F e) p) := by
  obtain ⟨n, hn⟩ := exists_isUnitNormalAt hg hF hp
  have hnorm := height_normal_tangent_norm hg hF hU hp hn e
  have hnu : (inner ℝ n e) ^ 2 = 1 - covectorNormSq g (height F e) p := by
    rw [he] at hnorm
    linarith
  rw [covHessian_height_eq_normal_mul_secondFundamental hg hF hU hp hn e,
    SmoothLocal.det_two_smul,
    det_secondFundamental_eq_gaussianCurvature_mul_det hg hF hU hp hn, hnu]
  ring

theorem geometric_height_normal_point {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) {e : Ambient} (he : IsUnitNormalAt F e p) :
    fderiv ℝ (height F e) p = 0 ∧
      covHessian g (height F e) p = secondFundamental F e p :=
  ⟨height_derivative_at_normal hF.1 hU hp he,
    covHessian_height_at_normal g hF.1 hU hp he⟩

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_NegativeCurvatureHeight
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Geometry

theorem heightEnergy_at_critical (g : MetricField) (z : Coord → ℝ) (p : Coord)
    (hcrit : fderiv ℝ z p = 0) : heightEnergy g z p = (g p).det := by
  simp [heightEnergy, covectorNormSq, coordPartial, hcrit]

theorem no_localExtr_at_negative_curvature
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hp : p ∈ U) (hK : gaussianCurvature g p < 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    ¬IsLocalExtr z p := by
  intro he
  have hc := covHessian_at_localExtr hg hz hU hp he
  have hE : 0 < heightEnergy g z p := by
    rw [heightEnergy_at_critical g z p hc.1]
    exact (hg.2 p hp).det_pos
  have hneg : (covHessian g z p).det < 0 := by
    rw [hD]
    exact mul_neg_of_neg_of_pos hK hE
  exact (not_lt_of_ge hc.2.2) hneg

theorem immersion_height_no_localExtr
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (e : Ambient) (he : inner ℝ e e = 1) (hp : p ∈ U)
    (hK : gaussianCurvature g p < 0) : ¬IsLocalExtr (height F e) p := by
  apply no_localExtr_at_negative_curvature hg (height_smooth hF.1 e) hU hp hK
  simpa only [heightEnergy, mul_assoc] using geometric_height_equation hg hF hU e he hp

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_RankOne2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Matrix

namespace SmoothLocal.Geometry

theorem two_by_two_rank_pos {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A ≠ 0) :
    0 < A.rank := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hrange : LinearMap.range A.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp hz
  have hmap : A.mulVecLin = 0 := LinearMap.range_eq_bot.mp hrange
  apply hA
  ext i j
  have hv := congrArg
    (fun f : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) => f (Pi.single j 1) i) hmap
  change A i j = 0
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, LinearMap.zero_apply, Pi.zero_apply] using hv

theorem two_by_two_rank_eq_one_of_ne_zero_det_eq_zero
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A ≠ 0) (hdet : A.det = 0) :
    A.rank = 1 := by
  have hdetL : LinearMap.det A.mulVecLin = 0 := by
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
    exact hdet
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdetL
  have hkpos : 0 < Module.finrank ℝ (LinearMap.ker A.mulVecLin) := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hker (Submodule.finrank_eq_zero.mp hz)
  have hnull : A.rank + Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 2 := by
    simpa [Matrix.rank] using A.mulVecLin.finrank_range_add_finrank_ker
  have hrpos := two_by_two_rank_pos hA
  omega

theorem two_by_two_rank_eq_one_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.rank = 1 ↔ A ≠ 0 ∧ A.det = 0 := by
  constructor
  · intro hr
    refine ⟨?_, ?_⟩
    · intro hz
      simp only [hz, Matrix.rank_zero] at hr
      omega
    · by_contra hd
      have hfull := Matrix.rank_of_det_ne_zero hd
      simp only [Fintype.card_fin] at hfull
      omega
  · rintro ⟨hA, hd⟩
    exact two_by_two_rank_eq_one_of_ne_zero_det_eq_zero hA hd

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_RankOneOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Matrix BigOperators
open WithLp

namespace SmoothLocal.Geometry

theorem exists_nonzero_dyad_of_symmetric_rank_one
    (H : Matrix (Fin 2) (Fin 2) ℝ) (hsym : Hᵀ = H) (hrank : H.rank = 1) :
    ∃ lam : ℝ, ∃ u : PlanarAxis, lam ≠ 0 ∧ u ≠ 0 ∧
      H = lam • Matrix.vecMulVec (ofLp u) (ofLp u) := by
  classical
  have hprops := (two_by_two_rank_eq_one_iff H).mp hrank
  have h10 : H 1 0 = H 0 1 := congrFun (congrFun hsym 0) 1
  have hd : H 0 0 * H 1 1 - H 0 1 ^ 2 = 0 := by
    simpa only [Matrix.det_fin_two, h10, pow_two] using hprops.2
  by_cases h00 : H 0 0 = 0
  · have h01 : H 0 1 = 0 := by rw [h00] at hd; nlinarith [sq_nonneg (H 0 1)]
    have h11 : H 1 1 ≠ 0 := by
      intro hz
      apply hprops.1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, hz]
    let u : PlanarAxis := toLp 2 ![0, H 1 1]
    have hu : u ≠ 0 := by
      intro hu0
      have hc := congrArg (fun w : PlanarAxis => w 1) hu0
      exact h11 (by simpa [u] using hc)
    refine ⟨(H 1 1)⁻¹, u, inv_ne_zero h11, hu, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u, Matrix.smul_apply, h00, h01, h10, h11]
  · let u : PlanarAxis := toLp 2 ![H 0 0, H 0 1]
    have hu : u ≠ 0 := by
      intro hu0
      have hc := congrArg (fun w : PlanarAxis => w 0) hu0
      exact h00 (by simpa [u] using hc)
    refine ⟨(H 0 0)⁻¹, u, inv_ne_zero h00, hu, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u, Matrix.smul_apply, h10] <;>
      field_simp [h00]
    nlinarith [hd]

theorem exists_unit_dyad_of_symmetric_rank_one
    (H : Matrix (Fin 2) (Fin 2) ℝ) (hsym : Hᵀ = H) (hrank : H.rank = 1) :
    ∃ lam : ℝ, ∃ v : PlanarAxis, lam ≠ 0 ∧ ‖v‖ = 1 ∧
      H = lam • Matrix.vecMulVec (ofLp v) (ofLp v) := by
  obtain ⟨μ, u, hμ, hu, hH⟩ := exists_nonzero_dyad_of_symmetric_rank_one H hsym hrank
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  refine ⟨μ * ‖u‖ ^ 2, ‖u‖⁻¹ • u, mul_ne_zero hμ (pow_ne_zero 2 hn),
    norm_smul_inv_norm (𝕜 := ℝ) hu, ?_⟩
  rw [hH]
  ext i j
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul]
  field_simp [hn]

theorem planar_inner_coordinates (v a : PlanarAxis) :
    inner ℝ v a = v 0 * a 0 + v 1 * a 1 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct, Fin.sum_univ_two]
  ring

theorem clockwiseAxis_orthogonal (a : PlanarAxis) : inner ℝ a (clockwiseAxis a) = 0 := by
  rw [planar_inner_coordinates]
  change a 0 * a 1 + a 1 * (-a 0) = 0
  ring

theorem clockwiseAxis_unit {a : PlanarAxis} (ha : ‖a‖ = 1) : ‖clockwiseAxis a‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  change a 1 ^ 2 + (-a 0) ^ 2 = (1 : ℝ) ^ 2
  have hs := planarAxis_sq_sum ha
  nlinarith [hs]

theorem nearby_axis_inner_bounds {v a : PlanarAxis} (ha : ‖a‖ = 1)
    (hclose : dist v a < (1 / 1000 : ℝ)) :
    |inner ℝ v a - 1| < (1 / 1000 : ℝ) ∧
      |inner ℝ v (clockwiseAxis a)| < (1 / 1000 : ℝ) := by
  constructor
  · have hb := abs_real_inner_le_norm (v - a) a
    have heq : inner ℝ (v - a) a = inner ℝ v a - 1 := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, ha, one_pow]
    rw [heq, ha, mul_one, ← dist_eq_norm] at hb
    exact hb.trans_lt hclose
  · have hb := abs_real_inner_le_norm (v - a) (clockwiseAxis a)
    rw [inner_sub_left, clockwiseAxis_orthogonal, sub_zero,
      clockwiseAxis_unit ha, mul_one, ← dist_eq_norm] at hb
    exact hb.trans_lt hclose

theorem rotated_dyad_entries (lam : ℝ) (v a : PlanarAxis) :
    rotatedForm (lam • Matrix.vecMulVec (ofLp v) (ofLp v)) a 1 1 =
        lam * (inner ℝ v a) ^ 2 ∧
      rotatedForm (lam • Matrix.vecMulVec (ofLp v) (ofLp v)) a 0 1 =
        lam * inner ℝ v (clockwiseAxis a) * inner ℝ v a := by
  constructor <;>
    simp only [rotatedForm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul] <;>
    simp [axisRotation, clockwiseAxis, planar_inner_coordinates] <;> ring

theorem rotated_dyad_admissible_axis (lam : ℝ) (hlam : lam ≠ 0) (v a : PlanarAxis)
    (ha : ‖a‖ = 1) (hclose : dist v a < (1 / 1000 : ℝ)) :
    rotatedForm (lam • Matrix.vecMulVec (ofLp v) (ofLp v)) a 1 1 ≠ 0 ∧
      |rotatedForm (lam • Matrix.vecMulVec (ofLp v) (ofLp v)) a 0 1 /
        rotatedForm (lam • Matrix.vecMulVec (ofLp v) (ofLp v)) a 1 1| < (1 / 100 : ℝ) := by
  obtain ⟨hcos, hsin⟩ := nearby_axis_inner_bounds ha hclose
  have hcospos : 0 < inner ℝ v a := by
    have hl := (abs_lt.mp hcos).1
    linarith
  obtain ⟨hyy, hxy⟩ := rotated_dyad_entries lam v a
  constructor
  · rw [hyy]
    exact mul_ne_zero hlam (pow_ne_zero 2 hcospos.ne')
  · rw [hxy, hyy]
    have hquot : lam * inner ℝ v (clockwiseAxis a) * inner ℝ v a /
        (lam * (inner ℝ v a) ^ 2) = inner ℝ v (clockwiseAxis a) / inner ℝ v a := by
      field_simp [hlam, hcospos.ne']
    rw [hquot, abs_div, abs_of_pos hcospos]
    apply (div_lt_iff₀ hcospos).mpr
    have hl := (abs_lt.mp hcos).1
    nlinarith

theorem exists_orientationRotation_for_rank_one
    (H : Matrix (Fin 2) (Fin 2) ℝ) (hsym : Hᵀ = H) (hrank : H.rank = 1) :
    ∃ R ∈ orientationRotations,
      (Rᵀ * H * R) 1 1 ≠ 0 ∧
      |(Rᵀ * H * R) 0 1 / (Rᵀ * H * R) 1 1| < (1 / 100 : ℝ) := by
  classical
  obtain ⟨lam, v, hlam, hv, hH⟩ := exists_unit_dyad_of_symmetric_rank_one H hsym hrank
  obtain ⟨a, ha, hclose⟩ := orientationAxes_cover v hv
  refine ⟨axisRotation a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
  rw [hH]
  exact rotated_dyad_admissible_axis lam hlam v a (orientationAxes_unit a ha) hclose

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_OrientedHeightPullback
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Flow

theorem orientedCovHessian_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => orientedCovHessian g z R p i j) U := by
  simp only [orientedCovHessian, Matrix.mul_apply, Matrix.transpose_apply]
  apply ContDiffOn.sum
  intro k _
  apply ContDiffOn.mul _ contDiffOn_const
  apply ContDiffOn.sum
  intro a _
  exact contDiffOn_const.mul (covHessian_contDiffOn hg hU hz a k)

theorem exists_open_oriented_height_neighborhood
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {b : Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hb : b ∈ U) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hE : 0 < heightEnergy g z b) (hyy : orientedCovHessian g z R b 1 1 ≠ 0)
    (hq : |orientedCovHessian g z R b 0 1 / orientedCovHessian g z R b 1 1| <
      (1 : ℝ) / 100) :
    ∃ V : Set Coord, IsOpen V ∧ b ∈ V ∧ V ⊆ U ∧
      ∀ p ∈ V, 0 < heightEnergy g z p ∧ orientedCovHessian g z R p 1 1 ≠ 0 ∧
        |orientedCovHessian g z R p 0 1 / orientedCovHessian g z R p 1 1| <
          (1 : ℝ) / 100 := by
  have hEc : ContinuousAt (heightEnergy g z) b :=
    (heightEnergy_contDiffOn hg hU hz).continuousOn.continuousAt (hU.mem_nhds hb)
  have hHc (i j : Fin 2) : ContinuousAt (fun p => orientedCovHessian g z R p i j) b :=
    (orientedCovHessian_contDiffOn hg hz hU R i j).continuousOn.continuousAt (hU.mem_nhds hb)
  have hqc : ContinuousAt (fun p =>
      |orientedCovHessian g z R p 0 1 / orientedCovHessian g z R p 1 1|) b :=
    ((hHc 0 1).div (hHc 1 1) hyy).abs
  have hgood : {p | p ∈ U ∧ 0 < heightEnergy g z p ∧
      orientedCovHessian g z R p 1 1 ≠ 0 ∧
      |orientedCovHessian g z R p 0 1 / orientedCovHessian g z R p 1 1| <
        (1 : ℝ) / 100} ∈ 𝓝 b := by
    filter_upwards [hU.mem_nhds hb, continuousAt_const.eventually_lt hEc hE,
      (hHc 1 1).eventually_ne hyy, hqc.eventually_lt continuousAt_const hq]
      with p hp hEp hyyp hqp
    exact ⟨hp, hEp, hyyp, hqp⟩
  obtain ⟨V, hVsub, hVo, hbV⟩ := mem_nhds_iff.mp hgood
  exact ⟨V, hVo, hbV, fun p hp => (hVsub hp).1, fun p hp => (hVsub hp).2⟩

theorem rank_one_height_has_oriented_neighborhood
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord} {b : Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hb : b ∈ U) (e : Ambient) (he : IsUnitNormalAt F e b)
    (hrank : (secondFundamental F e b).rank = 1) :
    ∃ R : OrientationLabel, ∃ V : Set Coord,
      IsOpen V ∧ b ∈ V ∧ V ⊆ U ∧
      ∀ p ∈ V, 0 < heightEnergy g (height F e) p ∧
        orientedCovHessian g (height F e) R.val p 1 1 ≠ 0 ∧
        |orientedCovHessian g (height F e) R.val p 0 1 /
          orientedCovHessian g (height F e) R.val p 1 1| < (1 : ℝ) / 100 := by
  have hz := height_smooth hF.1 e
  have hnpoint := geometric_height_normal_point hF hU hb he
  have hsym : (covHessian g (height F e) b)ᵀ = covHessian g (height F e) b := by
    ext i j
    exact covHessian_symm hg hU hz hb j i
  have hHrank : (covHessian g (height F e) b).rank = 1 := by
    rw [hnpoint.2]
    exact hrank
  obtain ⟨R, hRnet, hRyy, hRq⟩ :=
    exists_orientationRotation_for_rank_one (covHessian g (height F e) b) hsym hHrank
  have hE : 0 < heightEnergy g (height F e) b := by
    rw [heightEnergy_at_critical g (height F e) b hnpoint.1]
    exact (hg.2 b hb).det_pos
  obtain ⟨V, hVo, hbV, hVU, hVgood⟩ :=
    exists_open_oriented_height_neighborhood hg hz hU hb R hE hRyy hRq
  exact ⟨⟨R, hRnet⟩, V, hVo, hbV, hVU, hVgood⟩

theorem scaled_matrix_congruence (H R : Matrix (Fin 2) (Fin 2) ℝ) (scale : ℝ) :
    (scale • R)ᵀ * H * (scale • R) = scale ^ 2 • (Rᵀ * H * R) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Fin.sum_univ_two, smul_eq_mul]
  ring

theorem covHessian_affinePullback_scaled
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (c : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (scale : ℝ)
    (hM : IsUnit (scale • R)) (p : Coord) (hp : affineCoordinates c (scale • R) p ∈ U) :
    covHessian (affinePullbackMetric g c (scale • R)) (z ∘ affineCoordinates c (scale • R)) p =
      scale ^ 2 • orientedCovHessian g z R (affineCoordinates c (scale • R) p) := by
  rw [covHessian_affinePullback hg hz hU c (scale • R) hM p hp]
  exact scaled_matrix_congruence _ R scale

theorem modelSquare_subset_closedPatchBox : modelSquare ⊆ closedPatchBox := by
  intro p hp i
  have hpi : (-3 : ℝ) ≤ p i ∧ p i ≤ 3 := ⟨hp.1 i, hp.2 i⟩
  change (-4 : ℝ) ≤ p i ∧ p i ≤ 4
  constructor <;> linarith [hpi.1, hpi.2]

theorem oriented_patch_height_admissible_of_subset
    {g : MetricField} {F : Coord → Ambient} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (e : Ambient) (he : inner ℝ e e = 1) (hVU : V ⊆ U)
    (R : OrientationLabel)
    (hgood : ∀ q ∈ V, 0 < heightEnergy g (height F e) q ∧
      orientedCovHessian g (height F e) R.val q 1 1 ≠ 0 ∧
      |orientedCovHessian g (height F e) R.val q 0 1 /
        orientedCovHessian g (height F e) R.val q 1 1| < (1 : ℝ) / 100)
    (n k : ℕ) (c : Coord) (hpatch : orientedClosedPatch n k R c ⊆ V) :
    PatchAdmissibleHeight
      (affinePullbackMetric g c (orientedPatchScale n k R • R.val))
      (height (affinePullbackImmersion F c (orientedPatchScale n k R • R.val)) e) := by
  let M := orientedPatchScale n k R • R.val
  let W := affineCoordinates c M ⁻¹' U
  let gP := affinePullbackMetric g c M
  let FP := affinePullbackImmersion F c M
  let zP := height FP e
  have hM : IsUnit M := orientedPatchMatrix_isUnit n k R
  have hW : IsOpen W := isOpen_affine_preimage hU c M
  have hSimage (p : Coord) (hp : p ∈ modelSquare) : affineCoordinates c M p ∈ V :=
    hpatch ⟨p, modelSquare_subset_closedPatchBox hp, rfl⟩
  have hSW : modelSquare ⊆ W := fun p hp => hVU (hSimage p hp)
  have hgP : SmoothPositiveOn gP W :=
    affinePullbackMetric_smoothPositive hg c M (Matrix.mulVec_injective_of_isUnit hM)
  have hFP : IsometricOn gP FP W := affinePullbackImmersion_isometric hF hU c M
  have hzP : ContDiffOn ℝ ∞ zP W := height_smooth hFP.1 e
  have hz : ContDiffOn ℝ ∞ (height F e) U := height_smooth hF.1 e
  have hscale : (orientedPatchScale n k R) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (orientedPatchScale_pos n k R).ne'
  have hpoint (p : Coord) (hp : p ∈ modelSquare) :
      0 < heightEnergy gP zP p ∧ covHessian gP zP p 1 1 ≠ 0 ∧
      |hessianQuotient gP zP p| ≤ (1 : ℝ) / 100 := by
    have hpU := hVU (hSimage p hp)
    have hpGood := hgood _ (hSimage p hp)
    have hH : covHessian gP zP p = (orientedPatchScale n k R) ^ 2 •
        orientedCovHessian g (height F e) R.val (affineCoordinates c M p) :=
      covHessian_affinePullback_scaled hg hz hU c R.val (orientedPatchScale n k R) hM p hpU
    refine ⟨?_, ?_, ?_⟩
    · change 0 < heightEnergy (affinePullbackMetric g c M)
        ((height F e) ∘ affineCoordinates c M) p
      apply (heightEnergy_affinePullback_pos_iff c M hM p
        (((hz _ hpU).contDiffAt (hU.mem_nhds hpU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))).mpr
      exact hpGood.1
    · rw [hH]
      exact mul_ne_zero hscale hpGood.2.1
    · unfold hessianQuotient
      rw [hH]
      simp only [Matrix.smul_apply, smul_eq_mul, mul_div_mul_left _ _ hscale]
      exact hpGood.2.2.le
  refine ⟨W, hW, hSW, hgP, hzP, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simpa only [heightEnergy, mul_assoc] using geometric_height_equation hgP hFP hW e he (hSW hp)
  · intro p hp; exact (hpoint p hp).1
  · intro p hp; exact (hpoint p hp).2.1
  · intro p hp; exact (hpoint p hp).2.2

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_CompactBoundaryExtremum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

theorem exists_localExtr_of_constant_frontier
    {S : Set Coord} {z : Coord → ℝ} (hS : IsCompact S)
    (hne : (interior S).Nonempty) (hz : ContinuousOn z S)
    (c : ℝ) (hfront : ∀ p ∈ frontier S, z p = c) :
    ∃ p ∈ interior S, IsLocalExtr z p := by
  obtain ⟨p, hp⟩ := hne
  have hSn : S.Nonempty := ⟨p, interior_subset hp⟩
  obtain ⟨a, ha, hmax⟩ := hS.exists_isMaxOn hSn hz
  obtain ⟨b, hb, hmin⟩ := hS.exists_isMinOn hSn hz
  by_cases hai : a ∈ interior S
  · exact ⟨a, hai, Or.inr (hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hai))⟩
  by_cases hbi : b ∈ interior S
  · exact ⟨b, hbi, Or.inl (hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hbi))⟩
  have hac : z a = c := hfront a ⟨subset_closure ha, hai⟩
  have hbc : z b = c := hfront b ⟨subset_closure hb, hbi⟩
  have hzconst : ∀ q ∈ S, z q = c := by
    intro q hq
    exact le_antisymm (hac ▸ hmax hq) (hbc ▸ hmin hq)
  have hmaxp : IsMaxOn z S p := by
    intro q hq
    change z q ≤ z p
    rw [hzconst q hq, hzconst p (interior_subset hp)]
  exact ⟨p, hp, Or.inr (hmaxp.isLocalMax (mem_interior_iff_mem_nhds.mp hp))⟩

theorem immersion_height_not_constant_frontier
    {g : MetricField} {F : Coord → Ambient} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hS : IsCompact S) (hSU : S ⊆ U) (hne : (interior S).Nonempty)
    (hK : ∀ p ∈ interior S, gaussianCurvature g p < 0)
    (e : Ambient) (he : inner ℝ e e = 1) :
    ¬∃ c : ℝ, ∀ p ∈ frontier S, height F e p = c := by
  rintro ⟨c, hc⟩
  obtain ⟨p, hp, hextr⟩ := exists_localExtr_of_constant_frontier hS hne
    ((height_smooth hF.1 e).continuousOn.mono hSU) c hc
  exact immersion_height_no_localExtr hg hF hU e he (hSU (interior_subset hp))
    (hK p hp) hextr

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Obstructions_DiskBoundaryObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry

variable {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
variable {center : Coord} {radius : ℝ}

theorem exists_roundDisk_boundary_nonzero_secondFundamental
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hr : 0 < radius) (hDU : roundClosedDisk center radius ⊆ U)
    (hK : ∀ p ∈ roundOpenDisk center radius, gaussianCurvature g p < 0) :
    ∃ b ∈ frontier (roundClosedDisk center radius),
      secondFundamental F (unitNormalField F b) b ≠ 0 := by
  by_contra hnone
  have hcircle : ∀ t, coordinateCircle center radius t ∈ U :=
    fun t => hDU (coordinateCircle_mem_roundClosedDisk center radius t)
  have hII : ∀ t, secondFundamental F
      (unitNormalField F (coordinateCircle center radius t))
      (coordinateCircle center radius t) = 0 := by
    intro t
    by_contra ht
    exact hnone ⟨coordinateCircle center radius t,
      coordinateCircle_mem_frontier_roundClosedDisk center hr t, ht⟩
  obtain ⟨e, c, he, _, _, hh⟩ :=
    exists_circle_constant_normal_and_height hg hF hU hcircle hII
  have hK' : ∀ p ∈ interior (roundClosedDisk center radius), gaussianCurvature g p < 0 := by
    intro p hp
    exact hK p (by simpa only [interior_roundClosedDisk center hr] using hp)
  apply immersion_height_not_constant_frontier hg hF hU
    (isCompact_roundClosedDisk center hr) hDU
    (interior_roundClosedDisk_nonempty center hr) hK' e he
  refine ⟨c, ?_⟩
  intro p hp
  obtain ⟨t, rfl⟩ := exists_coordinateCircle_of_mem_frontier_roundClosedDisk center p hr hp
  exact hh t

theorem roundDisk_boundary_rank_one
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hr : 0 < radius) (hDU : roundClosedDisk center radius ⊆ U)
    (hK : ∀ p ∈ roundOpenDisk center radius, gaussianCurvature g p < 0)
    (hKboundary : ∀ p ∈ frontier (roundClosedDisk center radius), gaussianCurvature g p = 0) :
    ∃ b ∈ frontier (roundClosedDisk center radius),
      secondFundamental F (unitNormalField F b) b ≠ 0 ∧
      (secondFundamental F (unitNormalField F b) b).rank = 1 := by
  obtain ⟨b, hb, hII⟩ := exists_roundDisk_boundary_nonzero_secondFundamental
    hg hF hU hr hDU hK
  have hbD : b ∈ roundClosedDisk center radius :=
    ((mem_frontier_roundClosedDisk_iff center b hr).mp hb).le
  have hbU : b ∈ U := hDU hbD
  have hdet := det_secondFundamental_eq_gaussianCurvature_mul_det hg hF hU hbU
    (unitNormalField_isUnitNormalAt hg hF hbU)
  rw [hKboundary b hb, zero_mul] at hdet
  exact ⟨b, hb, hII, two_by_two_rank_eq_one_of_ne_zero_det_eq_zero hII hdet⟩

theorem exists_roundDisk_boundary_unitNormal_rank_one
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hr : 0 < radius) (hDU : roundClosedDisk center radius ⊆ U)
    (hK : ∀ p ∈ roundOpenDisk center radius, gaussianCurvature g p < 0)
    (hKboundary : ∀ p ∈ frontier (roundClosedDisk center radius), gaussianCurvature g p = 0) :
    ∃ b ∈ frontier (roundClosedDisk center radius), ∃ n : Ambient,
      IsUnitNormalAt F n b ∧ secondFundamental F n b ≠ 0 ∧
      (secondFundamental F n b).rank = 1 := by
  obtain ⟨b, hb, hII, hrank⟩ := roundDisk_boundary_rank_one hg hF hU hr hDU hK hKboundary
  have hbU : b ∈ U := hDU (((mem_frontier_roundClosedDisk_iff center b hr).mp hb).le)
  exact ⟨b, hb, unitNormalField F b, unitNormalField_isUnitNormalAt hg hF hbU, hII, hrank⟩

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Obstructions_UniversalPatchSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

theorem rank_one_boundary_eventually_admissible_patches
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord} {b : Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hbU : b ∈ U) (n : ℕ) (hb : b ∈ frontier (accumulatingDisk n))
    (e : Ambient) (he : IsUnitNormalAt F e b)
    (hrank : (secondFundamental F e b).rank = 1) :
    ∃ R : OrientationLabel, ∃ centers : ℕ → Coord,
      (∀ k, centers k ∈ orientedExteriorCenters n k R) ∧
      Tendsto centers atTop (𝓝 b) ∧
      ∀ᶠ k in atTop,
        orientedClosedPatch n k R (centers k) ⊆ U ∧
        PatchAdmissibleHeight
          (affinePullbackMetric g (centers k) (orientedPatchScale n k R • R.val))
          (height (affinePullbackImmersion F (centers k)
            (orientedPatchScale n k R • R.val)) e) := by
  obtain ⟨R, V, hVo, hbV, hVU, hgood⟩ :=
    rank_one_height_has_oriented_neighborhood hg hF hU hbU e he hrank
  obtain ⟨centers, hcenters, ht, hpatches⟩ :=
    every_boundary_point_every_orientation_patch_neighborhoods n b hb R
  refine ⟨R, centers, hcenters, ht, ?_⟩
  filter_upwards [hpatches V (hVo.mem_nhds hbV)] with k hk
  exact ⟨hk.trans hVU,
    oriented_patch_height_admissible_of_subset hg hF hU e he.1 hVU R hgood
      n k (centers k) hk⟩

theorem rank_one_boundary_exists_admissible_patch
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord} {b : Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hbU : b ∈ U) (n : ℕ) (hb : b ∈ frontier (accumulatingDisk n))
    (e : Ambient) (he : IsUnitNormalAt F e b)
    (hrank : (secondFundamental F e b).rank = 1) (kmin : ℕ) :
    ∃ R : OrientationLabel, ∃ k ≥ kmin, ∃ c ∈ orientedExteriorCenters n k R,
      orientedClosedPatch n k R c ⊆ U ∧
      PatchAdmissibleHeight
        (affinePullbackMetric g c (orientedPatchScale n k R • R.val))
        (height (affinePullbackImmersion F c (orientedPatchScale n k R • R.val)) e) := by
  obtain ⟨R, centers, hcenters, _, hgood⟩ :=
    rank_one_boundary_eventually_admissible_patches hg hF hU hbU n hb e he hrank
  obtain ⟨k, hk⟩ := (hgood.and (eventually_ge_atTop kmin)).exists
  exact ⟨R, k, hk.2, centers k, hcenters k, hk.1.1, hk.1.2⟩

theorem immersion_containing_disk_has_admissible_patch
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (n : ℕ) (hDU : accumulatingDisk n ⊆ U)
    (hK : ∀ p ∈ roundOpenDisk (accumulatingCenter n) (accumulatingRadius n),
      gaussianCurvature g p < 0)
    (hKb : ∀ p ∈ frontier (accumulatingDisk n), gaussianCurvature g p = 0)
    (kmin : ℕ) :
    ∃ b ∈ frontier (accumulatingDisk n), ∃ e : Ambient,
      IsUnitNormalAt F e b ∧ secondFundamental F e b ≠ 0 ∧
      (secondFundamental F e b).rank = 1 ∧
      ∃ R : OrientationLabel, ∃ k ≥ kmin, ∃ c ∈ orientedExteriorCenters n k R,
        orientedClosedPatch n k R c ⊆ U ∧
        PatchAdmissibleHeight
          (affinePullbackMetric g c (orientedPatchScale n k R • R.val))
          (height (affinePullbackImmersion F c (orientedPatchScale n k R • R.val)) e) := by
  obtain ⟨b, hb, e, he, hne, hrank⟩ :=
    exists_roundDisk_boundary_unitNormal_rank_one hg hF hU (accumulatingRadius_pos n)
      hDU hK hKb
  have hbD : b ∈ accumulatingDisk n :=
    ((mem_frontier_roundClosedDisk_iff (accumulatingCenter n) b
      (accumulatingRadius_pos n)).mp hb).le
  refine ⟨b, hb, e, he, hne, hrank, ?_⟩
  exact rank_one_boundary_exists_admissible_patch hg hF hU (hDU hbD) n hb e he hrank kmin

theorem every_local_immersion_has_admissible_oriented_patch
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (h0 : (0 : Coord) ∈ U)
    (hK : ∀ n : ℕ, ∀ p ∈ roundOpenDisk (accumulatingCenter n) (accumulatingRadius n),
      gaussianCurvature g p < 0)
    (hKb : ∀ n : ℕ, ∀ p ∈ frontier (accumulatingDisk n), gaussianCurvature g p = 0)
    (nmin kmin : ℕ) :
    ∃ n ≥ nmin, ∃ b ∈ frontier (accumulatingDisk n), ∃ e : Ambient,
      IsUnitNormalAt F e b ∧ secondFundamental F e b ≠ 0 ∧
      (secondFundamental F e b).rank = 1 ∧
      ∃ R : OrientationLabel, ∃ k ≥ kmin, ∃ c ∈ orientedExteriorCenters n k R,
        orientedClosedPatch n k R c ⊆ U ∧
        PatchAdmissibleHeight
          (affinePullbackMetric g c (orientedPatchScale n k R • R.val))
          (height (affinePullbackImmersion F c (orientedPatchScale n k R • R.val)) e) := by
  have hdisks := eventually_accumulatingDisk_subset (hU.mem_nhds h0)
  obtain ⟨n, hn⟩ := (hdisks.and (eventually_ge_atTop nmin)).exists
  exact ⟨n, hn.2, immersion_containing_disk_has_admissible_patch hg hF hU n hn.1
    (hK n) (hKb n) kmin⟩

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_AssembledImmersionHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation SmoothLocal.ODE

theorem every_assembled_local_immersion_has_actual_local_height
    {epsilon : ℝ} (he : 0 < epsilon) (eta : PatchAddress → SymmetricPerturbation)
    (hsmall : ∀ a, eta a ∈ patchTensorBudgetNeighborhood epsilon a)
    (hlocal : ∀ a, ∀ q ∈ modelSquare, (localPatchMetric initialAssemblyMetric eta a q).PosDef)
    {U : Set Coord} (hU : IsOpen U) (hUS : U ⊆ square) (h0 : (0 : Coord) ∈ U)
    (F : Coord → Ambient) (hF : IsometricOn (assembledPatchMetric initialAssemblyMetric eta) F U)
    (nmin kmin : ℕ) :
    ∃ a : PatchAddress, nmin ≤ a.1 ∧ kmin ≤ a.2.1 ∧
      ∃ b ∈ frontier (accumulatingDisk a.1), ∃ e : Ambient,
        IsUnitNormalAt F e b ∧ secondFundamental F e b ≠ 0 ∧
        (secondFundamental F e b).rank = 1 ∧ patchAddressCarrier a ⊆ U ∧
        PatchAdmissibleHeight (localPatchMetric initialAssemblyMetric eta a)
          (height (affinePullbackImmersion F (patchAddressCenter a) (patchAddressMatrix a)) e) := by
  let g := assembledPatchMetric initialAssemblyMetric eta
  have hg : SmoothPositiveOn g square := assembledPatchMetric_smoothPositive_of_local_metrics
    he initialAssemblyMetric_smoothPositiveOn eta hsmall hlocal
  have hgU : SmoothPositiveOn g U :=
    ⟨fun i j => (hg.1 i j).mono hUS,fun p hp => hg.2 p (hUS hp)⟩
  have hcurv (n : ℕ) (p : Coord) (hp : p ∈ accumulatingDisk n) :
      gaussianCurvature g p = gaussianCurvature initialAssemblyMetric p :=
    assembledPatchMetric_curvature_on_disk_of_local_metrics he initialAssemblyMetric_smoothPositiveOn
      coordinate_square_isOpen eta hsmall hlocal n hp (accumulatingDisk_subset_square n hp)
  have hK (n : ℕ) (p : Coord)
      (hp : p ∈ roundOpenDisk (accumulatingCenter n) (accumulatingRadius n)) : gaussianCurvature g p < 0 := by
    have hi : p ∈ interior (accumulatingDisk n) := by
      simpa only [accumulatingDisk,interior_roundClosedDisk _ (accumulatingRadius_pos n)] using hp
    rw [hcurv n p (interior_subset hi)]
    exact initialAssemblyMetric_negative_on_disk_interior n hi
  have hKb (n : ℕ) (p : Coord) (hp : p ∈ frontier (accumulatingDisk n)) : gaussianCurvature g p = 0 := by
    have hdisk : p ∈ accumulatingDisk n := by
      simpa only [(accumulatingDisk_isCompact n).isClosed.closure_eq] using frontier_subset_closure hp
    rw [hcurv n p hdisk]
    exact initialAssemblyMetric_zero_on_disk_frontier n hp
  obtain ⟨n,hn,b,hb,e,hen,hne,hrank,R,k,hk,c,hc,hpatch,hadm⟩ :=
    every_local_immersion_has_admissible_oriented_patch hgU hF hU h0 hK hKb nmin kmin
  let a : PatchAddress := ⟨n,k,R,c,hc⟩
  refine ⟨a,hn,hk,b,hb,e,hen,hne,hrank,hpatch,?_⟩
  exact assembledPatchMetric_admissible_local initialAssemblyMetric eta a hadm

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_SelectedPatchObstructions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

theorem selectedPatchTensor_spec (a : PatchAddress) :
    selectedPatchTensor a ∈ patchTensorBudgetNeighborhood 1 a ∧
    selectedPatchTensor a ∈ metricPatchSet (patchAddressInitialMetric a) (patchAddressAmplitude a) ∧
    SmoothPositiveOn (perturbedMetric (patchAddressInitialMetric a) (selectedPatchTensor a))
      patchAddressModelDomain ∧
    ∀ z : Coord → ℝ,
      ¬ PatchAdmissibleHeight (perturbedMetric (patchAddressInitialMetric a) (selectedPatchTensor a)) z :=
  Classical.choose_spec (exists_obstructing_patch_tensor a)

theorem selectedPatchTensor_small (a : PatchAddress) :
    selectedPatchTensor a ∈ patchTensorBudgetNeighborhood 1 a :=
  (selectedPatchTensor_spec a).1

theorem selected_local_metric_eq (a : PatchAddress) :
    localPatchMetric initialAssemblyMetric selectedPatchTensor a =
      perturbedMetric (patchAddressInitialMetric a) (selectedPatchTensor a) := rfl

theorem selectedPatchTensor_local_positive (a : PatchAddress) (q : Coord) (hq : q ∈ modelSquare) :
    (localPatchMetric initialAssemblyMetric selectedPatchTensor a q).PosDef := by
  rw [selected_local_metric_eq]
  exact (selectedPatchTensor_spec a).2.1.1 q hq

theorem selectedPatchTensor_local_no_height (a : PatchAddress) :
    ∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (localPatchMetric initialAssemblyMetric selectedPatchTensor a) z := by
  rw [selected_local_metric_eq]
  exact (selectedPatchTensor_spec a).2.2.2

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_FinalMetric
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

theorem counterexampleMetric_smoothPositive :
    SmoothPositiveOn counterexampleMetric square :=
  assembledPatchMetric_smoothPositive_of_local_metrics (by norm_num : (0 : ℝ) < 1)
    initialAssemblyMetric_smoothPositiveOn selectedPatchTensor selectedPatchTensor_small
    selectedPatchTensor_local_positive

theorem counterexampleMetric_no_local_isometric_immersion
    {U : Set Coord} (hU : IsOpen U) (hUS : U ⊆ square) (h0 : (0 : Coord) ∈ U)
    (F : Coord → Ambient) : ¬ IsometricOn counterexampleMetric F U := by
  intro hF
  obtain ⟨a,_,_,_,_,_,_,_,_,_,hadm⟩ :=
    every_assembled_local_immersion_has_actual_local_height (by norm_num : (0 : ℝ) < 1)
      selectedPatchTensor selectedPatchTensor_small selectedPatchTensor_local_positive hU hUS h0 F hF 0 0
  exact selectedPatchTensor_local_no_height a _ hadm

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_LocalDomains
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function TopologicalSpace
open scoped ContDiff Topology Manifold Matrix

namespace SmoothLocal.Geometry

section Extension
variable {E : Type*}

theorem openDomainExtend_restrict (U : Opens Coord) (F : U → E)
    (outside : E) : (fun p : U => openDomainExtend U F outside p) = F := by
  funext p
  exact openDomainExtend_apply U F outside p

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contMDiff_restrict_iff (U : Opens Coord) (F : Coord → E)
    (n : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, E) n (fun p : U => F p) ↔
      ContDiffOn ℝ n F (U : Set Coord) := by
  constructor
  · intro h p hp
    have hs := contMDiffAt_subtype_iff.mp (h ⟨p, hp⟩)
    exact hs.contDiffAt.contDiffWithinAt
  · intro h p
    apply contMDiffAt_subtype_iff.mpr
    exact ((h p p.property).contDiffAt (U.isOpen.mem_nhds p.property)).contMDiffAt

theorem mfderiv_restrict_eq_fderiv (U : Opens Coord) (F : Coord → E)
    (p : U) (hF : ContDiffAt ℝ ∞ F (p : Coord)) :
    mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, E) (fun q : U => F q) p =
      fderiv ℝ F (p : Coord) := by
  have hs : ContMDiffAt 𝓘(ℝ, Coord) 𝓘(ℝ, E) ∞
      (fun q : U => F q) p :=
    contMDiffAt_subtype_iff.mpr hF.contMDiffAt
  have hd := hs.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hc : (fun y : Coord => ((chartAt Coord p).symm y : Coord))
      =ᶠ[𝓝 (p : Coord)] (fun y : Coord => y) := by
    exact (U.chartAt_subtype_val_symm_eventuallyEq (H := Coord) (x := p)).symm
  have he : writtenInExtChartAt 𝓘(ℝ, Coord) 𝓘(ℝ, E) p
      (fun q : U => F q) =ᶠ[𝓝 (p : Coord)] F := by
    exact hc.fun_comp F
  rw [hd.mfderiv]
  change fderivWithin ℝ
    (writtenInExtChartAt 𝓘(ℝ, Coord) 𝓘(ℝ, E) p (fun q : U => F q))
    (range 𝓘(ℝ, Coord)) (p : Coord) = _
  rw [ModelWithCorners.range_eq_univ, fderivWithin_univ]
  exact he.fderiv_eq

end Extension

theorem localIsometric_restrict_iff (g : MetricField) (U : Opens Coord)
    (F : Coord → Ambient) :
    LocalIsometric g U (fun p : U => F p) ↔ IsometricOn g F (U : Set Coord) := by
  constructor
  · rintro ⟨hF, he⟩
    have hc := (contMDiff_restrict_iff U F ∞).mp hF
    refine ⟨hc, ?_⟩
    intro p hp v w
    have hd := mfderiv_restrict_eq_fderiv U F ⟨p, hp⟩
      ((hc p hp).contDiffAt (U.isOpen.mem_nhds hp))
    have hinner := he ⟨p, hp⟩ v w
    rw [hd] at hinner
    exact hinner
  · rintro ⟨hF, he⟩
    refine ⟨(contMDiff_restrict_iff U F ∞).mpr hF, ?_⟩
    intro p v w
    rw [mfderiv_restrict_eq_fderiv U F p
      ((hF p p.property).contDiffAt (U.isOpen.mem_nhds p.property))]
    exact he p p.property v w

theorem localIsometric_extend_iff (g : MetricField) (U : Opens Coord)
    (F : U → Ambient) (outside : Ambient) :
    LocalIsometric g U F ↔ IsometricOn g (openDomainExtend U F outside) U := by
  rw [← localIsometric_restrict_iff, openDomainExtend_restrict]

theorem localSmoothPositive_restrict_iff (U : Opens Coord) (g : MetricField) :
    LocalSmoothPositive U (fun p => g p) ↔ SmoothPositiveOn g U := by
  constructor
  · rintro ⟨hs, hp⟩
    exact ⟨fun i j => (contMDiff_restrict_iff U (fun p => g p i j) ∞).mp (hs i j),
      fun p h => hp ⟨p, h⟩⟩
  · rintro ⟨hs, hp⟩
    exact ⟨fun i j => (contMDiff_restrict_iff U (fun p => g p i j) ∞).mpr (hs i j),
      fun p => hp p p.property⟩

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set TopologicalSpace
open scoped ContDiff Topology Manifold Matrix

namespace SmoothLocal.Geometry

theorem counterexampleMetric_local_smoothPositive :
    LocalSmoothPositive coordinateSquareOpen (fun p => counterexampleMetric p) :=
  (localSmoothPositive_restrict_iff coordinateSquareOpen counterexampleMetric).mpr
    counterexampleMetric_smoothPositive

theorem counterexampleMetric_no_subtype_isometric_immersion
    (U : Opens Coord) (hUS : (U : Set Coord) ⊆ square)
    (h0 : (0 : Coord) ∈ U) (F : U → Ambient) :
    ¬ LocalIsometric counterexampleMetric U F := by
  intro hF
  exact counterexampleMetric_no_local_isometric_immersion U.isOpen hUS h0
    (openDomainExtend U F 0) ((localIsometric_extend_iff _ U F 0).mp hF)

theorem exists_local_metric_without_local_immersion_oai :
    ∃ g : coordinateSquareOpen → Matrix (Fin 2) (Fin 2) ℝ,
      LocalSmoothPositive coordinateSquareOpen g ∧
      ∀ U : Opens Coord, ∀ hUS : (U : Set Coord) ⊆ square,
        (0 : Coord) ∈ U → ∀ F : U → Ambient,
          ¬ (ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ F ∧
            ∀ p : U, ∀ v w : Coord,
              (inner ℝ : Ambient → Ambient → ℝ) (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) F p v)
                (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) F p w) =
                  v ⬝ᵥ (g ⟨p, hUS p.property⟩ *ᵥ w)) := by
  refine ⟨fun p => counterexampleMetric p, counterexampleMetric_local_smoothPositive, ?_⟩
  intro U hUS h0 F hF
  exact counterexampleMetric_no_subtype_isometric_immersion U hUS h0 F hF

end SmoothLocal.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion_oai := @OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion_oai
