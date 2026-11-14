-- Prove2me | solution 1 for OAI.KadisonKastler.constructed_exists_normalizing_representation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:15:55.810953+00:00
-- url     : https://prove2.me/submissions/7cb11934-69d4-42e3-bc06-86bdee240100

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K020
import Definitions.Def_Q260K023
import Theorems.Thm_OAI_KadisonKastler_constructed_exists_normalizer_near_mean

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryImprovement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The quadratic step in boundary cocycle correction

Only the structural properties of the boundary mean occur here.  The mean
need not be normal.  Covariance cancellation and polar normalization give
the quadratic improvement used in the measurable iteration.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

namespace BimoduleMean

variable {ι : B →⋆ₐ[ℂ] A} (m : BimoduleMean ι)

/-- The linear terms cancel exactly in the centered product. -/
theorem covariance (x y : A) :
    m.toCLM (x * y) - m.toCLM x * m.toCLM y =
      m.toCLM ((x - ι (m.toCLM x)) * (y - ι (m.toCLM y))) := by
  simp only [sub_mul, mul_sub, map_sub, m.map_right, m.map_left, m.fixed]
  noncomm_ring

/-- Contractivity of the mean bounds the covariance by its two residuals. -/
theorem norm_covariance_le (x y : A) :
    ‖m.toCLM (x * y) - m.toCLM x * m.toCLM y‖ ≤
      ‖x - ι (m.toCLM x)‖ * ‖y - ι (m.toCLM y)‖ := by
  rw [m.covariance]
  exact (m.norm_le _).trans (norm_mul_le _ _)

/-- Averaging preserves the error from a field independent of the mean variable. -/
theorem norm_sub_le (x : A) (b : B) {e : ℝ} (h : ‖x - ι b‖ ≤ e) :
    ‖m.toCLM x - b‖ ≤ e := by
  rw [← m.fixed b, ← map_sub]
  exact (m.norm_le _).trans h

/-- The residual from the average is at most twice the original error. -/
theorem norm_residual_le (x : A) (b : B) {e : ℝ} (h : ‖x - ι b‖ ≤ e) :
    ‖x - ι (m.toCLM x)‖ ≤ 2 * e := by
  calc
    _ ≤ ‖x - ι b‖ + ‖ι b - ι (m.toCLM x)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ e + e := add_le_add h (by
      rw [← map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le ι _).trans
        (by simpa only [norm_sub_rev] using m.norm_sub_le x b h))
    _ = _ := by ring

/-- Two residuals bounded by `2e` give the quadratic covariance bound. -/
theorem norm_covariance_le_four_mul_sq (x y : A) {e : ℝ} (he : 0 ≤ e)
    (hx : ‖x - ι (m.toCLM x)‖ ≤ 2 * e)
    (hy : ‖y - ι (m.toCLM y)‖ ≤ 2 * e) :
    ‖m.toCLM (x * y) - m.toCLM x * m.toCLM y‖ ≤ 4 * e ^ 2 := by
  calc
    _ ≤ ‖x - ι (m.toCLM x)‖ * ‖y - ι (m.toCLM y)‖ := m.norm_covariance_le x y
    _ ≤ (2 * e) * (2 * e) := mul_le_mul hx hy (norm_nonneg _) (by positivity)
    _ = _ := by ring

end BimoduleMean

section Transport

variable {G : Type*} [Group G]

/-- The transport construction has an exact factorization even when `V`
is only an approximate cocycle. -/
theorem boundaryTransport_factor (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : G → unitary B) (g h t : G) :
    boundaryTransport α V (g * h) t =
      boundaryTransport α V g t * α g (boundaryTransport α V h (g⁻¹ * t)) := by
  have hcancel : α g (star (V (g⁻¹ * t) : B)) * α g (V (g⁻¹ * t) : B) = 1 := by
    rw [← map_mul, Unitary.star_mul_self_of_mem (V (g⁻¹ * t)).property, map_one]
  simp only [boundaryTransport, map_mul, StarAlgEquiv.mul_apply, mul_inv_rev, mul_assoc]
  rw [← mul_assoc (α g (star (V (g⁻¹ * t) : B))), hcancel, one_mul]

/-- The pointwise distance from the transport field to the original
unitary is bounded by the original cocycle defect. -/
theorem norm_boundaryTransport_sub_le (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : G → unitary B) {e : ℝ}
    (hdefect : ∀ g h, ‖(V g : B) * α g (V h : B) - (V (g * h) : B)‖ ≤ e)
    (g t : G) : ‖boundaryTransport α V g t - (V g : B)‖ ≤ e := by
  let W : unitary B := Unitary.map (StarMonoidHom.ofClass (α g)) (V (g⁻¹ * t))
  have hcancel : α g (star (V (g⁻¹ * t) : B)) * (W : B) = 1 := by
    change α g (star (V (g⁻¹ * t) : B)) * α g (V (g⁻¹ * t) : B) = 1
    rw [← map_mul, Unitary.star_mul_self_of_mem (V (g⁻¹ * t)).property, map_one]
  have heq : (boundaryTransport α V g t - (V g : B)) * (W : B) =
      (V t : B) - (V g : B) * α g (V (g⁻¹ * t) : B) := by
    rw [sub_mul, boundaryTransport, mul_assoc, hcancel, mul_one]
    rfl
  calc
    ‖boundaryTransport α V g t - (V g : B)‖ =
        ‖(boundaryTransport α V g t - (V g : B)) * (W : B)‖ :=
      (CStarRing.norm_mul_coe_unitary _ W).symm
    _ = ‖(V t : B) - (V g : B) * α g (V (g⁻¹ * t) : B)‖ := congrArg norm heq
    _ = ‖(V g : B) * α g (V (g⁻¹ * t) : B) - (V t : B)‖ := norm_sub_rev _ _
    _ ≤ e := by simpa only [mul_inv_cancel_left] using hdefect g (g⁻¹ * t)

end Transport

section Improvement

variable {ι : B →⋆ₐ[ℂ] A} (m : BimoduleMean ι)
variable [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
/-- The operator-norm defect of the averaged family is quadratic. -/
theorem BimoduleMean.norm_averaged_defect_le_four_mul_sq
    {G : Type*} [Group G]
    (α : G → B ≃⋆ₐ[ℂ] B) (fieldAction : G → A ≃⋆ₐ[ℂ] A)
    (hequiv : ∀ g x, m.toCLM (fieldAction g x) = α g (m.toCLM x))
    (hι : ∀ g b, fieldAction g (ι b) = ι (α g b))
    (X : G → unitary A) (V : G → unitary B)
    (hfactor : ∀ g h, (X (g * h) : A) = (X g : A) * fieldAction g (X h : A))
    {e : ℝ} (he : 0 ≤ e) (hXV : ∀ g, ‖(X g : A) - ι (V g : B)‖ ≤ e)
    (g h : G) :
    ‖m.toCLM (X (g * h) : A) -
      m.toCLM (X g : A) * α g (m.toCLM (X h : A))‖ ≤ 4 * e ^ 2 := by
  rw [hfactor, ← hequiv]
  apply m.norm_covariance_le_four_mul_sq _ _ he
  · exact m.norm_residual_le _ _ (hXV g)
  · rw [hequiv, ← hι, ← map_sub, StarAlgEquiv.norm_map]
    exact m.norm_residual_le _ _ (hXV h)

end Improvement

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_QuadraticIteration
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Convergence of the quadratic boundary correction

The constants are the ones used by the cocycle averaging step: defect
`e` improves to `16e²`, at displacement at most `e + 4e²`.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

/-- Iterating the quadratic improvement gives an exact solution within
`2e`, where `e ≤ 1/64` is the original defect. -/
theorem exists_zero_of_quadratic_improvement
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (d : X → ℝ) (hd : Continuous d) (hd0 : ∀ x, 0 ≤ d x)
    (hstep : ∀ x, d x ≤ 1 / 64 → ∃ y,
      d y ≤ 16 * (d x) ^ 2 ∧ dist x y ≤ d x + 4 * (d x) ^ 2)
    (x₀ : X) (hx₀ : d x₀ ≤ 1 / 64) :
    ∃ y, d y = 0 ∧ dist x₀ y ≤ 2 * d x₀ := by
  let S := {x : X // d x ≤ 1 / 64}
  have hquarter (x : S) : 16 * (d x.val) ^ 2 ≤ d x.val / 4 := by
    have hp := hd0 x.val
    have hb := x.property
    nlinarith
  let next : S → S := fun x =>
    ⟨Classical.choose (hstep x.val x.property),
      ((Classical.choose_spec (hstep x.val x.property)).1.trans
        (hquarter x)).trans (by have hx := x.property; linarith)⟩
  have hnext (x : S) : d (next x).val ≤ d x.val / 4 ∧
      dist x.val (next x).val ≤ d x.val + 4 * (d x.val) ^ 2 := by
    exact ⟨(Classical.choose_spec (hstep x.val x.property)).1.trans (hquarter x),
      (Classical.choose_spec (hstep x.val x.property)).2⟩
  let s : ℕ → S := fun n => (next^[n]) ⟨x₀, hx₀⟩
  have hs0 : (s 0).val = x₀ := rfl
  have hsnext (n : ℕ) : s (n + 1) = next (s n) := by
    exact Function.iterate_succ_apply' next n ⟨x₀, hx₀⟩
  have hdecay (n : ℕ) : d (s n).val ≤ d x₀ * (1 / 4 : ℝ) ^ n := by
    induction n with
    | zero => simp only [hs0, pow_zero, mul_one, le_refl]
    | succ n ih =>
      rw [hsnext]
      calc
        _ ≤ d (s n).val / 4 := (hnext (s n)).1
        _ ≤ (d x₀ * (1 / 4 : ℝ) ^ n) / 4 := div_le_div_of_nonneg_right ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  have hdist (n : ℕ) : dist (s n).val (s (n + 1)).val ≤
      (17 / 16 * d x₀) * (1 / 4 : ℝ) ^ n := by
    rw [hsnext]
    calc
      _ ≤ d (s n).val + 4 * (d (s n).val) ^ 2 := (hnext (s n)).2
      _ ≤ 17 / 16 * d (s n).val := by
        have hp := hd0 (s n).val
        have hb := (s n).property
        nlinarith
      _ ≤ 17 / 16 * (d x₀ * (1 / 4 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left (hdecay n) (by norm_num)
      _ = _ := by ring
  have hc : CauchySeq (fun n => (s n).val) :=
    cauchySeq_of_le_geometric (1 / 4) (17 / 16 * d x₀) (by norm_num) hdist
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  have hdz : Tendsto (fun n => d (s n).val) atTop (𝓝 0) := by
    have hgeom : Tendsto (fun n : ℕ => d x₀ * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)))
    exact squeeze_zero (fun n => hd0 (s n).val) hdecay hgeom
  have hdy : d y = 0 := tendsto_nhds_unique (hd.continuousAt.tendsto.comp hy) hdz
  refine ⟨y, hdy, ?_⟩
  have hb := dist_le_of_le_geometric_of_tendsto₀ (1 / 4)
    (17 / 16 * d x₀) (by norm_num) hdist hy
  rw [hs0] at hb
  norm_num at hb
  have hp := hd0 x₀
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CocycleMetric
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The complete metric space of uniformly bounded unitary families

The cocycle defect is continuous for the uniform norm. This supplies the
metric-space part of the boundary correction iteration.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G B : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [CStarAlgebra B]

local instance instCompleteSpaceSubtypeBoundedContinuousFunctionMemSubmonoidUnitary_solutions_rf2b015_1 : CompleteSpace (unitary (G →ᵇ B)) := isClosed_unitary.completeSpace_coe
theorem unitaryCocycleDefect_nonneg (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) : 0 ≤ unitaryCocycleDefect α V := norm_nonneg _

theorem unitaryCocycleDefect_eq_zero_iff (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) : unitaryCocycleDefect α V = 0 ↔
      ∀ g h, V.val g * α g (V.val h) = V.val (g * h) := by
  rw [unitaryCocycleDefect, norm_eq_zero]
  constructor
  · intro h g k
    exact sub_eq_zero.mp (congrArg (fun f : (G × G) →ᵇ B => f (g, k)) h)
  · intro h
    ext ⟨g, k⟩
    exact sub_eq_zero.mpr (h g k)

private theorem unitary_cocycle_error_difference_le
    (α : G →* (B ≃⋆ₐ[ℂ] B)) (V W : unitary (G →ᵇ B)) (g h : G) :
    ‖unitaryCocycleError α V (g, h) - unitaryCocycleError α W (g, h)‖ ≤
      3 * ‖V.val - W.val‖ := by
  let c := ‖V.val - W.val‖
  have he (g : G) : ‖V.val g - W.val g‖ ≤ c :=
    (V.val - W.val).norm_coe_le_norm g
  have hv : ‖α g (V.val h)‖ ≤ 1 :=
    norm_unitary_le_one (Unitary.map (StarMonoidHom.ofClass (α g)) (unitaryFamilyEval V h))
  have hw : ‖W.val g‖ ≤ 1 := norm_unitary_le_one (unitaryFamilyEval W g)
  have hα : ‖α g (V.val h - W.val h)‖ ≤ c := by
    have hi : ‖α g (V.val h - W.val h)‖ = ‖V.val h - W.val h‖ :=
      NonUnitalStarAlgHom.norm_map (α g).toStarAlgHom (α g).injective _
    rw [hi]
    exact he h
  change ‖(V.val g * α g (V.val h) - V.val (g * h)) -
    (W.val g * α g (W.val h) - W.val (g * h))‖ ≤ 3 * c
  have hid : (V.val g * α g (V.val h) - V.val (g * h)) -
      (W.val g * α g (W.val h) - W.val (g * h)) =
      (V.val g - W.val g) * α g (V.val h) +
        W.val g * α g (V.val h - W.val h) - (V.val (g * h) - W.val (g * h)) := by
    rw [map_sub]
    noncomm_ring
  rw [hid]
  calc
    _ ≤ ‖(V.val g - W.val g) * α g (V.val h)‖ +
        ‖W.val g * α g (V.val h - W.val h)‖ + ‖V.val (g * h) - W.val (g * h)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ c * 1 + 1 * c + c := by
      exact add_le_add (add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul (he g) hv (norm_nonneg _) (norm_nonneg _)))
        ((norm_mul_le _ _).trans (mul_le_mul hw hα (norm_nonneg _) (by norm_num)))) (he _)
    _ = _ := by ring

theorem unitaryCocycleError_lipschitz (α : G →* (B ≃⋆ₐ[ℂ] B)) :
    LipschitzWith 3 (unitaryCocycleError α) := by
  apply LipschitzWith.of_dist_le_mul
  intro V W
  simp only [Subtype.dist_eq, dist_eq_norm]
  change ‖unitaryCocycleError α V - unitaryCocycleError α W‖ ≤
    (3 : ℝ) * ‖V.val - W.val‖
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  rintro ⟨g, h⟩
  exact unitary_cocycle_error_difference_le α V W g h

theorem continuous_unitaryCocycleDefect (α : G →* (B ≃⋆ₐ[ℂ] B)) :
    Continuous (unitaryCocycleDefect α) :=
  (unitaryCocycleError_lipschitz α).continuous.norm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryBoundedTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded transport fields and the correction step

For an action on a C-star algebra, the transport fields are actual bounded
unitary families.  An equivariant bimodule mean therefore gives the quadratic
step in the complete metric space of unitary families.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction CStarAlgebra

noncomputable section

variable {G B : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [CStarAlgebra B]

local instance boundaryBoundedComplete_rf2b015_1 : CompleteSpace (unitary (G →ᵇ B)) :=
  isClosed_unitary.completeSpace_coe
attribute [local instance] OAI.KadisonKastler.boundaryBoundedStarOrder
/-- The translation action agrees with the original action on constant fields. -/
theorem boundaryTranslate_constant (α : G →* (B ≃⋆ₐ[ℂ] B)) (g : G) (b : B) :
    boundaryTranslate α g (boundaryConstant (G := G) b) =
      boundaryConstant (G := G) (α g b) := by
  ext t
  rfl

/-- The exact pointwise transport factorization holds in the bounded algebra. -/
theorem boundedBoundaryTransport_factor (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) (g h : G) :
    (boundedBoundaryTransport α V (g * h) : G →ᵇ B) =
      (boundedBoundaryTransport α V g : G →ᵇ B) *
        boundaryTranslate α g (boundedBoundaryTransport α V h : G →ᵇ B) := by
  ext t
  exact boundaryTransport_factor α (unitaryFamilyEval V) g h t

/-- Each pointwise defect is bounded by its actual uniform norm. -/
theorem norm_unitaryCocycleError_le (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) (g h : G) :
    ‖V.val g * α g (V.val h) - V.val (g * h)‖ ≤ unitaryCocycleDefect α V :=
  (unitaryCocycleError α V).norm_coe_le_norm (g, h)

/-- The transport family is uniformly within the actual cocycle defect of
its constant value at the given group element. -/
theorem norm_boundedBoundaryTransport_sub_le (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : unitary (G →ᵇ B)) (g : G) :
    ‖(boundedBoundaryTransport α V g : G →ᵇ B) -
      boundaryConstant (G := G) (V.val g)‖ ≤ unitaryCocycleDefect α V := by
  apply (BoundedContinuousFunction.norm_le (unitaryCocycleDefect_nonneg α V)).mpr
  intro t
  exact norm_boundaryTransport_sub_le α (unitaryFamilyEval V)
    (norm_unitaryCocycleError_le α V) g t

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizerTopology
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The closed group of unitary normalizers

Uniform limits of normalizing unitary families remain normalizing. This
provides the complete space in which the normalizer correction is iterated.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem mem_normalizerGroup_iff (P : VonNeumannAlgebra H)
    (v : unitary (H →L[ℂ] H)) : v ∈ normalizerGroup P ↔
      ∀ x ∈ P, unitaryConj v x ∈ P ∧ unitaryConj (star v) x ∈ P := by
  constructor
  · intro hv x hx
    have hf : unitaryConj v x ∈ (P : Set (H →L[ℂ] H)) := by
      rw [← hv]
      exact ⟨x, hx, rfl⟩
    have hb : unitaryConj (star v) x ∈ (P : Set (H →L[ℂ] H)) := by
      rw [← hv.symm]
      exact ⟨x, hx, rfl⟩
    exact ⟨hf, hb⟩
  · intro hv
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hv x hx).1
    · intro x hx
      exact ⟨unitaryConj (star v) x, (hv x hx).2, by
        simpa only [star_star] using unitaryConj_star_unitaryConj (star v) x⟩

theorem isClosed_normalizerGroup (P : VonNeumannAlgebra H) :
    IsClosed (normalizerGroup P : Set (unitary (H →L[ℂ] H))) := by
  have hc (x : H →L[ℂ] H) : Continuous (fun v : unitary (H →L[ℂ] H) =>
      unitaryConj v x) := by
    unfold unitaryConj
    fun_prop
  have hs (x : H →L[ℂ] H) : Continuous (fun v : unitary (H →L[ℂ] H) =>
      unitaryConj (star v) x) := (hc x).comp continuous_star
  have he : (normalizerGroup P : Set (unitary (H →L[ℂ] H))) =
      {v | ∀ x ∈ P, unitaryConj v x ∈ P ∧ unitaryConj (star v) x ∈ P} := by
    ext v
    exact mem_normalizerGroup_iff P v
  rw [he]
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    ((isClosed_algebra P).preimage (hc x)).inter ((isClosed_algebra P).preimage (hs x))

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

omit [Group G] [DiscreteTopology G] in
theorem continuous_unitaryFamilyEval (g : G) :
    Continuous (fun V : unitary (G →ᵇ (H →L[ℂ] H)) => unitaryFamilyEval V g) := by
  apply Continuous.subtype_mk
  exact (BoundedContinuousFunction.lipschitz_eval_const g).continuous.comp
    continuous_subtype_val

omit [Group G] [DiscreteTopology G] in
theorem isClosed_normalizingFamilies (P : VonNeumannAlgebra H) :
    IsClosed {V : unitary (G →ᵇ (H →L[ℂ] H)) |
      ∀ g, unitaryFamilyEval V g ∈ normalizerGroup P} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun g => (isClosed_normalizerGroup P).preimage
    (continuous_unitaryFamilyEval g)

instance normalizingFamilyCompleteSpace (P : VonNeumannAlgebra H) :
    CompleteSpace (NormalizingFamily (G := G) P) := by
  let : CompleteSpace (unitary (G →ᵇ (H →L[ℂ] H))) := isClosed_unitary.completeSpace_coe
  exact (isClosed_normalizingFamilies P).completeSpace_coe

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedNormalizerCorrection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Quadratic correction while preserving normalizers

Averages are corrected inside the algebra and its commutant before they
are multiplied. The iteration therefore takes place in the complete space
of normalizing families, not in all ambient unitary families.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

private theorem product_defect_of_near_averages_p0
    {B : Type*} [CStarAlgebra B] (u v w : unitary B) (a b c : B)
    {r s : ℝ} (hu : ‖(u : B) - a‖ ≤ r)
    (hv : ‖(v : B) - b‖ ≤ r) (hw : ‖(w : B) - c‖ ≤ r)
    (ha : ‖a‖ ≤ 1) (hprod : ‖a * b - c‖ ≤ s) :
    ‖(u : B) * (v : B) - (w : B)‖ ≤ 3 * r + s := by
  have hid : (u : B) * (v : B) - (w : B) =
      ((u : B) - a) * (v : B) + a * ((v : B) - b) + (a * b - c) + (c - (w : B)) := by
    noncomm_ring
  rw [hid]
  calc
    _ ≤ ‖((u : B) - a) * (v : B)‖ + ‖a * ((v : B) - b)‖ +
        ‖a * b - c‖ + ‖c - (w : B)‖ := by
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ r + r + s + r := by
      apply add_le_add
      · apply add_le_add
        · exact add_le_add (by simpa only [CStarRing.norm_mul_coe_unitary] using hu)
            ((norm_mul_le _ _).trans
              ((mul_le_mul ha hv (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)))
        · exact hprod
      · simpa only [norm_sub_rev] using hw
    _ = _ := by ring

private theorem scaled_normalizer_estimates_p0 {e f a : ℝ} (he : 0 ≤ e)
    (hf : f ≤ 3604 * e ^ 2) (ha : a ≤ e + 1200 * e ^ 2) :
    256 * f ≤ 16 * (256 * e) ^ 2 ∧ a ≤ 256 * e + 4 * (256 * e) ^ 2 := by
  constructor <;> nlinarith only [he, hf, ha, sq_nonneg e]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

attribute [local instance] OAI.KadisonKastler.constructedNormalizerCorrectionCStar
/-- One averaging step stays in the normalizer group and has quadratic
multiplicative defect. -/
theorem constructed_exists_normalizing_quadratic_step
    (P : VonNeumannAlgebra H) (hpub : SmallNormalizerFactorization P)
    (m : BimoduleMean (boundaryConstant (G := G) (B := H →L[ℂ] H)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate (1 : G →* ((H →L[ℂ] H) ≃⋆ₐ[ℂ]
      (H →L[ℂ] H))) g f) = m.toCLM f)
    (hpres : ∀ (Q : VonNeumannAlgebra H) (F : G →ᵇ (H →L[ℂ] H)),
      (∀ g, F g ∈ Q) → m.toCLM F ∈ Q)
    (V : unitary (G →ᵇ (H →L[ℂ] H)))
    (hV : ∀ g : G, Conjugates (unitaryFamilyEval (B := H →L[ℂ] H) V g) P P)
    (hsmall : 64 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 V < 1) :
    ∃ W : unitary (G →ᵇ (H →L[ℂ] H)),
      (∀ g : G, Conjugates (unitaryFamilyEval (B := H →L[ℂ] H) W g) P P) ∧
      unitaryCocycleDefect (B := H →L[ℂ] H) 1 W ≤ 3604 * (unitaryCocycleDefect (B := H →L[ℂ] H) 1 V) ^ 2 ∧
      dist V W ≤ unitaryCocycleDefect (B := H →L[ℂ] H) 1 V + 1200 * (unitaryCocycleDefect (B := H →L[ℂ] H) 1 V) ^ 2 := by
  let α : G →* ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)) := 1
  let X := boundedBoundaryTransport α V
  let e := unitaryCocycleDefect (B := H →L[ℂ] H) α V
  have he : 0 ≤ e := unitaryCocycleDefect_nonneg (B := H →L[ℂ] H) α V
  have hX (g t : G) : Conjugates (unitaryFamilyEval (B := H →L[ℂ] H) (X g) t) P P := by
    have h := (hV (g⁻¹ * t)).symm.trans (hV t)
    exact h
  have hnear (g t : G) : ‖(X g).val t - (unitaryFamilyEval (B := H →L[ℂ] H) V g : H →L[ℂ] H)‖ ≤ e :=
    norm_boundaryTransport_sub_le α (unitaryFamilyEval (B := H →L[ℂ] H) V)
      (norm_unitaryCocycleError_le α V) g t
  have hex (g : G) := constructed_exists_normalizer_near_mean P hpub m hpres (X g)
    (hX g) (unitaryFamilyEval (B := H →L[ℂ] H) V g) (hV g) he hsmall (hnear g)
  choose w hw hwm using hex
  let W := boundedUnitaryFamily w
  have hAnorm (g : G) : ‖m.toCLM (X g).val‖ ≤ 1 :=
    (m.norm_le _).trans (norm_unitary_le_one (X g))
  have hmean (g k : G) : ‖m.toCLM (X (g * k)).val -
      m.toCLM (X g).val * m.toCLM (X k).val‖ ≤ 4 * e ^ 2 := by
    exact m.norm_averaged_defect_le_four_mul_sq (fun g => α g) (boundaryTranslate α)
      (by intro g f; exact hm g f) (boundaryTranslate_constant α) X
      (unitaryFamilyEval (B := H →L[ℂ] H) V) (boundedBoundaryTransport_factor α V) he
      (norm_boundedBoundaryTransport_sub_le α V) g k
  have hnew (g k : G) : ‖(w g : H →L[ℂ] H) * (w k : H →L[ℂ] H) -
      (w (g * k) : H →L[ℂ] H)‖ ≤ 3604 * e ^ 2 := by
    have h := product_defect_of_near_averages_p0 (w g) (w k) (w (g * k))
      (m.toCLM (X g).val) (m.toCLM (X k).val) (m.toCLM (X (g * k)).val)
      (hwm g) (hwm k) (hwm (g * k))
      (hAnorm g) (by simpa only [norm_sub_rev] using hmean g k)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  refine ⟨W, hw, ?_, ?_⟩
  · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    rintro ⟨g, k⟩
    exact hnew g k
  · simp only [Subtype.dist_eq, dist_eq_norm]
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro g
    have hmnear := m.norm_sub_le (X g).val (V.val g)
      (norm_boundedBoundaryTransport_sub_le α V g)
    have hn := norm_sub_le_norm_sub_add_norm_sub (w g : H →L[ℂ] H)
      (m.toCLM (X g).val) (V.val g)
    have hh := hn.trans (add_le_add (hwm g) hmnear)
    change ‖V.val g - (w g : H →L[ℂ] H)‖ ≤ e + 1200 * e ^ 2
    rw [norm_sub_rev]
    exact hh.trans_eq (add_comm _ _)

/-- Uniform iteration corrects the selected normalizers to an exact group
representation, still inside the normalizer group at every parameter. -/
theorem constructed_exists_normalizing_representation_oai
    (P : VonNeumannAlgebra H) (hpub : SmallNormalizerFactorization P)
    (m : BimoduleMean (boundaryConstant (G := G) (B := H →L[ℂ] H)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate (1 : G →* ((H →L[ℂ] H) ≃⋆ₐ[ℂ]
      (H →L[ℂ] H))) g f) = m.toCLM f)
    (hpres : ∀ (Q : VonNeumannAlgebra H) (F : G →ᵇ (H →L[ℂ] H)),
      (∀ g, F g ∈ Q) → m.toCLM F ∈ Q)
    (V : unitary (G →ᵇ (H →L[ℂ] H)))
    (hV : ∀ g : G, Conjugates (unitaryFamilyEval (B := H →L[ℂ] H) V g) P P)
    (hsmall : unitaryCocycleDefect (B := H →L[ℂ] H) 1 V ≤ 1 / 16384) :
    ∃ z : G →* unitary (H →L[ℂ] H),
      (∀ g : G, Conjugates (z g) P P) ∧
      ∀ g, ‖(z g : H →L[ℂ] H) - V.val g‖ ≤ 512 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 V := by
  let d : NormalizingFamily (G := G) P → ℝ := fun X => 256 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 X.val
  have hd : Continuous d := continuous_const.mul
    ((continuous_unitaryCocycleDefect (B := H →L[ℂ] H) 1).comp continuous_subtype_val)
  have hd0 (X : NormalizingFamily (G := G) P) : 0 ≤ d X :=
    mul_nonneg (by norm_num) (unitaryCocycleDefect_nonneg (B := H →L[ℂ] H) 1 X.val)
  have hstep (X : NormalizingFamily (G := G) P) (hX : d X ≤ 1 / 64) :
      ∃ Y, d Y ≤ 16 * (d X) ^ 2 ∧ dist X Y ≤ d X + 4 * (d X) ^ 2 := by
    have he := unitaryCocycleDefect_nonneg (B := H →L[ℂ] H) 1 X.val
    have hXe : unitaryCocycleDefect (B := H →L[ℂ] H) 1 X.val ≤ 1 / 16384 := by
      change 256 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 X.val ≤ _ at hX
      linarith only [hX]
    obtain ⟨W, hW, hn, hdist⟩ := constructed_exists_normalizing_quadratic_step P hpub m hm hpres
      X.val X.property (by linarith)
    refine ⟨⟨W, hW⟩, ?_, ?_⟩
    · exact (scaled_normalizer_estimates_p0 he hn hdist).1
    · exact (scaled_normalizer_estimates_p0 he hn hdist).2
  let X₀ : NormalizingFamily (G := G) P := ⟨V, hV⟩
  obtain ⟨Y, hY, hdist⟩ := exists_zero_of_quadratic_improvement d hd hd0 hstep X₀
    (by change 256 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 V ≤ _; linarith)
  have hzero : unitaryCocycleDefect (B := H →L[ℂ] H) 1 Y.val = 0 := by
    change 256 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 Y.val = 0 at hY
    linarith
  have hlaw := (unitaryCocycleDefect_eq_zero_iff (B := H →L[ℂ] H) 1 Y.val).mp hzero
  let z : G →* unitary (H →L[ℂ] H) :=
    { toFun := unitaryFamilyEval (B := H →L[ℂ] H) Y.val
      map_one' := by
        apply mul_left_cancel (a := unitaryFamilyEval (B := H →L[ℂ] H) Y.val 1)
        apply Subtype.ext
        have h := hlaw 1 1
        simp only [MonoidHom.one_apply, StarAlgEquiv.one_apply, one_mul] at h
        exact h
      map_mul' g k := by
        apply Subtype.ext
        exact (hlaw g k).symm }
  refine ⟨z, Y.property, ?_⟩
  intro g
  have hn := (V.val - Y.val.val).norm_coe_le_norm g
  have hb : ‖V.val - Y.val.val‖ ≤ 512 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 V := by
    have hh : ‖V.val - Y.val.val‖ ≤
        2 * (256 * unitaryCocycleDefect (B := H →L[ℂ] H) 1 V) := by
      change dist V Y.val ≤ _ at hdist
      simpa only [d, X₀, Subtype.dist_eq, dist_eq_norm] using hdist
    linarith
  change ‖Y.val.val g - V.val g‖ ≤ _
  rw [norm_sub_rev]
  exact hn.trans hb

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.constructed_exists_normalizing_representation_oai.{u_1, u_2} := @OAI.KadisonKastler.constructed_exists_normalizing_representation_oai.{u_1, u_2}
