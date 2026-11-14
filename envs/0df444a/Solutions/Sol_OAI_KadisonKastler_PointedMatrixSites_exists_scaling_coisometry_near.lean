-- Prove2me | solution 1 for OAI.KadisonKastler.PointedMatrixSites.exists_scaling_coisometry_near
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:27:22.433731+00:00
-- url     : https://prove2.me/submissions/466342d5-b03b-4717-a54c-4f480c73b39a

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
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
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Nat
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.RootsOfUnity.Complex
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
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K034
import Theorems.Thm_OAI_KadisonKastler_PointedMatrixSites_twoRatio_centralizer_diffuse
import Theorems.Thm_OAI_KadisonKastler_exists_state_scaling_coisometry

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductStateCentralizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The centralizer of an infinite product state is irreducible

The proof uses only dense local vectors and state-preserving local swaps
which move a local observable to an independent set of sites. These are
the finite-site properties of the two-ratio tensor product in section 6.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_productVectorState_le (Ω : H) (hΩ : ‖Ω‖ = 1) (T : H →L[ℂ] H) :
    ‖productVectorState Ω T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖Ω‖ * ‖T Ω‖ := norm_inner_le_norm _ _
    _ ≤ ‖Ω‖ * (‖T‖ * ‖Ω‖) := mul_le_mul_of_nonneg_left (T.le_opNorm Ω) (norm_nonneg Ω)
    _ = ‖T‖ := by rw [hΩ]; ring

/-- State centralization and commutation with `x` allow a local observable
to be moved by the swap while leaving its pairing with `x` unchanged. -/
theorem productVectorState_swap (D : VonNeumannAlgebra H) (Ω : H)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ D)
    (hcentral : ProductStateCentralizes D Ω u)
    (a x : H →L[ℂ] H) (ha : a ∈ D) (hx : x ∈ D)
    (hcomm : (u : H →L[ℂ] H) * x = x * u) :
    productVectorState Ω (unitaryConj u a * x) = productVectorState Ω (a * x) := by
  have hxu : star (u : H →L[ℂ] H) * x * u = x := by
    calc
      _ = star (u : H →L[ℂ] H) * (x * u) := mul_assoc _ _ _
      _ = star (u : H →L[ℂ] H) * (u * x) := by rw [← hcomm]
      _ = x := by rw [← mul_assoc, Unitary.star_mul_self_of_mem u.property, one_mul]
  calc
    _ = productVectorState Ω ((u : H →L[ℂ] H) * (a * star (u : H →L[ℂ] H) * x)) := by
      simp only [unitaryConj, mul_assoc]
    _ = productVectorState Ω ((a * star (u : H →L[ℂ] H) * x) * u) :=
      hcentral _ (D.mul_mem (D.mul_mem ha (D.toStarSubalgebra.star_mem' hu)) hx)
    _ = productVectorState Ω (a * x) := by rw [mul_assoc a, mul_assoc a, hxu]

omit [CompleteSpace H] in
/-- A vector-functional error only sees the vector error in the right factor. -/
theorem productVectorState_mul_error (Ω : H) (hΩ : ‖Ω‖ = 1)
    (a x y : H →L[ℂ] H) :
    ‖productVectorState Ω (a * x) - productVectorState Ω (a * y)‖ ≤
      ‖a‖ * ‖(x - y) Ω‖ := by
  calc
    _ = ‖inner ℂ Ω (a ((x - y) Ω))‖ := by
      simp only [productVectorState, mul_apply_eq_comp, sub_apply, map_sub, inner_sub_right]
    _ ≤ ‖Ω‖ * ‖a ((x - y) Ω)‖ := norm_inner_le_norm _ _
    _ ≤ ‖Ω‖ * (‖a‖ * ‖(x - y) Ω‖) :=
      mul_le_mul_of_nonneg_left (a.le_opNorm _) (norm_nonneg Ω)
    _ = ‖a‖ * ‖(x - y) Ω‖ := by rw [hΩ, one_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductStateIrreducible
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Local independent swaps force scalar relative commutant -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace LocalProductSwaps

variable {D : VonNeumannAlgebra H} {Ω : H} (L : LocalProductSwaps D Ω)

/-- Factorization of the vector state against every local observable. -/
theorem local_factorization (hΩ : ‖Ω‖ = 1) (x : H →L[ℂ] H) (hx : x ∈ D)
    (hcomm : ∀ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ D →
      ProductStateCentralizes D Ω u → (u : H →L[ℂ] H) * x = x * u)
    (k : ℕ) (a : L.localAlgebra k) :
    productVectorState Ω ((a : H →L[ℂ] H) * x) =
      productVectorState Ω a * productVectorState Ω x := by
  apply eq_of_sub_eq_zero
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  simp only [zero_add]
  let δ := ε / (2 * ‖(a : H →L[ℂ] H)‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := Metric.mem_closure_iff.mp (L.dense (x Ω)) δ hδ
  have herr : ‖(x - (p.2 : H →L[ℂ] H)) Ω‖ < δ := by
    simpa only [dist_eq_norm, sub_apply, norm_sub_rev] using hp
  obtain ⟨u, hu, hc, hi⟩ := L.independent_swap k a p.1
  let b : H →L[ℂ] H := p.2
  let c : H →L[ℂ] H := unitaryConj u a
  have hs : productVectorState Ω (c * x) = productVectorState Ω (a * x) :=
    productVectorState_swap D Ω u hu hc a x (L.local_le k a.property) hx (hcomm u hu hc)
  have hi' : productVectorState Ω (c * b) =
      productVectorState Ω a * productVectorState Ω b := hi p.2
  have he : productVectorState Ω (a * x) -
      productVectorState Ω a * productVectorState Ω x =
      (productVectorState Ω (c * x) - productVectorState Ω (c * b)) +
        productVectorState Ω a * (productVectorState Ω b - productVectorState Ω x) := by
    rw [hs, hi']
    ring
  have hv : ‖productVectorState Ω b - productVectorState Ω x‖ ≤ ‖(x - b) Ω‖ := by
    calc
      _ = ‖inner ℂ Ω ((b - x) Ω)‖ := by
        simp only [productVectorState, sub_apply, inner_sub_right]
      _ ≤ ‖Ω‖ * ‖(b - x) Ω‖ := norm_inner_le_norm _ _
      _ = ‖(x - b) Ω‖ := by rw [hΩ, one_mul, sub_apply, norm_sub_rev, ← sub_apply]
  apply le_of_lt
  calc
    _ = ‖(productVectorState Ω (c * x) - productVectorState Ω (c * b)) +
        productVectorState Ω a * (productVectorState Ω b - productVectorState Ω x)‖ :=
      congrArg norm he
    _ ≤ ‖productVectorState Ω (c * x) - productVectorState Ω (c * b)‖ +
        ‖productVectorState Ω a * (productVectorState Ω b - productVectorState Ω x)‖ :=
      norm_add_le _ _
    _ ≤ ‖c‖ * ‖(x - b) Ω‖ + ‖(a : H →L[ℂ] H)‖ * ‖(x - b) Ω‖ := by
      apply add_le_add (productVectorState_mul_error Ω hΩ c x b)
      rw [norm_mul]
      exact mul_le_mul (norm_productVectorState_le Ω hΩ a) hv (norm_nonneg _) (norm_nonneg _)
    _ = 2 * ‖(a : H →L[ℂ] H)‖ * ‖(x - b) Ω‖ := by
      dsimp [c]
      rw [norm_unitaryConj]
      ring
    _ ≤ (2 * ‖(a : H →L[ℂ] H)‖ + 1) * ‖(x - b) Ω‖ := by
      nlinarith [norm_nonneg ((x - b) Ω)]
    _ < (2 * ‖(a : H →L[ℂ] H)‖ + 1) * δ :=
      mul_lt_mul_of_pos_left herr (by positivity)
    _ = ε := mul_div_cancel₀ _ (by positivity)

include L in
/-- The relative commutant of the full vector-state centralizer is scalar.
The argument uses only finite-site independence, dense local vectors, and
separation by the product vector. -/
theorem scalar_of_commutes (hΩ : ‖Ω‖ = 1)
    (hsep : Function.Injective (algebraVectorMap D Ω))
    (x : H →L[ℂ] H) (hx : x ∈ D)
    (hcomm : ∀ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ D →
      ProductStateCentralizes D Ω u → (u : H →L[ℂ] H) * x = x * u) :
    x = productVectorState Ω x • (1 : H →L[ℂ] H) := by
  have hv : x Ω = productVectorState Ω x • Ω := by
    apply DenseRange.eq_of_inner_right ℂ L.dense
    rintro ⟨k, a⟩
    have hf := L.local_factorization hΩ x hx hcomm k (star a)
    calc
      inner ℂ ((a : H →L[ℂ] H) Ω) (x Ω) =
          productVectorState Ω ((star (a : H →L[ℂ] H)) * x) := by
        rw [← ContinuousLinearMap.adjoint_inner_right]
        rfl
      _ = productVectorState Ω (star (a : H →L[ℂ] H)) * productVectorState Ω x := hf
      _ = inner ℂ ((a : H →L[ℂ] H) Ω) (productVectorState Ω x • Ω) := by
        rw [inner_smul_right]
        change inner ℂ Ω ((a : H →L[ℂ] H).adjoint Ω) * productVectorState Ω x = _
        rw [ContinuousLinearMap.adjoint_inner_right]
        ring
  have he : (⟨x, hx⟩ : Algebra D) =
      ⟨productVectorState Ω x • (1 : H →L[ℂ] H),
        D.toStarSubalgebra.smul_mem D.one_mem _⟩ := by
    apply hsep
    simpa only [algebraVectorMap, LinearMap.coe_mk, AddHom.coe_mk, smul_apply,
      one_apply_eq_self] using hv
  exact congrArg Subtype.val he

end LocalProductSwaps

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductMatrixStages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Deriving the product-state argument from finite matrix data

A remote copy of a finite tensor block has identical matrix moments.
Every other finite block embeds in the product of these two blocks and
a finite complement. These are finite tensor-product statements; no
centralizer irreducibility or crossed-product conclusion is assumed.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ProductMatrixStages

variable (P : ProductMatrixStages (H := H))

/-- The finite-product construction implies the irreducibility of its
state centralizer. -/
theorem state_centralizer_irreducible (x : H →L[ℂ] H) (hx : x ∈ P.algebra)
    (hc : ∀ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ P.algebra →
      ProductStateCentralizes P.algebra P.vector u → (u : H →L[ℂ] H) * x = x * u) :
    x = productVectorState P.vector x • (1 : H →L[ℂ] H) :=
  P.localSwaps.scalar_of_commutes P.unit_vector P.separating x hx hc

end ProductMatrixStages

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioParameters
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two fixed product-state parameters

The manuscript uses `exp (-1)` and `exp (-sqrt 2)`. Their logarithms
generate an incommensurable pair of modular frequencies. No parameter
depends on an algebra, representation, or requested perturbation bound.
-/

namespace KadisonKastler

noncomputable section

theorem fixedProduct_log_ratio_irrational :
    Irrational (Real.log fixedProductLambda / Real.log fixedProductMu) := by
  simpa only [fixedProductLambda, fixedProductMu, Real.log_exp,
    neg_div_neg_eq, one_div] using irrational_sqrt_two.inv

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateCentralizerVonNeumann
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # The exact vector-state centralizer as a von Neumann algebra

Strong approximation preserves its defining matrix-coefficient identities.
The reference vector restricts to a faithful trace. For the fixed product
construction, finite-site swaps make this centralizer a factor.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem ProductMatrixStages.stateCentralizer_scalarCenter (P : ProductMatrixStages (H := H)) :
    ScalarCenter (stateCentralizerVonNeumann (M := P.algebra) P.vector) := by
  intro a ha hc
  refine ⟨productVectorState P.vector a,?_⟩
  apply P.state_centralizer_irreducible a ha.1
  intro u hu huc
  exact hc u.val ⟨hu,huc⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductCentralizerDiffuse
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Diffuseness of the fixed product-state centralizer

Scalar center and small nonzero projections exclude minimal projections.
This supplies the trace cuts used to assemble state-scaling isometries.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

namespace PointedMatrixSites

variable {Ω : H} (S : PointedMatrixSites M Ω twoRatioSiteParameter)

include S

theorem twoRatio_centralizer_scalarCenter :
    ScalarCenter (stateCentralizerVonNeumann (M := M) Ω) := by
  have h := S.twoRatioStages.stateCentralizer_scalarCenter
  change ScalarCenter (stateCentralizerVonNeumann (M := S.twoRatioStages.algebra) Ω) at h
  simpa only [S.twoRatioStages_algebra] using h

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProductScalingWords
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite product words as state-scaling partial isometries

All scale ratios here come from the actual two fixed site families.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

include S

theorem site_weight_pos (i : TwoRatioSite) (a : Fin 2) :
    0 < twoSiteWeight (twoRatioSiteParameter i) a := by
  have hp := (S.valid i).1
  unfold twoSiteWeight
  split_ifs <;> positivity

theorem site_entry_mem (i : TwoRatioSite) (a b : Fin 2) : (S.site i).entry a b ∈ M := by
  have hm := subset_generatedVonNeumannAlgebra _
    ((le_iSup (fun j => (S.site j).algebra) i) ((S.site i).entry_mem a b))
  exact Eq.mpr (congrArg (fun N : VonNeumannAlgebra H =>
    (S.site i).entry a b ∈ N) S.generates) hm

theorem site_entry_scales (i : TwoRatioSite) (a b : Fin 2) :
    StateScales M Ω (twoSiteWeight (twoRatioSiteParameter i) b /
      twoSiteWeight (twoRatioSiteParameter i) a) ((S.site i).entry a b) := by
  intro x hx
  have hh := S.twoRatio_site_balance i a b x hx
  have hw : (twoSiteWeight (twoRatioSiteParameter i) a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (S.site_weight_pos i a).ne'
  rw [Complex.ofReal_div]
  apply mul_left_cancel₀ hw
  calc
    _ = (twoSiteWeight (twoRatioSiteParameter i) b : ℂ)*
        productVectorState Ω ((S.site i).entry a b*x) := hh.symm
    _ = _ := by field_simp

theorem blockEntry_scales (l : List TwoRatioSite) (hl : l.Nodup)
    (a b : MatrixSiteBlockIndex l) :
    StateScales M Ω (matrixSiteBlockScale twoRatioSiteParameter l a b)
      (S.blockEntry l a b) := by
  induction l with
  | nil => intro x hx; simp [blockEntry,matrixSiteBlockScale]
  | cons i l ih =>
    exact (S.site_entry_scales i a.1 b.1).mul
      (ih (List.nodup_cons.mp hl).2 a.2 b.2) (S.site_entry_mem i a.1 b.1)
      (S.finiteBlock_le l (List.nodup_cons.mp hl).2
        ((S.finiteBlock l (List.nodup_cons.mp hl).2).entry_mem a.2 b.2))

theorem block_diagonal_weight_ne_zero (l : List TwoRatioSite)
    (a : MatrixSiteBlockIndex l) :
    matrixSiteBlockWeight twoRatioSiteParameter l a a ≠ 0 := by
  induction l with
  | nil => exact _root_.one_ne_zero
  | cons i l ih =>
    change (if a.1=a.1 then (twoSiteWeight (twoRatioSiteParameter i) a.1 : ℂ) else 0)*
      matrixSiteBlockWeight twoRatioSiteParameter l a.2 a.2 ≠ 0
    simp only [↓reduceIte]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (S.site_weight_pos i a.1).ne') (ih a.2)

theorem blockScalingPartialIsometry_nonzero (l : List TwoRatioSite) (hl : l.Nodup)
    (a b : MatrixSiteBlockIndex l) : (S.blockScalingPartialIsometry l hl a b).val ≠ 0 := by
  intro hz
  have hh := (S.blockScalingPartialIsometry l hl a b).initial
  rw [hz,star_zero,zero_mul] at hh
  have he : S.blockEntry l b b=0 := (congrArg (fun x : Algebra M => x.val) hh).symm
  have ht := S.blockEntry_moment l hl b b
  rw [he,zero_apply,inner_zero_right] at ht
  exact S.block_diagonal_weight_ne_zero l b ht.symm

theorem block_coisometry (l : List TwoRatioSite) (hl : l.Nodup)
    (a b : MatrixSiteBlockIndex l)
    (hr : 0 < matrixSiteBlockScale twoRatioSiteParameter l a b)
    (hr1 : matrixSiteBlockScale twoRatioSiteParameter l a b ≤ 1) :
    ∃ w : Algebra M, w*star w=1 ∧
      StateScales M Ω (matrixSiteBlockScale twoRatioSiteParameter l a b) w.val :=
  exists_state_scaling_coisometry S.unit_vector S.separating S.twoRatio_centralizer_scalarCenter
    S.twoRatio_centralizer_diffuse hr hr1 (S.blockScalingPartialIsometry l hl a b)
    (S.blockEntry_scales l hl a b) (S.blockScalingPartialIsometry_nonzero l hl a b)

end PointedMatrixSites

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioScalingWords
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Integer powers of the two fixed state-scaling ratios

Distinct finite sites realize each ratio `lambda^k * mu^l` exactly.
-/

namespace KadisonKastler

noncomputable section

theorem signed_site_weight_ratio {ν : ℝ} (hν : 0 < ν) (k : ℤ) :
    twoSiteWeight ν (signedSiteColumn k) / twoSiteWeight ν (signedSiteRow k) =
      signedSiteScale ν k := by
  have hden : 1+ν ≠ 0 := ne_of_gt (by linarith)
  by_cases hk : k < 0
  · simp only [signedSiteRow,signedSiteColumn,signedSiteScale,hk,↓reduceIte,twoSiteWeight]
    norm_num
    field_simp
  · simp only [signedSiteRow,signedSiteColumn,signedSiteScale,hk,↓reduceIte,twoSiteWeight]
    norm_num
    field_simp

theorem signed_site_scale_pow (ν : ℝ) (k : ℤ) :
    signedSiteScale ν k ^ k.natAbs = ν^k := by
  cases k with
  | ofNat n => simp [signedSiteScale]
  | negSucc n => simp [signedSiteScale,zpow_negSucc,inv_pow]

theorem twoRatioScalingSites_nodup (k l : ℤ) : (twoRatioScalingSites k l).Nodup := by
  apply List.Nodup.append
  · exact List.nodup_range.map Sum.inl_injective
  · exact List.nodup_range.map Sum.inr_injective
  · apply List.disjoint_left.mpr
    intro i hi hj
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hi
    simp at hj

theorem matrixSiteBlockScale_ofFunction (ν : TwoRatioSite → ℝ) (l : List TwoRatioSite)
    (a b : TwoRatioSite → Fin 2) :
    matrixSiteBlockScale ν l (matrixSiteBlockIndexOfFunction l a)
      (matrixSiteBlockIndexOfFunction l b) =
      (l.map fun i => twoSiteWeight (ν i) (b i) / twoSiteWeight (ν i) (a i)).prod := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change _*matrixSiteBlockScale ν l (matrixSiteBlockIndexOfFunction l a)
      (matrixSiteBlockIndexOfFunction l b) = _
    rw [ih]
    rfl

theorem twoRatioScalingWords_scale (k l : ℤ) :
    matrixSiteBlockScale twoRatioSiteParameter (twoRatioScalingSites k l)
      (matrixSiteBlockIndexOfFunction _ (twoRatioScalingRow k l))
      (matrixSiteBlockIndexOfFunction _ (twoRatioScalingColumn k l)) =
      fixedProductLambda^k * fixedProductMu^l := by
  rw [matrixSiteBlockScale_ofFunction]
  simp only [twoRatioScalingSites,List.map_append,List.prod_append,List.map_map]
  change ((List.range k.natAbs).map (fun _ =>
    twoSiteWeight fixedProductLambda (signedSiteColumn k) /
      twoSiteWeight fixedProductLambda (signedSiteRow k))).prod *
    ((List.range l.natAbs).map (fun _ =>
    twoSiteWeight fixedProductMu (signedSiteColumn l) /
      twoSiteWeight fixedProductMu (signedSiteRow l))).prod = _
  simp_rw [signed_site_weight_ratio fixedProductLambda_pos,
    signed_site_weight_ratio fixedProductMu_pos]
  simp only [List.map_const',List.length_range,List.prod_replicate]
  rw [signed_site_scale_pow,signed_site_scale_pow]

open Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem PointedMatrixSites.exists_twoRatio_scaling_coisometry
    (S : PointedMatrixSites M Ω twoRatioSiteParameter) (k l : ℤ)
    (hsmall : fixedProductLambda^k * fixedProductMu^l ≤ 1) :
    ∃ w : Algebra M, w*star w=1 ∧
      StateScales M Ω (fixedProductLambda^k * fixedProductMu^l) w.val := by
  have hr : 0 < fixedProductLambda^k * fixedProductMu^l :=
    mul_pos (zpow_pos fixedProductLambda_pos k) (zpow_pos fixedProductMu_pos l)
  have h := S.block_coisometry (twoRatioScalingSites k l) (twoRatioScalingSites_nodup k l)
    (matrixSiteBlockIndexOfFunction _ (twoRatioScalingRow k l))
    (matrixSiteBlockIndexOfFunction _ (twoRatioScalingColumn k l))
  rw [twoRatioScalingWords_scale] at h
  exact h hr hsmall

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TwoRatioScalingDensity
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Density of the constructed state-scaling ratios -/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

theorem exists_twoRatio_scale_near {r ε : ℝ} (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε) :
    ∃ k l : ℤ, fixedProductLambda^k * fixedProductMu^l < 1 ∧
      dist (fixedProductLambda^k * fixedProductMu^l) r < ε := by
  have hd : Dense (AddSubgroup.closure
      ({Real.log fixedProductLambda,Real.log fixedProductMu} : Set ℝ) : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr fixedProduct_log_ratio_irrational
  let U : Set ℝ := Real.exp ⁻¹' Metric.ball r ε ∩ Set.Iio 0
  have hU : IsOpen U :=
    (Metric.isOpen_ball.preimage Real.continuous_exp).inter isOpen_Iio
  have hmem : Real.log r ∈ U := by
    refine ⟨?_,Real.log_neg hr hr1⟩
    change dist (Real.exp (Real.log r)) r < ε
    simpa only [Real.exp_log hr,dist_self] using hε
  obtain ⟨x,hxU,hx⟩ := hd.inter_open_nonempty U hU ⟨Real.log r,hmem⟩
  obtain ⟨k,l,hkl⟩ := AddSubgroup.mem_closure_pair.mp hx
  have hp : 0 < fixedProductLambda^k * fixedProductMu^l :=
    mul_pos (zpow_pos fixedProductLambda_pos k) (zpow_pos fixedProductMu_pos l)
  have he : Real.log (fixedProductLambda^k * fixedProductMu^l)=x := by
    rw [Real.log_mul (ne_of_gt (zpow_pos fixedProductLambda_pos k))
      (ne_of_gt (zpow_pos fixedProductMu_pos l)),Real.log_zpow,Real.log_zpow]
    simpa only [zsmul_eq_mul] using hkl
  have hv : fixedProductLambda^k * fixedProductMu^l=Real.exp x := by
    rw [← he,Real.exp_log hp]
  refine ⟨k,l,?_,?_⟩
  · rw [hv]
    exact Real.exp_lt_one_iff.mpr hxU.2
  · rw [hv]
    exact hxU.1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem PointedMatrixSites.exists_scaling_coisometry_near_oai
    (S : PointedMatrixSites M Ω twoRatioSiteParameter)
    {r ε : ℝ} (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε) :
    ∃ (s : ℝ) (w : Algebra M),
      0 < s ∧ s < 1 ∧ dist s r < ε ∧ w*star w=1 ∧ StateScales M Ω s w.val := by
  obtain ⟨k,l,hs,hclose⟩ := exists_twoRatio_scale_near hr hr1 hε
  obtain ⟨w,hw,hscale⟩ := S.exists_twoRatio_scaling_coisometry k l hs.le
  exact ⟨_,w,mul_pos (zpow_pos fixedProductLambda_pos k) (zpow_pos fixedProductMu_pos l),
    hs,hclose,hw,hscale⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.PointedMatrixSites.exists_scaling_coisometry_near_oai.{u_1} := @OAI.KadisonKastler.PointedMatrixSites.exists_scaling_coisometry_near_oai.{u_1}
