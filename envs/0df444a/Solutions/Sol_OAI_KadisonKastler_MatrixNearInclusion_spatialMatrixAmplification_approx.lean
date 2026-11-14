-- Prove2me | solution 1 for OAI.KadisonKastler.MatrixNearInclusion.spatialMatrixAmplification_approx
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:05:52.990417+00:00
-- url     : https://prove2.me/submissions/94d4c81b-5abb-4f15-86f1-8d804a956f27

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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
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
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
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
import Definitions.Def_Q260K069

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixNearInclusion
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix unit-ball proximity and graph row estimates

The cb distance supplies a separate approximant at each matrix level.
No linear selection of those approximants is assumed.
-/

namespace KadisonKastler

open scoped WithCStarModule InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace MatrixNearInclusion

variable {M N : VonNeumannAlgebra H} {γ η : ℝ}

attribute [local instance] OAI.KadisonKastler.MatrixNearInclusion.matrixNearOrder
attribute [local instance] OAI.KadisonKastler.MatrixNearInclusion.matrixNearStarOrder
/-- The choice of finite index set does not affect the proximity bound. -/
theorem square (h : MatrixNearInclusion M N γ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (X : CStarMatrix ι ι (H →L[ℂ] H))
    (hX : ∀ i j, X i j ∈ M) (hn : ‖X‖ ≤ 1) :
    ∃ Y : CStarMatrix ι ι (H →L[ℂ] H),
      (∀ i j, Y i j ∈ N) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ γ := by
  let e := CStarMatrix.reindexₐ ℂ (H →L[ℂ] H) (Fintype.equivFin ι)
  have he (T : CStarMatrix ι ι (H →L[ℂ] H)) : ‖e T‖ = ‖T‖ :=
    NonUnitalStarAlgHom.norm_map e.toStarAlgHom e.injective T
  have hes (T : CStarMatrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι))
      (H →L[ℂ] H)) : ‖e.symm T‖ = ‖T‖ :=
    NonUnitalStarAlgHom.norm_map e.symm.toStarAlgHom e.symm.injective T
  obtain ⟨Y, hY, hYn, hc⟩ := h _ (e X) (fun i j => hX _ _) (by rwa [he])
  refine ⟨e.symm Y, (fun i j => hY _ _), (hes Y).le.trans hYn, ?_⟩
  have hx : X = e.symm (e X) := (e.symm_apply_apply X).symm
  rw [hx, ← map_sub, hes]
  exact hc

end MatrixNearInclusion

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.countableTensorAlgebraic_tmul _root_.OAI.KadisonKastler.countableTensorEquiv_symm_single _root_.OAI.KadisonKastler.countableTensorEquiv_tmul _root_.OAI.KadisonKastler.countableTensorIsometry_tmul _root_.OAI.KadisonKastler.countableTensorVector_apply _root_.OAI.KadisonKastler.countableTensorVector_single _root_.OAI.KadisonKastler.leftTensorVector_apply _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.rightTensorSlice_apply _root_.OAI.KadisonKastler.spatialIsometry_tmul _root_.OAI.KadisonKastler.spatialMap_id _root_.OAI.KadisonKastler.spatialMap_tmul _root_.OAI.KadisonKastler.spatialMatrixAmplification_apply _root_.OAI.KadisonKastler.tensorVectorSliceCP_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite matrix amplification in a spatial tensor product

An actual matrix-unit system in the second tensor factor gives a star
representation of operator-valued matrices. Its norm is the C-star matrix
norm: multiplying on both sides by matrix units recovers each coefficient,
so the representation is faithful whenever the second Hilbert space is
nonzero. No assertion about amplification of an ordinary algebra gap is
used here.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator
open scoped BigOperators TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.KadisonKastler.spatialMatrixStarOrder
theorem spatialMatrixHom_apply (E : MatrixUnitSystem ι (K →L[ℂ] K))
    (X : CStarMatrix ι ι (H →L[ℂ] H)) :
    spatialMatrixHom E X = ∑ i, ∑ j, spatialTensorOp (X i j) (E.entry i j) := by
  change (∑ i, ∑ j, spatialLeft (K := K) (X i j) *
    spatialRight (H := H) (E.entry i j)) = _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change spatialTensorOp (X i j) 1 * spatialTensorOp 1 (E.entry i j) = _
  rw [← spatialTensorOp_mul, mul_one, one_mul]

/-- Matrix-unit multiplication extracts a single spatial coefficient. -/
theorem spatialMatrixHom_sandwich (E : MatrixUnitSystem ι (K →L[ℂ] K))
    (X : CStarMatrix ι ι (H →L[ℂ] H)) (o i j : ι) :
    spatialRight (H := H) (E.entry o i) * spatialMatrixHom E X *
      spatialRight (H := H) (E.entry j o) = spatialTensorOp (X i j) (E.entry o o) := by
  have hterm (a b : ι) :
      (spatialTensorOp (1 : H →L[ℂ] H) (E.entry o i) *
        spatialTensorOp (X a b) (E.entry a b)) *
        spatialTensorOp 1 (E.entry j o) =
      if i = a then if b = j then spatialTensorOp (X a b) (E.entry o o) else 0 else 0 := by
    rw [← spatialTensorOp_mul, ← spatialTensorOp_mul]
    simp only [one_mul, mul_one, E.mul_entry]
    by_cases hia : i = a
    · subst a
      by_cases hbj : b = j
      · subst b
        simp [E.mul_entry]
      · simp [E.mul_entry, hbj]
    · simp [hia]
  rw [spatialMatrixHom_apply]
  change spatialTensorOp (1 : H →L[ℂ] H) (E.entry o i) * _ *
    spatialTensorOp 1 (E.entry j o) = _
  simp only [Finset.mul_sum, Finset.sum_mul, hterm]
  simp

variable [Nonempty ι] [Nontrivial K]

/-- A nonzero second tensor leg makes the finite matrix representation faithful. -/
theorem spatialMatrixHom_injective (E : MatrixUnitSystem ι (K →L[ℂ] K)) :
    Function.Injective (spatialMatrixHom (H := H) E) := by
  let o : ι := Classical.arbitrary ι
  obtain ⟨η, hη⟩ : ∃ η : K, E.entry o o η ≠ 0 := by
    by_contra h
    apply E.diagonal_ne_zero o
    ext η
    exact not_exists_not.mp h η
  apply (injective_iff_map_eq_zero _).mpr
  intro X hX
  apply CStarMatrix.ext
  intro i j
  apply ContinuousLinearMap.ext
  intro ξ
  have hs : spatialTensorOp (X i j) (E.entry o o) = 0 := by
    rw [← spatialMatrixHom_sandwich E X o i j, hX, mul_zero, zero_mul]
  have hn := congrArg (fun T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
    ‖T ((ξ ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : SpatialHilbert H K)‖) hs
  have hz : ‖X i j ξ‖ * ‖E.entry o o η‖ = 0 := by
    simpa only [spatialTensorOp_coe, TensorProduct.mapL_tmul,
      UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul, zero_apply,
      norm_zero] using hn
  exact norm_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (norm_ne_zero_iff.mpr hη))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialMatrixAmplification
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite matrix amplification of spatial matrix images

Finite matrices over a generated operator algebra generate the matrix
von Neumann algebra.  The proof uses the existing strong approximation
theorem entry by entry.  Flattening the two finite matrix indices then
preserves the complete unit-ball approximation constant.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator Filter
open scoped Topology BigOperators

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] OAI.KadisonKastler.spatialAmplificationStarOrder
attribute [local instance] OAI.KadisonKastler.spatialAmplificationTargetStarOrder
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

attribute [local instance] OAI.KadisonKastler.spatialAmplificationTargetOrder
theorem spatialMatrixAmplification_injective [Nonempty κ] [Nontrivial K]
    (E : MatrixUnitSystem κ (K →L[ℂ] K)) :
    Function.Injective (spatialMatrixAmplification (H := H) (ι := ι) E) := by
  intro X Y hXY
  apply CStarMatrix.ext
  intro i j
  apply spatialMatrixHom_injective E
  exact congrArg (fun Z => Z i j) hXY

attribute [local instance] OAI.KadisonKastler.spatialAmplificationOrder
theorem norm_spatialMatrixAmplification [Nonempty κ] [Nontrivial K]
    (E : MatrixUnitSystem κ (K →L[ℂ] K))
    (X : CStarMatrix ι ι (CStarMatrix κ κ (H →L[ℂ] H))) :
    ‖spatialMatrixAmplification E X‖ = ‖X‖ :=
  NonUnitalStarAlgHom.norm_map (spatialMatrixAmplification E)
    (spatialMatrixAmplification_injective E) X

/-- Flattening lets the original complete approximation hypothesis control
every finite amplification of a spatial matrix image. -/
theorem MatrixNearInclusion.spatialMatrixAmplification_approx_oai
    {M N : VonNeumannAlgebra H} {γ : ℝ} (h : MatrixNearInclusion M N γ)
    [Nonempty κ] [Nontrivial K] (E : MatrixUnitSystem κ (K →L[ℂ] K))
    (X : CStarMatrix ι ι (CStarMatrix κ κ (H →L[ℂ] H)))
    (hX : ∀ i j a b, X i j a b ∈ M) (hn : ‖X‖ ≤ 1) :
    ∃ Y : CStarMatrix ι ι (CStarMatrix κ κ (H →L[ℂ] H)),
      (∀ i j a b, Y i j a b ∈ N) ∧ ‖Y‖ ≤ 1 ∧
      ‖spatialMatrixAmplification E X - spatialMatrixAmplification E Y‖ ≤ γ := by
  let e := cstarMatrixComp (A := H →L[ℂ] H) ι κ
  have he (Z : CStarMatrix ι ι (CStarMatrix κ κ (H →L[ℂ] H))) : ‖e Z‖ = ‖Z‖ :=
    NonUnitalStarAlgHom.norm_map e.toStarAlgHom e.injective Z
  have hes (Z : CStarMatrix (ι × κ) (ι × κ) (H →L[ℂ] H)) : ‖e.symm Z‖ = ‖Z‖ :=
    NonUnitalStarAlgHom.norm_map e.symm.toStarAlgHom e.symm.injective Z
  obtain ⟨Y, hY, hYn, hc⟩ := h.square (e X)
    (fun i j => hX i.1 j.1 i.2 j.2) ((he X).le.trans hn)
  refine ⟨e.symm Y, (fun i j a b => hY (i, a) (j, b)), (hes Y).le.trans hYn, ?_⟩
  rw [← map_sub, norm_spatialMatrixAmplification]
  have hx : X = e.symm (e X) := (e.symm_apply_apply X).symm
  rw [hx, ← map_sub, hes]
  exact hc

end

end KadisonKastler

end OAI
end

theorem solution.{u, u_1, u_2} : type_of% @OAI.KadisonKastler.MatrixNearInclusion.spatialMatrixAmplification_approx_oai.{u, u_1, u_2} := @OAI.KadisonKastler.MatrixNearInclusion.spatialMatrixAmplification_approx_oai.{u, u_1, u_2}
