-- Prove2me | solution 1 for OAI.KadisonKastler.uniform_modular_matrix_graph_strong_stability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T14:32:25.689197+00:00
-- url     : https://prove2.me/submissions/2f4a3908-c9bd-40a7-8e65-195150dd8fc0

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
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
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
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
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
import Mathlib.Analysis.Normed.Operator.NNNorm
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
import Mathlib.Analysis.SpecialFunctions.Exponential
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
import Mathlib.Data.Finset.Sort
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
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
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
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Contracting
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K072
import Definitions.Def_Q260K044
import Theorems.Thm_OAI_KadisonKastler_MatrixNearInclusion_regularTensor_gap
import Theorems.Thm_OAI_KadisonKastler_kkDistance_regularTensor_conjugate_le
import Theorems.Thm_OAI_KadisonKastler_publishedBlockCommutantApproximation
import Theorems.Thm_OAI_KadisonKastler_publishedRealNestDistance
import Theorems.Thm_OAI_KadisonKastler_regularCore_spatial_of_typeIIInfinity
import Theorems.Thm_OAI_KadisonKastler_uniform_common_action_of_rescaled_graphs

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The concrete Kadison–Kastler distance

The distance is the operator-norm Hausdorff distance between the closed unit
balls of two concrete, unital von Neumann algebras.  All Hilbert spaces are
allowed, including the zero space. The elementary estimates belong to §2 of
*Universal strong Kadison–Kastler stability* (2026).
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kkDistance_triangle (M N P : VonNeumannAlgebra H) :
    kkDistance M P ≤ kkDistance M N + kkDistance N P :=
  Metric.hausdorffDist_triangle (unitBall_hausdorffEDist_ne_top M N)

theorem unitaryConj_unitBall {M N : VonNeumannAlgebra H}
    {v : unitary (H →L[ℂ] H)} (hv : Conjugates v M N) :
    unitaryConj v '' unitBall M = unitBall N := by
  change unitaryConj v '' (M : Set (H →L[ℂ] H)) = (N : Set (H →L[ℂ] H)) at hv
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, by simpa using hx.2⟩
    change unitaryConj v x ∈ (N : Set (H →L[ℂ] H))
    rw [← hv]
    exact Set.mem_image_of_mem _ hx.1
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (show y ∈ unitaryConj v '' (M : Set (H →L[ℂ] H)) from
      hv.symm ▸ hy.1)
    exact ⟨x, ⟨hx, by simpa using hy.2⟩, rfl⟩

/-- The elementary displacement estimate used at every matrix level in §2. -/
theorem norm_unitaryConj_sub_le (v : unitary (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    ‖unitaryConj v x - x‖ ≤ 2 * ‖(v : H →L[ℂ] H) - 1‖ * ‖x‖ := by
  have hid : unitaryConj v x - x =
      (((v : H →L[ℂ] H) - 1) * x) * star (v : H →L[ℂ] H) +
        x * (star (v : H →L[ℂ] H) - 1) := by
    dsimp [unitaryConj]
    noncomm_ring
  have hstar : ‖star (v : H →L[ℂ] H) - 1‖ = ‖(v : H →L[ℂ] H) - 1‖ := by
    simpa only [star_sub, star_one] using norm_star ((v : H →L[ℂ] H) - 1)
  calc
    ‖unitaryConj v x - x‖ ≤
        ‖(((v : H →L[ℂ] H) - 1) * x) * star (v : H →L[ℂ] H)‖ +
          ‖x * (star (v : H →L[ℂ] H) - 1)‖ := hid ▸ norm_add_le _ _
    _ = ‖((v : H →L[ℂ] H) - 1) * x‖ +
          ‖x * (star (v : H →L[ℂ] H) - 1)‖ := by
      rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary]
    _ ≤ ‖(v : H →L[ℂ] H) - 1‖ * ‖x‖ +
          ‖x‖ * ‖star (v : H →L[ℂ] H) - 1‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖(v : H →L[ℂ] H) - 1‖ * ‖x‖ := by rw [hstar]; ring

theorem kkDistance_le_of_conjugates {M N : VonNeumannAlgebra H}
    {v : unitary (H →L[ℂ] H)} (hv : Conjugates v M N) :
    kkDistance M N ≤ 2 * ‖(v : H →L[ℂ] H) - 1‖ := by
  have hb := unitaryConj_unitBall hv
  apply Metric.hausdorffDist_le_of_mem_dist (mul_nonneg (by norm_num) (norm_nonneg _))
  · intro x hx
    refine ⟨unitaryConj v x, hb ▸ Set.mem_image_of_mem _ hx, ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact (norm_unitaryConj_sub_le v x).trans
      (mul_le_of_le_one_right (mul_nonneg (by norm_num) (norm_nonneg _)) hx.2)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (show y ∈ unitaryConj v '' unitBall M from hb.symm ▸ hy)
    refine ⟨x, hx, ?_⟩
    rw [dist_eq_norm]
    exact (norm_unitaryConj_sub_le v x).trans
      (mul_le_of_le_one_right (mul_nonneg (by norm_num) (norm_nonneg _)) hx.2)

/-- Moving one algebra by a small unitary increases its gap by at most twice
the unitary displacement (the ordinary-distance part of equation (2.1)). -/
theorem kkDistance_conjugate_le {M N P : VonNeumannAlgebra H}
    {v : unitary (H →L[ℂ] H)} (hv : Conjugates v N P) :
    kkDistance M P ≤ kkDistance M N + 2 * ‖(v : H →L[ℂ] H) - 1‖ :=
  (kkDistance_triangle M N P).trans (add_le_add le_rfl (kkDistance_le_of_conjugates hv))

/-- Errors add when two unitary changes of position are composed. -/
theorem norm_unitary_mul_sub_one_le (v w : unitary (H →L[ℂ] H)) :
    ‖((v * w : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ ≤
      ‖(v : H →L[ℂ] H) - 1‖ + ‖(w : H →L[ℂ] H) - 1‖ := by
  have hid : (v : H →L[ℂ] H) * (w : H →L[ℂ] H) - 1 =
      (v : H →L[ℂ] H) * ((w : H →L[ℂ] H) - 1) + ((v : H →L[ℂ] H) - 1) := by
    noncomm_ring
  change ‖(v : H →L[ℂ] H) * (w : H →L[ℂ] H) - 1‖ ≤ _
  rw [hid]
  exact (norm_add_le _ _).trans_eq (by simp [add_comm])

theorem NearConjugacy.symm {M N : VonNeumannAlgebra H} {ε : ℝ}
    (h : NearConjugacy M N ε) : NearConjugacy N M ε := by
  obtain ⟨v, hv, hε⟩ := h
  refine ⟨star v, hv.symm, ?_⟩
  have heq : ‖((star v : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ =
      ‖(v : H →L[ℂ] H) - 1‖ := by
    simpa only [Unitary.coe_star, star_sub, star_one] using
      norm_star ((v : H →L[ℂ] H) - 1)
  rw [heq]
  exact hε

theorem NearConjugacy.trans {M N P : VonNeumannAlgebra H} {ε η : ℝ}
    (hMN : NearConjugacy M N ε) (hNP : NearConjugacy N P η) :
    NearConjugacy M P (ε + η) := by
  obtain ⟨v, hv, hε⟩ := hMN
  obtain ⟨w, hw, hη⟩ := hNP
  refine ⟨w * v, hv.trans hw, ?_⟩
  exact (norm_unitary_mul_sub_one_le w v).trans_lt
    (by simpa only [add_comm] using add_lt_add hε hη)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AmenableEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Moving an injective subalgebra into a nearby algebra

The published input is the one-sided assertion of Cameron--Christensen--
Sinclair--Smith--White--Wiggins, *Kadison--Kastler stable factors*, Duke
Math. J. 163 (2014), Theorem 3.3(i), arXiv:1209.4116v3, p. 13. Only
the inclusion and the displacement bound `150 * γ` are retained.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The algebra just constructed is the exact unitary image. -/
theorem conjugates_unitaryConjugateAlgebra (w : unitary (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) : Conjugates w M (unitaryConjugateAlgebra w M) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteFactorModulus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A uniform tolerance for the finite-factor displacement estimate -/

namespace KadisonKastler

open Filter Topology

noncomputable section

theorem continuous_commonPositionError : Continuous commonPositionError := by
  unfold commonPositionError
  fun_prop

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedFiniteFactorModulus
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A uniform tolerance for the finite-factor displacement estimate -/

namespace KadisonKastler

open Filter Topology

noncomputable section

theorem continuous_constructedFiniteFactorError : Continuous constructedFiniteFactorError := by
  unfold constructedFiniteFactorError
  exact (continuous_const.mul continuous_id).add
    (continuous_const.mul (continuous_commonPositionError.comp
      (continuous_const.mul continuous_id)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AmenableMatrixStability
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Removing the common matrix-unit hypothesis

A countable full matrix corner in an injective subalgebra is moved into the
neighbor using the constructed finite-group embedding. The original
finite corner and its representation remain fixed throughout this step.
-/

namespace KadisonKastler

open Filter Topology

noncomputable section

universe u

theorem continuous_matrixCornerError : Continuous matrixCornerError := by
  unfold matrixCornerError
  exact (continuous_const.mul continuous_id).add
    (continuous_constructedFiniteFactorError.comp (continuous_const.mul continuous_id))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreModulus
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # A uniform tolerance for regular-core descent

The tolerance is obtained from the proved continuous error functions at zero.
It is chosen before the Hilbert space, the algebras, and the modular action.
Both the original-space gap and the regular tensor gap remain explicit.
-/

namespace KadisonKastler

open Filter Topology

noncomputable section

universe u

/-- One positive tolerance satisfies every numerical requirement of the
regular-core descent and the prescribed final displacement. -/
theorem exists_regularCore_tolerance {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧
      302 * t < 1 / 100 ∧
      302 * (302 * t) < 174 / 1000000000000000 ∧
      3 * 50948 * Real.sqrt (302 * (302 * t)) < 1 / 100000 ∧
      commonPositionError (302 * (302 * t)) < 1 / 4000000 ∧
      2 * matrixCornerError t < 1 / 1000 ∧
      t + 2 * matrixCornerError t < 1 ∧
      256 * matrixCornerError t < ε := by
  have h₁ : ∀ᶠ t : ℝ in 𝓝 0, 302 * t < 1 / 100 :=
    (continuous_const.mul continuous_id).continuousAt.eventually_lt_const (by norm_num)
  have h₂ : ∀ᶠ t : ℝ in 𝓝 0,
      302 * (302 * t) < 174 / 1000000000000000 :=
    (continuous_const.mul (continuous_const.mul continuous_id)).continuousAt.eventually_lt_const
      (by norm_num)
  have hc₃ : Continuous (fun t : ℝ =>
      3 * 50948 * Real.sqrt (302 * (302 * t))) := by fun_prop
  have h₃ : ∀ᶠ t : ℝ in 𝓝 0,
      3 * 50948 * Real.sqrt (302 * (302 * t)) < 1 / 100000 :=
    hc₃.continuousAt.eventually_lt_const (by norm_num)
  have hc₄ : Continuous (fun t : ℝ => commonPositionError (302 * (302 * t))) :=
    continuous_commonPositionError.comp
      (continuous_const.mul (continuous_const.mul continuous_id))
  have h₄ : ∀ᶠ t : ℝ in 𝓝 0,
      commonPositionError (302 * (302 * t)) < 1 / 4000000 :=
    hc₄.continuousAt.eventually_lt_const (by norm_num)
  have h₅ : ∀ᶠ t : ℝ in 𝓝 0, 2 * matrixCornerError t < 1 / 1000 :=
    (continuous_const.mul continuous_matrixCornerError).continuousAt.eventually_lt_const
      (by norm_num)
  have h₆ : ∀ᶠ t : ℝ in 𝓝 0, t + 2 * matrixCornerError t < 1 :=
    (continuous_id.add (continuous_const.mul continuous_matrixCornerError)).continuousAt.eventually_lt_const
      (by norm_num)
  have h₇ : ∀ᶠ t : ℝ in 𝓝 0, 256 * matrixCornerError t < ε :=
    (continuous_const.mul continuous_matrixCornerError).continuousAt.eventually_lt_const
      (by simpa using hε)
  have hall : ∀ᶠ t : ℝ in 𝓝 0,
      302 * t < 1 / 100 ∧
      302 * (302 * t) < 174 / 1000000000000000 ∧
      3 * 50948 * Real.sqrt (302 * (302 * t)) < 1 / 100000 ∧
      commonPositionError (302 * (302 * t)) < 1 / 4000000 ∧
      2 * matrixCornerError t < 1 / 1000 ∧
      t + 2 * matrixCornerError t < 1 ∧
      256 * matrixCornerError t < ε := by
    filter_upwards [h₁, h₂, h₃, h₄, h₅, h₆, h₇] with t ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ ht₇
    exact ⟨ht₁, ht₂, ht₃, ht₄, ht₅, ht₆, ht₇⟩
  obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨d / 2, half_pos hd, hball ?_⟩
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hd)] using
    half_lt_self hd

attribute [local instance] OAI.KadisonKastler.regularCoreModulusOrder
attribute [local instance] OAI.KadisonKastler.regularCoreModulusStarOrder
/-- Uniform strong stability from a type II∞ source regular core. The
original and tensor gaps are both hypotheses; no ordinary-gap amplification
is asserted. -/
theorem uniform_regularCore_strong_stability
    (h : FiniteFactorPublishedInputs.{u})
    (hComm : PublishedRegularCommutant.{u})
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (hCopies : PublishedProperInfiniteProjectionCopies.{u})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
      (M N : VonNeumannAlgebra H),
      PublishedMultiplicationCorrection M →
      PublishedBlockCommutantApproximation (Algebra M) H →
      ∀ (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
        (hU : ∀ ξ, Continuous (fun s : ℝ =>
          (U (Multiplicative.ofAdd s) : H →L[ℂ] H) ξ)),
      (∀ s T, T ∈ M → unitaryConj (U s) T ∈ M) →
      (∀ s T, T ∈ N → unitaryConj (U s) T ∈ N) →
      TypeIIInfinityFactor (regularCoreAlgebra U hU M) →
      kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) < t →
      kkDistance M N < t → NearConjugacy M N ε := by
  obtain ⟨t, ht, hEmbed, hPosition, hStandard, hSpatial, hCP, hge, hεt⟩ :=
    exists_regularCore_tolerance hε
  refine ⟨t, ht, ?_⟩
  intro H _ _ _ _ M N hCorrection hCommutant U hU hM hN hCore hTensor hGap
  obtain ⟨v, hv, hnorm⟩ := regularCore_spatial_of_typeIIInfinity
    h hComm hSpectral hDiagonal M N hCorrection hCommutant U hU hM hN
    hCopies hCore ht hEmbed hPosition hTensor hGap hStandard hSpatial hCP hge
  exact ⟨v, hv, hnorm.trans_lt hεt⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularCoreStability
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # Completing modular graph stability by descent through the regular core

The source core belongs to the neighboring modular group.
The tensor gap is proved from the same complete maps used for graph
comparison and is propagated through the small action alignment.
-/

namespace KadisonKastler

noncomputable section

universe u

attribute [local instance] OAI.KadisonKastler.modularCoreOrder
local instance modularCoreStarOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _


/-- The same original-space conclusion under actual matrix unit-ball proximity.
No global linear selection of approximants is required. -/
theorem uniform_modular_matrix_graph_strong_stability_oai
    (h : ModularCorePublishedInputs.{u}) {B : ℝ} (hB : 0 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H],
      ∀ (M N : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ (Ω : H) (_m : ModularSpectralResolution M Ω) (n : ModularSpectralResolution N Ω)
        (J : H ≃ₗᵢ⋆[ℂ] H),
      TypeIIInfinityFactor (regularCoreAlgebra n.group n.continuous N) →
      ∀ γ : ℝ, 0 < γ → γ < δ → kkDistance M N < γ →
      MatrixNearInclusion M N γ → MatrixNearInclusion N M γ →
      (∀ c : ℝ, 0 < c →
        ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤ B * γ) →
      NearConjugacy M N ε := by
  obtain ⟨γ0, K, hγ0, hK, haction⟩ := uniform_common_action_of_rescaled_graphs
    h.spectral h.comparison h.sakai (fun H _ _ _ M => publishedBlockCommutantApproximation (Algebra M) H)
    h.hardy publishedRealNestDistance h.realSpectral h.diagonal
    hB
  obtain ⟨t, ht, hcore⟩ := uniform_regularCore_strong_stability h.finite h.coreCommutant
    h.realSpectral h.diagonal h.copies (half_pos hε)
  have hA : 0 < 2 + 2 * K := by positivity
  refine ⟨min γ0 (min (t / (2 + 2 * K)) (ε / (2 * K))),
    lt_min hγ0 (lt_min (div_pos ht hA) (div_pos hε (by positivity))), ?_⟩
  intro H _ _ _ _ _ M N hM Ω m n J hNcore γ hγ hsmall hgap hMN hNM hgraph
  obtain ⟨q, hq, hqaction⟩ := haction H M N hM Ω m n J
    (fun _ => h.correction H _) γ hγ (hsmall.trans_le (min_le_left _ _)) hgap hgraph
  let P := unitaryConjugateAlgebra q M
  have htγ : (2 + 2 * K) * γ < t := by
    have hx := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
    have hx' := (lt_div_iff₀ hA).mp hx
    nlinarith
  have hqt : K * γ < ε / 2 := by
    have hx := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
    have hx' := (lt_div_iff₀ (by positivity : 0 < 2 * K)).mp hx
    linarith
  have htensor : kkDistance (regularTensorAlgebra N) (regularTensorAlgebra P) < t := by
    have hg := MatrixNearInclusion.regularTensor_gap hMN hNM hγ.le
    rw [kkDistance_comm] at hg
    exact (kkDistance_regularTensor_conjugate_le M N q).trans_lt
      (by nlinarith)
  have hgapP : kkDistance N P < t := by
    have hg := kkDistance_conjugate_le (M := N) (conjugates_unitaryConjugateAlgebra q M)
    rw [kkDistance_comm N M] at hg
    exact hg.trans_lt (by nlinarith)
  have hv := hcore H N P (h.correction H N) (publishedBlockCommutantApproximation (Algebra N) H)
    n.group n.continuous
    (fun s x hx => by
      have hs := n.normalizes s
      change unitaryConj (n.group s) x ∈ (N : Set (H →L[ℂ] H))
      rw [← hs]
      exact Set.mem_image_of_mem _ hx)
    (fun s x hx => by
      have hs := hqaction s
      change unitaryConj (n.group s) x ∈
        (unitaryConjugateAlgebra q M : Set (H →L[ℂ] H))
      rw [← hs]
      exact Set.mem_image_of_mem _ hx)
    hNcore htensor hgapP
  have hMP : NearConjugacy M P (ε / 2) :=
    ⟨q, conjugates_unitaryConjugateAlgebra q M, hq.trans_lt hqt⟩
  simpa only [add_halves] using hMP.trans hv.symm

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.uniform_modular_matrix_graph_strong_stability_oai.{u} := @OAI.KadisonKastler.uniform_modular_matrix_graph_strong_stability_oai.{u}
