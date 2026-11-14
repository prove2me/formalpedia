-- Prove2me | solution 1 for OAI.KadisonKastler.exists_matrixPair_preparation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:02:12.752979+00:00
-- url     : https://prove2.me/submissions/54f043ef-fb6c-4c86-9189-80a02d39d326

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
import Definitions.Def_Q260K072
import Theorems.Thm_OAI_KadisonKastler_MatrixNearInclusion_commutant_kkDistance_le
import Theorems.Thm_OAI_KadisonKastler_MatrixNearInclusion_commutant_nearInclusion
import Theorems.Thm_OAI_KadisonKastler_ModularConjugationData_expected_right_data
import Theorems.Thm_OAI_KadisonKastler_exists_localized_unitary_matrixUnits_embedding
import Theorems.Thm_OAI_KadisonKastler_expected_modular_corrected_cyclic_separating

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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Amenable
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Conditional strong stability for injective represented algebras

The hypothesis `ChristensenMutual` is the mutual near-inclusion
consequence of Cameron–Christensen–Sinclair–Smith–White–Wiggins,
*Kadison–Kastler stable factors*, Duke Math. J. 163 (2014), Theorem 3.3(i),
building on Christensen, *Near inclusions of C*-algebras* (1980).
The stability theorem is conditional on this near-inclusion property.
-/

namespace KadisonKastler

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem nearInclusion_of_kkDistance_lt {M N : VonNeumannAlgebra H} {γ : ℝ}
    (h : kkDistance M N < γ) : NearInclusion M N γ := by
  obtain ⟨γ', hdist, hγ'⟩ := exists_between h
  refine ⟨γ', hγ', ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := exists_unitBall_approx hx hdist
  exact (Metric.infDist_le_dist_of_mem hy.1).trans
    (le_of_lt (by simpa only [dist_eq_norm] using hxy))

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AmenableEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Restricting the source preserves a near inclusion with the same bound. -/
theorem nearInclusion_mono_left {R M N : VonNeumannAlgebra H} {γ : ℝ}
    (hRM : R ≤ M) (hMN : NearInclusion M N γ) : NearInclusion R N γ := by
  obtain ⟨γ', hγ', happrox⟩ := hMN
  exact ⟨γ', hγ', fun x hx => happrox x ⟨hRM hx.1, hx.2⟩⟩

/-- The algebra just constructed is the exact unitary image. -/
theorem conjugates_unitaryConjugateAlgebra (w : unitary (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) : Conjugates w M (unitaryConjugateAlgebra w M) := rfl

theorem le_unitaryConjugateAlgebra_star {R N : VonNeumannAlgebra H}
    (w : unitary (H →L[ℂ] H)) (hw : ∀ x ∈ R, unitaryConj w x ∈ N) :
    R ≤ unitaryConjugateAlgebra (star w) N := by
  intro x hx
  exact ⟨unitaryConj w x, hw x hx, unitaryConj_star_unitaryConj w x⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompletelyBounded
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Matrix bounds for perturbation maps

All norms here are the C*-matrix norms, including for rectangular matrices.
The rectangular formulation records exactly the estimates needed for the
Haagerup product norm in the multiplication-correction argument.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in
theorem rectangular_toCLM_mul {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    CStarMatrix.toCLM (X * Y) = (CStarMatrix.toCLM Y).comp (CStarMatrix.toCLM X) := by
  ext v i
  simp only [CStarMatrix.toCLM_apply, ContinuousLinearMap.comp_apply]
  exact congrFun (Matrix.vecMul_vecMul v X Y).symm i

/-- Submultiplicativity also holds for rectangular C*-matrices. -/
theorem rectangular_norm_mul_le {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := by
  simp only [CStarMatrix.norm_def, rectangular_toCLM_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
theorem matrix_map_sub (F G : A →ₗ[ℂ] B) {p q : ℕ}
    (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (F - G) X = CStarMatrix.mapₗ F X - CStarMatrix.mapₗ G X := by
  ext i j
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Faithful representations are completely isometric

Injective star-algebra homomorphisms preserve C⋆-norms at each square
matrix level. The isometric corner embedding then gives the same statement
for every rectangular matrix size used in the perturbation estimates.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

/-- Faithfulness preserves the norm of each square amplification. -/
theorem injective_starAlgHom_matrix_norm (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    {n : Type*} [Fintype n] (X : CStarMatrix n n A) :
    ‖CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X‖ = ‖X‖ := by
  change ‖CStarMatrix.mapₙₐ φ.toNonUnitalStarAlgHom X‖ = ‖X‖
  exact NonUnitalStarAlgHom.norm_map _ (injective_starAlgHom_matrix φ hφ) X

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CompletelyBoundedBy.toContinuousLinearMap_apply _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.matrixScalarHom_mul_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mul_matrixScalarHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The complete displacement of an inner conjugation -/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The same displacement bound holds at every rectangular matrix level. -/
theorem complete_unitaryConjugation_sub_id (u : unitary B) :
    CompletelyBoundedBy (unitaryConjugationLinear u - LinearMap.id)
      (2 * ‖(u : B) - 1‖) := by
  intro p q X
  nontriviality B
  let P : CStarMatrix (Fin p) (Fin p) B := matrixScalarHom (u : B)
  let Q : CStarMatrix (Fin q) (Fin q) B := matrixScalarHom (star (u : B))
  have hQ : ‖Q‖ ≤ 1 := by
    exact (NonUnitalStarAlgHom.norm_apply_le
      (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin q) (Fin q) B) _).trans_eq
        (by simp)
  have hPsub : ‖P - 1‖ ≤ ‖(u : B) - 1‖ := by
    simpa only [map_sub, map_one] using NonUnitalStarAlgHom.norm_apply_le
      (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin p) (Fin p) B) ((u : B) - 1)
  have hQsub : ‖Q - 1‖ ≤ ‖(u : B) - 1‖ := by
    have h := NonUnitalStarAlgHom.norm_apply_le
      (matrixScalarHom : B →⋆ₐ[ℂ] CStarMatrix (Fin q) (Fin q) B) (star (u : B) - 1)
    have hs : ‖star (u : B) - 1‖ = ‖(u : B) - 1‖ := by
      simpa only [star_sub, star_one] using norm_star ((u : B) - 1)
    simpa only [map_sub, map_one, hs] using h
  have hmatrix : CStarMatrix.mapₗ (unitaryConjugationLinear u) X = P * X * Q := by
    ext i j
    simp [P, Q, CStarMatrix.mul_apply, matrixScalarHom_apply]
  have hid : P * X * Q - X = (P - 1) * X * Q + X * (Q - 1) := by
    have hm (A : Matrix (Fin p) (Fin p) B) (Y : Matrix (Fin p) (Fin q) B)
        (D : Matrix (Fin q) (Fin q) B) :
        A * Y * D - Y = (A - 1) * Y * D + Y * (D - 1) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      abel
    exact hm P X Q
  rw [matrix_map_sub, hmatrix]
  change ‖P * X * Q - X‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖(P - 1) * X * Q‖ + ‖X * (Q - 1)‖ := norm_add_le _ _
    _ ≤ (‖P - 1‖ * ‖X‖) * ‖Q‖ + ‖X‖ * ‖Q - 1‖ :=
      add_le_add ((rectangular_norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (rectangular_norm_mul_le _ _) (norm_nonneg Q)))
        (rectangular_norm_mul_le _ _)
    _ ≤ (‖(u : B) - 1‖ * ‖X‖) * 1 + ‖X‖ * ‖(u : B) - 1‖ := by
      gcongr
    _ = 2 * ‖(u : B) - 1‖ * ‖X‖ := by ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Normalizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Published small-normalizer factorization and its consequence

The factorization hypothesis is Proposition 3.2 of
Cameron–Christensen–Sinclair–Smith–White–Wiggins, *Kadison–Kastler stable
factors*, Duke Math. J. 163 (2014), 2639–2686.  That proposition factors
two sufficiently close normalizers through the algebra and its commutant.

Its specialization at the identity gives the small exact normalizer lemma
used in §7 of *Universal strong Kadison–Kastler stability* (2026), with
radius one and displacement constant four, under the stated factorization
hypothesis.
-/

namespace KadisonKastler

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Unitaries in the commutant act trivially on the algebra by conjugation. -/
theorem unitaryConj_eq_self_of_mem_commutant {P : VonNeumannAlgebra H}
    {b : unitary (H →L[ℂ] H)} (hb : (b : H →L[ℂ] H) ∈ P.commutant)
    {x : H →L[ℂ] H} (hx : x ∈ P) : unitaryConj b x = x := by
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp hb x hx
  rw [unitaryConj, ← hcomm, mul_assoc,
    Unitary.mul_star_self_of_mem b.property, mul_one]

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PreparedPairCorrection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Preserving the first inclusion under the commutant correction

The second local embedding in the preparation argument is chosen in the
von Neumann algebra generated by the right algebra and the neighboring
commutant. That entire generated algebra commutes with the common left
algebra. These are algebraic consequences of the location of the chosen
unitary; its existence is not assumed here as a new perturbation theorem.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The right algebra and the neighboring commutant generate an algebra
commuting with the common left algebra. -/
theorem generated_right_correction_le_commutant
    (R S N : VonNeumannAlgebra H) (hRN : R ≤ N) (hSR : S ≤ R.commutant) :
    generatedVonNeumannAlgebra (S.toStarSubalgebra ⊔ N.commutant.toStarSubalgebra) ≤
      R.commutant := by
  apply generatedVonNeumannAlgebra_le_of_le
  apply sup_le hSR
  intro x hx
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro r hr
  exact VonNeumannAlgebra.mem_commutant_iff.mp hx r (hRN hr)

/-- Membership in a conjugated commutant is the same as conjugating
the membership in the original commutant. -/
theorem unitaryConj_mem_conjugated_commutant
    (N : VonNeumannAlgebra H) (w : unitary (H →L[ℂ] H))
    {x : H →L[ℂ] H} (hx : x ∈ N.commutant) :
    unitaryConj w x ∈ (unitaryConjugateAlgebra w N).commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  rintro y ⟨z, hz, rfl⟩
  have he := congrArg (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) w)
    (VonNeumannAlgebra.mem_commutant_iff.mp hx z hz)
  rw [map_mul, map_mul] at he
  exact he

/-- Inverse conjugation of a moved right algebra gives the desired
right inclusion for the corrected neighboring algebra. -/
theorem right_inclusion_of_moved_right_algebra
    (S N : VonNeumannAlgebra H) (w : unitary (H →L[ℂ] H))
    (hmove : ∀ s ∈ S, unitaryConj w s ∈ N.commutant) :
    S ≤ (unitaryConjugateAlgebra (star w) N).commutant := by
  intro s hs
  have hm := unitaryConj_mem_conjugated_commutant N (star w) (hmove s hs)
  simpa only [unitaryConj_star_unitaryConj] using hm

/-- A correction from the indicated generated algebra preserves the
first, literal common inclusion and establishes the second one. -/
theorem preparedPair_second_correction
    (R S N : VonNeumannAlgebra H) (hRN : R ≤ N) (hSR : S ≤ R.commutant)
    (w : unitary (H →L[ℂ] H))
    (hw : (w : H →L[ℂ] H) ∈ generatedVonNeumannAlgebra
      (S.toStarSubalgebra ⊔ N.commutant.toStarSubalgebra))
    (hmove : ∀ s ∈ S, unitaryConj w s ∈ N.commutant) :
    R ≤ unitaryConjugateAlgebra (star w) N ∧
      S ≤ (unitaryConjugateAlgebra (star w) N).commutant := by
  have hwR : (w : H →L[ℂ] H) ∈ R.commutant :=
    generated_right_correction_le_commutant R S N hRN hSR hw
  refine ⟨?_, right_inclusion_of_moved_right_algebra S N w hmove⟩
  apply le_unitaryConjugateAlgebra_star w
  intro r hr
  simpa only [unitaryConj_eq_self_of_mem_commutant hwR hr] using hRN hr

/-- The corrected pair has the same elementary gap loss as any unitary
movement of the neighbor. -/
theorem preparedPair_second_correction_gap
    (M N : VonNeumannAlgebra H) (w : unitary (H →L[ℂ] H)) :
    kkDistance M (unitaryConjugateAlgebra (star w) N) ≤
      kkDistance M N + 2 * ‖(w : H →L[ℂ] H) - 1‖ := by
  have hs : ‖((star w : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ =
      ‖(w : H →L[ℂ] H) - 1‖ := by
    simpa only [Unitary.coe_star, star_sub, star_one] using
      norm_star ((w : H →L[ℂ] H) - 1)
  simpa only [hs] using
    (kkDistance_conjugate_le (M := M) (conjugates_unitaryConjugateAlgebra (star w) N))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PreparedRightGraphBridge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Prepared graph comparison from common right actions

The vector and conjugation identities are imposed only on the
shared increasing matrix algebra. In particular, no tracial state on either
ambient algebra is needed. The relative right-action data imply the required
centralizer identities, and matrix averaging transfers relative irreducibility
to the nearby algebra.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance preparedRightGraphOrder_r628590_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance preparedRightGraphStarOrder_r628590_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance preparedRightGraphOperatorOrder_r628590_1 : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance preparedRightGraphOperatorStarOrder_r628590_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
/-- The source right algebra commutes with the common left algebra. -/
theorem commonRightAlgebra_le_commutant
    (M R S : VonNeumannAlgebra H) (hRM : R ≤ M) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hrightM : ∀ r ∈ R, conjugationOperator J r ∈ M.commutant)
    (hS : (S : Set (H →L[ℂ] H)) =
      conjugationOperator J '' (R : Set (H →L[ℂ] H))) :
    S ≤ R.commutant := by
  intro s hs
  change s ∈ (S : Set (H →L[ℂ] H)) at hs
  rw [hS] at hs
  obtain ⟨r, hr, rfl⟩ := hs
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  exact VonNeumannAlgebra.mem_commutant_iff.mp (hrightM r hr) a (hRM ha)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateRightIrreducibility
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Relative irreducibility in the conjugate right algebra

The scalar relative commutant property transports through the actual
conjugate-linear operator map. In standard position its ambient image is
the commutant, so the source's left irreducibility supplies the right one.
The same central-vector identity supplies both orbit correspondences.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem conjugateRightAlgebra_mono
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {R M : VonNeumannAlgebra H} (hRM : R ≤ M) :
    conjugateRightAlgebra J hJ R ≤ conjugateRightAlgebra J hJ M := by
  rintro _ ⟨r, hr, rfl⟩
  exact ⟨r, hRM hr, rfl⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateMatrixStages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Actual matrix stages in the conjugate right algebra

Conjugation changes the scalar coefficients by complex conjugation, while
the conjugated matrix-unit entries retain their usual product laws. Thus
the right algebra is generated by actual increasing full matrix stages.
This lets the same finite averaging argument transfer its irreducibility
to a nearby commutant.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem conjugateMatrixUnits_hom (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : MatrixUnitSystem ι (H →L[ℂ] H)) (a : Matrix ι ι ℂ) :
    (conjugateMatrixUnits J hJ E).hom (fun i j => star (a i j)) =
      conjugationOperator J (E.hom a) := by
  change (∑ i, ∑ j, star (a i j) • conjugationOperator J (E.entry i j)) =
    conjugationOperator J (E.hom a)
  simp only [MatrixUnitSystem.hom_apply, conjugationOperator_sum_p0,
    conjugationOperator_smul]

theorem conjugation_mem_conjugateMatrixUnits (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : MatrixUnitSystem ι (H →L[ℂ] H)) {x : H →L[ℂ] H} (hx : x ∈ E.algebra) :
    conjugationOperator J x ∈ (conjugateMatrixUnits J hJ E).algebra := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨(fun i j => star (a i j)), conjugateMatrixUnits_hom J hJ E a⟩

theorem conjugateMatrixUnits_mono (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (d : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra)) :
    Monotone (fun n => (conjugateMatrixUnits J hJ (E n)).algebra) := by
  intro i j hij
  apply ((conjugateMatrixUnits J hJ (E i)).algebra_le_iff
    (conjugateMatrixUnits J hJ (E j)).algebra).mpr
  intro a b
  exact conjugation_mem_conjugateMatrixUnits J hJ (E j)
    (hmono hij ((E i).entry_mem a b))

/-- The weakly generated right algebra is exactly generated by the
conjugated finite matrix stages. -/
theorem conjugateRightAlgebra_generated_matrixStages
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (d : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H)) :
    conjugateRightAlgebra J hJ (generatedVonNeumannAlgebra (⨆ n, (E n).algebra)) =
      generatedVonNeumannAlgebra (⨆ n, (conjugateMatrixUnits J hJ (E n)).algebra) := by
  let R := generatedVonNeumannAlgebra (⨆ n, (E n).algebra)
  let S := generatedVonNeumannAlgebra (⨆ n, (conjugateMatrixUnits J hJ (E n)).algebra)
  have hRS : R ≤ conjugateRightAlgebra J hJ S := by
    apply generatedVonNeumannAlgebra_le_of_le
    apply iSup_le
    intro n
    apply ((E n).algebra_le_iff (conjugateRightAlgebra J hJ S).toStarSubalgebra).mpr
    intro i j
    refine ⟨(conjugateMatrixUnits J hJ (E n)).entry i j, ?_, ?_⟩
    · exact subset_generatedVonNeumannAlgebra _
        ((le_iSup (fun n => (conjugateMatrixUnits J hJ (E n)).algebra) n)
          ((conjugateMatrixUnits J hJ (E n)).entry_mem i j))
    · exact conjugationOperator_twice J hJ ((E n).entry i j)
  apply le_antisymm
  · rintro _ ⟨r, hr, rfl⟩
    obtain ⟨s, hs, he⟩ := hRS hr
    rw [← he, conjugationOperator_twice J hJ]
    exact hs
  · apply generatedVonNeumannAlgebra_le_of_le
    apply iSup_le
    intro n
    apply ((conjugateMatrixUnits J hJ (E n)).algebra_le_iff
      (conjugateRightAlgebra J hJ R).toStarSubalgebra).mpr
    intro i j
    exact ⟨(E n).entry i j,
      subset_generatedVonNeumannAlgebra _ ((le_iSup (fun n => (E n).algebra) n)
        ((E n).entry_mem i j)), rfl⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixNearInclusion
attribute [-instance] _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
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

protected theorem mono (h : MatrixNearInclusion M N γ) (hγη : γ ≤ η) :
    MatrixNearInclusion M N η := by
  intro n X hX hn
  obtain ⟨Y, hY, hYn, hclose⟩ := h n X hX hn
  exact ⟨Y, hY, hYn, hclose.trans hγη⟩

attribute [local instance] OAI.KadisonKastler.MatrixNearInclusion.matrixNearOrder
attribute [local instance] OAI.KadisonKastler.MatrixNearInclusion.matrixNearStarOrder
/-- Moving the target algebra changes every matrix bound by at most the
complete displacement of the conjugation. -/
theorem conjugate_right (h : MatrixNearInclusion M N γ)
    (u : unitary (H →L[ℂ] H)) :
    MatrixNearInclusion M (unitaryConjugateAlgebra u N)
      (γ + 2 * ‖(u : H →L[ℂ] H) - 1‖) := by
  intro n X hX hn
  obtain ⟨Y, hY, hYn, hc⟩ := h n X hX hn
  let e := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u
  let Z := CStarMatrix.mapₗ e.toAlgEquiv.toLinearMap Y
  refine ⟨Z, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨Y i j, hY i j, rfl⟩
  · exact (injective_starAlgHom_matrix_norm e.toStarAlgHom e.injective Y).le.trans hYn
  · have hd := complete_unitaryConjugation_sub_id u n n Y
    have he : CStarMatrix.mapₗ (unitaryConjugationLinear u - LinearMap.id) Y = Z - Y := by
      ext i j
      rfl
    rw [he] at hd
    have hZY : ‖Y - Z‖ ≤ 2 * ‖(u : H →L[ℂ] H) - 1‖ := by
      rw [norm_sub_rev]
      exact hd.trans (mul_le_of_le_one_right (by positivity) hYn)
    exact (norm_sub_le_norm_sub_add_norm_sub X Y Z).trans (add_le_add hc hZY)

/-- Moving the source algebra has the same matrix displacement bound. -/
theorem conjugate_left (h : MatrixNearInclusion M N γ)
    (u : unitary (H →L[ℂ] H)) :
    MatrixNearInclusion (unitaryConjugateAlgebra u M) N
      (γ + 2 * ‖(u : H →L[ℂ] H) - 1‖) := by
  intro n X hX hn
  let e := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u
  let X₀ := CStarMatrix.mapₗ e.symm.toAlgEquiv.toLinearMap X
  have hX₀ : ∀ i j, X₀ i j ∈ M := by
    intro i j
    obtain ⟨a, ha, he⟩ := hX i j
    change e a = X i j at he
    change e.symm (X i j) ∈ M
    rw [← he, e.symm_apply_apply]
    exact ha
  have hX₀n : ‖X₀‖ ≤ 1 :=
    (injective_starAlgHom_matrix_norm e.symm.toStarAlgHom e.symm.injective X).le.trans hn
  obtain ⟨Y, hY, hYn, hc⟩ := h n X₀ hX₀ hX₀n
  refine ⟨Y, hY, hYn, ?_⟩
  have hd := complete_unitaryConjugation_sub_id u n n X₀
  have he : CStarMatrix.mapₗ (unitaryConjugationLinear u - LinearMap.id) X₀ = X - X₀ := by
    apply Matrix.ext
    intro i j
    change e (e.symm (X i j)) - e.symm (X i j) = X i j - e.symm (X i j)
    rw [e.apply_symm_apply]
  rw [he] at hd
  have hXX₀ : ‖X - X₀‖ ≤ 2 * ‖(u : H →L[ℂ] H) - 1‖ :=
    hd.trans (mul_le_of_le_one_right (by positivity) hX₀n)
  exact (norm_sub_le_norm_sub_add_norm_sub X X₀ Y).trans (by linarith)

end MatrixNearInclusion

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixPairPreparation
attribute [-instance] _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
attribute [-simp] _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.PointedMatrixSites.wordOperator_cons _root_.OAI.KadisonKastler.PointedMatrixSites.wordVector_cons _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.centralVectorDefect_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulTensorHom_intertwines _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rightVectorLinear_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialMatrixAmplification_apply _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

namespace OAI

/-! # Two-sided matrix preparation of an expected finite subalgebra

The first constructed matrix embedding makes the finite algebra common. The second,
localized matrix embedding aligns its conjugate right algebra without destroying
the first inclusion. All matrix and ordinary-gap losses are calculated
from the actual two unitaries. The expected vector is then proved cyclic
and separating for the corrected neighbor.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.matrixPairPreparationStarOrder
private theorem norm_star_unitary_sub_one (a : unitary (H →L[ℂ] H)) :
    ‖((star a : unitary (H →L[ℂ] H)) : H →L[ℂ] H) - 1‖ =
      ‖(a : H →L[ℂ] H) - 1‖ := by
  simpa only [Unitary.coe_star, star_sub, star_one] using
    norm_star ((a : H →L[ℂ] H) - 1)

attribute [local instance] OAI.KadisonKastler.matrixPairPreparationOrder
/-- Actual two-correction preparation, including the matrix error and
cyclic/separating conclusions needed by the modular spectral theorem.
The trace belongs only to `R`; the vector state on `M` is its composition
with the supplied expectation. -/
theorem exists_matrixPair_preparation_oai
    (hDistance : ∀ Q : VonNeumannAlgebra H,
      PublishedBlockCommutantApproximation (Algebra Q) H)
    (M N R : VonNeumannAlgebra H) (hRM : R ≤ M)
    (τ : FaithfulTracialState (Algebra R))
    (P : Algebra M →L[ℂ] Algebra R) (hP : P 1 = 1)
    (hleft : ∀ (r : Algebra R) (x : Algebra M),
      P (StarSubalgebra.inclusion hRM r * x) = r * P x)
    (hright : ∀ (r : Algebra R) (x : Algebra M),
      P (x * StarSubalgebra.inclusion hRM r) = P x * r)
    (Ω : H) (hΩ : ∀ x : Algebra M, expectedTrace τ P x = inner ℂ Ω (x.val Ω))
    (d : ModularConjugationData M Ω)
    (s : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (s n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hR : R = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hirr : ∀ T ∈ M, (∀ r ∈ R, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : H →L[ℂ] H))
    {γ : ℝ} (hγ : 0 < γ) (hsmall : γ < 1 / 200000)
    (hgap : kkDistance M N < γ)
    (hMN : MatrixNearInclusion M N γ) (hNM : MatrixNearInclusion N M γ) :
    ∃ a b : unitary (H →L[ℂ] H),
      ‖(a : H →L[ℂ] H) - 1‖ ≤ 150 * γ ∧
      ‖(b : H →L[ℂ] H) - 1‖ ≤ 45300 * γ ∧
      let N₂ := unitaryConjugateAlgebra (star b) (unitaryConjugateAlgebra (star a) N)
      R ≤ N₂ ∧
      conjugateRightAlgebra d.conjugation d.involutive R ≤ N₂.commutant ∧
      MatrixNearInclusion M N₂ (90901 * γ) ∧
      MatrixNearInclusion N₂ M (90901 * γ) ∧
      kkDistance M N₂ < 90902 * γ ∧
      DenseRange (algebraVectorMap N₂ Ω) ∧
      Function.Injective (algebraVectorMap N₂ Ω) ∧
      DenseRange (algebraVectorMap N₂.commutant Ω) ∧
      Function.Injective (algebraVectorMap N₂.commutant Ω) := by
  obtain ⟨hunit, hrightM, hvector⟩ := d.expected_right_data hRM τ P hP hleft hright hΩ
  have : Nontrivial H := by
    refine ⟨⟨Ω, 0, ?_⟩⟩
    intro hz
    rw [hz, norm_zero] at hunit
    exact zero_ne_one hunit
  obtain ⟨a, _, hmove, hna⟩ := exists_localized_unitary_matrixUnits_embedding
    s E hmono hR hγ.le (by linarith)
    (nearInclusion_mono_left hRM (nearInclusion_of_kkDistance_lt hgap))
  have hRa := le_unitaryConjugateAlgebra_star a hmove
  have hda := preparedPair_second_correction_gap M N a
  let N₁ := unitaryConjugateAlgebra (star a) N
  have hMN₁ : MatrixNearInclusion M N₁ (169 * γ) :=
    (hMN.conjugate_right (star a)).mono (by
      rw [norm_star_unitary_sub_one]
      linarith)
  have hN₁M : MatrixNearInclusion N₁ M (169 * γ) :=
    (hNM.conjugate_left (star a)).mono (by
      rw [norm_star_unitary_sub_one]
      linarith)
  have hd₁ : kkDistance M N₁ < 301 * γ := by
    have hd : kkDistance M N₁ ≤ kkDistance M N + 2 * ‖(a : H →L[ℂ] H) - 1‖ := hda
    linarith
  have hd₁' : kkDistance M.commutant N₁.commutant ≤ 602 * γ := by
    have hd := hMN₁.commutant_kkDistance_le hN₁M (by positivity)
      (hDistance M) (hDistance N₁)
    linarith
  let S := conjugateRightAlgebra d.conjugation d.involutive R
  have hSM : S ≤ M.commutant := by
    rw [← d.commutant]
    exact conjugateRightAlgebra_mono d.conjugation d.involutive hRM
  have hSR : S ≤ R.commutant := commonRightAlgebra_le_commutant M R S hRM
    d.conjugation hrightM (conjugateRightAlgebra_coe d.conjugation d.involutive R)
  have hnear : NearInclusion S N₁.commutant (170 * γ) :=
    nearInclusion_mono_left hSM
      (hN₁M.commutant_nearInclusion (by positivity) (hDistance N₁) (by linarith))
  have hS : S = generatedVonNeumannAlgebra
      (⨆ n, (conjugateMatrixUnits d.conjugation d.involutive (E n)).algebra) := by
    dsimp [S]
    rw [hR]
    exact conjugateRightAlgebra_generated_matrixStages d.conjugation d.involutive s E
  obtain ⟨b, hbLocation, hbMove, hnb⟩ := exists_localized_unitary_matrixUnits_embedding s
    (fun n => conjugateMatrixUnits d.conjugation d.involutive (E n))
    (conjugateMatrixUnits_mono d.conjugation d.involutive s E hmono)
    hS (by positivity : 0 ≤ 170 * γ) (by linarith : 170 * γ ≤ 1 / 1152) hnear
  obtain ⟨hRb, hSb⟩ := preparedPair_second_correction R S N₁ hRa hSR b hbLocation hbMove
  have hdb : kkDistance M (unitaryConjugateAlgebra (star b) N₁) ≤
      kkDistance M N₁ + 300 * (302 * γ) := by
    have hd := preparedPair_second_correction_gap M N₁ b
    linarith
  have hnb' : ‖(b : H →L[ℂ] H) - 1‖ ≤ 45300 * γ := by linarith
  let N₂ := unitaryConjugateAlgebra (star b) N₁
  have hMN₂ : MatrixNearInclusion M N₂ (90901 * γ) :=
    (hMN₁.conjugate_right (star b)).mono (by
      rw [norm_star_unitary_sub_one]
      linarith)
  have hN₂M : MatrixNearInclusion N₂ M (90901 * γ) :=
    (hN₁M.conjugate_left (star b)).mono (by
      rw [norm_star_unitary_sub_one]
      linarith)
  have hd₂ : kkDistance M N₂ < 90902 * γ := by
    have hd : kkDistance M N₂ ≤ kkDistance M N₁ + 300 * (302 * γ) := hdb
    linarith
  have hcyclic := expected_modular_corrected_cyclic_separating M N₁ R hRM τ P hP
    hleft hright Ω hΩ d s E hmono hR hirr b hRb hSb
    (by linarith) (by linarith)
  exact ⟨a, b, by linarith, hnb', hRb, hSb, hMN₂, hN₂M, hd₂, hcyclic⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_matrixPair_preparation_oai.{u_1} := @OAI.KadisonKastler.exists_matrixPair_preparation_oai.{u_1}
