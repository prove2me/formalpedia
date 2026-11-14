-- Prove2me | solution 1 for OAI.KadisonKastler.exists_commonTracialPosition_of_matrixStages
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T16:12:30.226256+00:00
-- url     : https://prove2.me/submissions/018df1ab-ac4a-49d9-b13b-807e6a92b7ab

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
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
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
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
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
import Definitions.Def_OAIQ075A032
import Definitions.Def_Q260K089
import Definitions.Def_Q260K044
import Theorems.Thm_OAI_Generator_Tracial_traceHilbertVonNeumann_wotClosed
import Theorems.Thm_OAI_Generator_isII1Factor_of_starAlgEquiv
import Theorems.Thm_OAI_KadisonKastler_countableDiagonal_isII1
import Theorems.Thm_OAI_KadisonKastler_cyclicCommonMatrixUnits_generated
import Theorems.Thm_OAI_KadisonKastler_cyclicCommonMatrixUnits_mono
import Theorems.Thm_OAI_KadisonKastler_exists_commonPositionData_of_matrix_cyclic_neighbor
import Theorems.Thm_OAI_KadisonKastler_exists_common_cyclic_projection_alignment
import Theorems.Thm_OAI_KadisonKastler_exists_faithfulCyclic_standardTracialPosition
import Theorems.Thm_OAI_KadisonKastler_faithfulCyclic_diagonal_corner_eq
import Theorems.Thm_OAI_KadisonKastler_kkDistance_reducing_commutants_after_alignment
import Theorems.Thm_OAI_KadisonKastler_nearInclusion_reducing_commutants_after_alignment
import Theorems.Thm_OAI_KadisonKastler_relative_ambient_scalar_of_common_equivs
import Theorems.Thm_OAI_KadisonKastler_unitaryConjugateAlgebra_isII1

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonCyclicSubalgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.rescaledGraphSubspace_complete _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The common subalgebra in the faithful cyclic representation -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  (M R : VonNeumannAlgebra H) (hRM : R ≤ M)

theorem cyclicCommon_restrict (r : Algebra R) :
    faithfulCyclicEquiv M (coordinateInclusion hRM r) =
      coordinateInclusion (cyclicCommon_le M R hRM) (cyclicCommonEquiv M R hRM r) := rfl

theorem cyclicCommon_neighbor_restrict (P : VonNeumannAlgebra (faithfulCyclicSpace M))
    (e : Algebra R →⋆ₐ[ℂ] Algebra P)
    (he : ∀ r, (e r).val = faithfulCyclicHom M (coordinateInclusion hRM r))
    (r : Algebra R) :
    e r = coordinateInclusion (cyclicCommon_le_neighbor M R hRM P e he)
      (cyclicCommonEquiv M R hRM r) := by
  apply Subtype.ext
  exact he r

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NearInclusionDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalizing strict near-inclusion approximants -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H}

/-- An algebra approximant can be normalized into its unit ball with at
most twice the original error. -/
theorem exists_unitBall_approx_of_algebra_approx
    {x y : H →L[ℂ] H} (hx : ‖x‖ ≤ 1) (hy : y ∈ N) :
    ∃ z ∈ unitBall N, ‖x - z‖ ≤ 2 * ‖x - y‖ := by
  by_cases hy1 : ‖y‖ ≤ 1
  · exact ⟨y, ⟨hy, hy1⟩, by nlinarith [norm_nonneg (x - y)]⟩
  have hypos : 0 < ‖y‖ := by linarith
  let z : H →L[ℂ] H := (‖y‖⁻¹ : ℂ) • y
  have hznorm : ‖z‖ = 1 := norm_smul_inv_norm (norm_pos_iff.mp hypos)
  have hyz : ‖y - z‖ = ‖y‖ - 1 := by
    have hi : 0 ≤ 1 - ‖y‖⁻¹ := by
      have ht : ‖y‖⁻¹ ≤ 1 := (inv_le_one₀ hypos).mpr (lt_of_not_ge hy1).le
      linarith
    have he : y - z = ((1 - ‖y‖⁻¹ : ℝ) : ℂ) • y := by
      simp only [z, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv,
        sub_smul, one_smul]
    rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hi]
    rw [sub_mul, one_mul, inv_mul_cancel₀ hypos.ne']
  have hnorm : ‖y‖ - 1 ≤ ‖x - y‖ := by
    have ht := norm_add_le (y - x) x
    rw [sub_add_cancel, norm_sub_rev] at ht
    linarith
  refine ⟨z, ⟨N.toStarSubalgebra.smul_mem hy _, hznorm.le⟩, ?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub x y z).trans (by rw [hyz]; linarith)

/-- The published strict near-inclusion convention controls the closed
unit balls with the factor two from normalization. -/
theorem exists_unitBall_approx_of_nearInclusion {γ : ℝ}
    (h : NearInclusion M N γ) {x : H →L[ℂ] H} (hx : x ∈ unitBall M) :
    ∃ y ∈ unitBall N, ‖x - y‖ < 2 * γ := by
  obtain ⟨γ', hγ', happrox⟩ := h
  obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff ⟨0, zero_mem N⟩).mp
    ((happrox x hx).trans_lt hγ')
  obtain ⟨z, hz, hxz⟩ := exists_unitBall_approx_of_algebra_approx hx.2 hy
  have hxy' : ‖x - y‖ < γ := by simpa only [dist_eq_norm] using hxy
  exact ⟨z, hz, hxz.trans_lt (by linarith)⟩

theorem kkDistance_le_two_mul_of_nearInclusions {γ : ℝ} (hγ : 0 ≤ γ)
    (hMN : NearInclusion M N γ) (hNM : NearInclusion N M γ) :
    kkDistance M N ≤ 2 * γ := by
  apply Metric.hausdorffDist_le_of_mem_dist (by positivity)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := exists_unitBall_approx_of_nearInclusion hMN hx
    exact ⟨y, hy, by simpa only [dist_eq_norm] using hxy.le⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := exists_unitBall_approx_of_nearInclusion hNM hx
    exact ⟨y, hy, by simpa only [dist_eq_norm] using hxy.le⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DiagonalGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Exact preservation of the operator-norm gap by countable diagonalization -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitBall_countableDiagonal (M : VonNeumannAlgebra H) :
    unitBall (countableDiagonalAlgebra M) =
      l2Diagonal '' unitBall M := by
  ext T
  constructor
  · intro hT
    obtain ⟨a, ha, rfl⟩ := countableDiagonalHom_surjective_unitBall M T hT.1 hT.2
    exact ⟨a.val, ⟨a.property, ha⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨subset_generatedVonNeumannAlgebra _ ⟨⟨a, ha.1⟩, rfl⟩,
      (norm_l2Diagonal H a).le.trans ha.2⟩

theorem kkDistance_countableDiagonal (M N : VonNeumannAlgebra H) :
    kkDistance (countableDiagonalAlgebra M) (countableDiagonalAlgebra N) =
      kkDistance M N := by
  have hi : Isometry (l2Diagonal (E := H)) := by
    apply isometry_iff_dist_eq.mpr
    intro a b
    simp only [dist_eq_norm]
    change ‖(l2DiagonalHom (E := H)) a - (l2DiagonalHom (E := H)) b‖ = ‖a - b‖
    rw [← map_sub]
    exact norm_l2Diagonal H (a - b)
  change Metric.hausdorffDist _ _ = Metric.hausdorffDist _ _
  rw [unitBall_countableDiagonal, unitBall_countableDiagonal]
  exact Metric.hausdorffDist_image hi

theorem kkDistance_lt_two_mul_of_nearInclusions {M N : VonNeumannAlgebra H}
    {γ : ℝ} (hγ : 0 < γ) (hMN : NearInclusion M N γ) (hNM : NearInclusion N M γ) :
    kkDistance M N < 2 * γ := by
  obtain ⟨a, ha, hMa⟩ := hMN
  obtain ⟨b, hb, hNb⟩ := hNM
  let c := max 0 (max a b)
  have hc : c < γ := max_lt hγ (max_lt ha hb)
  have hca : a ≤ c := (le_max_left a b).trans (le_max_right 0 (max a b))
  have hcb : b ≤ c := (le_max_right a b).trans (le_max_right 0 (max a b))
  have hc0 : 0 ≤ c := le_max_left _ _
  have hMc : NearInclusion M N ((c + γ) / 2) :=
    ⟨a, by linarith, hMa⟩
  have hNc : NearInclusion N M ((c + γ) / 2) :=
    ⟨b, by linarith, hNb⟩
  exact (kkDistance_le_two_mul_of_nearInclusions (by linarith) hMc hNc).trans_lt
    (by linarith)

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
-- module Solutions.OAIQ075_KS.KadisonKastler_ReducingFactorEquiv
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Faithful normal restriction of a factor to a nonzero reducing subspace -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial Filter
open scoped Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]
  (M : VonNeumannAlgebra H) (hE : E.starProjection ∈ M.commutant)
  (hE0 : E.starProjection ≠ 0) (hM : ScalarCenter M)

omit E hE hE0 hM in
theorem scalarCenter_of_isII1 (h : IsII1Factor M.toStarSubalgebra) : ScalarCenter M := by
  intro T hT hc
  obtain ⟨z, hz⟩ := traceHilbert_factor h ⟨T, hT⟩
    (fun a => Subtype.ext (hc a.val a.property))
  exact ⟨z, congrArg Subtype.val hz⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InitialCyclicNeighbor
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A faithful neighboring factor on the first factor's standard cyclic space -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]

theorem faithfulCyclic_projection_ne_zero (M : VonNeumannAlgebra H) :
    (faithfulCyclicSpace M).starProjection ≠ 0 := by
  intro hz
  have hv := (faithfulCyclicSpace M).starProjection_mem_subspace_eq_self
    (faithfulCyclicVector M)
  rw [hz, zero_apply] at hv
  have hn := norm_faithfulCyclicVector M
  have hv0 : faithfulCyclicVector M = 0 := Subtype.ext hv.symm
  rw [hv0, norm_zero] at hn
  exact zero_ne_one hn

theorem initial_cyclic_neighbor_of_alignment
    (M N R : VonNeumannAlgebra H) (hRM : R ≤ M) (hRN : R ≤ N)
    (hN : IsII1Factor N.toStarSubalgebra) {γ : ℝ}
    (u : unitary (CountableHilbertSum H →L[ℂ] CountableHilbertSum H))
    (huR : (u : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) ∈
      (countableDiagonalAlgebra R).commutant)
    (hp : (faithfulCyclicSpace M).starProjection ∈
      (unitaryConjugateAlgebra (star u) (countableDiagonalAlgebra N)).commutant)
    (hun : ‖(u : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1‖ ≤ 200000000 * γ) :
    ∃ (P : VonNeumannAlgebra (faithfulCyclicSpace M))
      (e : Algebra N ≃⋆ₐ[ℂ] Algebra P),
      IsII1Factor P.toStarSubalgebra ∧
      (∀ r : Algebra R,
        (e (coordinateInclusion hRN r)).val = faithfulCyclicHom M (coordinateInclusion hRM r)) ∧
      (∀ (a : Algebra M) (b : Algebra N), ‖b‖ ≤ 1 →
        ‖faithfulCyclicHom M a - (e b).val‖ ≤
          400000000 * γ + ‖a.val - b.val‖) ∧
      P = generatedVonNeumannAlgebra
        (commutantReducingHom (faithfulCyclicSpace M)
          (unitaryConjugateAlgebra (star u) (countableDiagonalAlgebra N)) hp).range := by
  let E := faithfulCyclicSpace M
  let D := unitaryConjugateAlgebra (star u) (countableDiagonalAlgebra N)
  let P := generatedVonNeumannAlgebra (commutantReducingHom E D hp).range
  have hD : IsII1Factor D.toStarSubalgebra :=
    unitaryConjugateAlgebra_isII1 (star u) (countableDiagonal_isII1 N hN)
  let f := reducingFactorEquiv E D hp (faithfulCyclic_projection_ne_zero M)
    (scalarCenter_of_isII1 D hD)
  let e : Algebra N ≃⋆ₐ[ℂ] Algebra P :=
    (countableDiagonalEquiv N).trans ((unitaryConjugateEquiv (star u)
      (countableDiagonalAlgebra N)).trans f)
  have he (b : Algebra N) :
      (e b).val = cornerCompression E (unitaryConj (star u) (l2Diagonal b.val)) := rfl
  have hstar : ‖((star u : unitary (CountableHilbertSum H →L[ℂ] CountableHilbertSum H)) :
      CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1‖ =
      ‖(u : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1‖ := by
    simpa only [Unitary.coe_star, star_sub, star_one] using norm_star
      ((u : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1)
  refine ⟨P, e, isII1Factor_of_starAlgEquiv e hN (traceHilbertVonNeumann_wotClosed P), ?_, ?_, rfl⟩
  · intro r
    rw [he]
    have hr : l2Diagonal r.val ∈ countableDiagonalAlgebra R :=
      subset_generatedVonNeumannAlgebra _ ⟨r, rfl⟩
    have hstarR : ((star u : unitary (CountableHilbertSum H →L[ℂ] CountableHilbertSum H)) :
        CountableHilbertSum H →L[ℂ] CountableHilbertSum H) ∈
        (countableDiagonalAlgebra R).commutant := star_mem huR
    change cornerCompression E (unitaryConj (star u) (l2Diagonal r.val)) = _
    rw [unitaryConj_eq_self_of_mem_commutant hstarR hr]
    rfl
  · intro a b hb
    have hleft : faithfulCyclicHom M a = cornerCompression E (l2Diagonal a.val) := rfl
    have hdiff : faithfulCyclicHom M a - (e b).val =
        cornerCompression E (l2Diagonal a.val - unitaryConj (star u) (l2Diagonal b.val)) := by
      exact (congrArg₂ (fun S T => S - T) hleft (he b)).trans
        ((cornerCompression E).map_sub _ _).symm
    apply (congrArg norm hdiff).le.trans
    apply (norm_cornerCompression_le E _).trans
    have hdist := norm_sub_le_norm_sub_add_norm_sub (l2Diagonal a.val)
      (l2Diagonal b.val) (unitaryConj (star u) (l2Diagonal b.val))
    have hmove := norm_unitaryConj_sub_le (star u) (l2Diagonal b.val)
    rw [hstar, norm_l2Diagonal H] at hmove
    have hd : ‖l2Diagonal a.val - l2Diagonal b.val‖ = ‖a.val - b.val‖ := by
      change ‖(l2DiagonalHom (E := H)) a.val - (l2DiagonalHom (E := H)) b.val‖ = _
      rw [← map_sub]
      exact norm_l2Diagonal H _
    rw [hd, norm_sub_rev (l2Diagonal b.val)] at hdist
    have hmove' : ‖unitaryConj (star u) (l2Diagonal b.val) - l2Diagonal b.val‖ ≤
        400000000 * γ := hmove.trans (by
      change 2 * ‖(u : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1‖ * ‖b‖ ≤ _
      nlinarith [norm_nonneg ((u : CountableHilbertSum H →L[ℂ] CountableHilbertSum H) - 1)])
    linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InitialCyclicCommutantNeighbor
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instSeparableSpaceSubtypePreLpPointedPowerConfigurationComplexMemAddSubgroupPointedPowerHilbert _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The initial cyclic neighbor with its two-sided commutant bound -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]

local instance cyclicNeighborCountableNontrivial_ref9a00_1 : Nontrivial (CountableHilbertSum H) :=
  nontrivial_of_ne (denseSeparatingUnitVector (H := H)) 0 (by
    intro h
    have hn := norm_denseSeparatingUnitVector (H := H)
    rw [h, norm_zero] at hn
    exact zero_ne_one hn)
theorem exists_initial_cyclic_commutant_neighbor
    (M N R : VonNeumannAlgebra H) (hRM : R ≤ M) (hRN : R ≤ N)
    (hM : IsII1Factor M.toStarSubalgebra) (hN : IsII1Factor N.toStarSubalgebra)
    {γ : ℝ} (hγ : 0 < γ) (hsmall : γ < 1 / 3200000000)
    (hMN : NearInclusion M N γ) (hNM : NearInclusion N M γ) :
    ∃ (P : VonNeumannAlgebra (faithfulCyclicSpace M))
      (e : Algebra N ≃⋆ₐ[ℂ] Algebra P),
      IsII1Factor P.toStarSubalgebra ∧
      (∀ r : Algebra R,
        (e (coordinateInclusion hRN r)).val = faithfulCyclicHom M (coordinateInclusion hRM r)) ∧
      (∀ (a : Algebra M) (b : Algebra N), ‖b‖ ≤ 1 →
        ‖faithfulCyclicHom M a - (e b).val‖ ≤ 400000000 * γ + ‖a.val - b.val‖) ∧
      NearInclusion (faithfulCyclicAlgebra M).commutant P.commutant (405000000 * γ) ∧
      kkDistance (faithfulCyclicAlgebra M).commutant P.commutant ≤ 810000000 * γ := by
  exact (exists_common_cyclic_projection_alignment (H := H) M N R hRM hRN hN
    (γ := γ) hγ (by linarith) hMN hNM).elim (fun u hu =>
      (initial_cyclic_neighbor_of_alignment (H := H) M N R hRM hRN hN (γ := γ)
        u hu.1 hu.2.1 hu.2.2.2).elim (fun P hP => hP.elim (fun e he => by
          have hgap : kkDistance (countableDiagonalAlgebra M) (countableDiagonalAlgebra N) <
              2 * γ := by
            rw [kkDistance_countableDiagonal]
            exact kkDistance_lt_two_mul_of_nearInclusions hγ hMN hNM
          have hnear := nearInclusion_reducing_commutants_after_alignment
            (faithfulCyclicSpace M) (countableDiagonalAlgebra M) (countableDiagonalAlgebra N)
            (countableDiagonal_isII1 N hN) (faithfulCyclic_projection_mem_diagonal_commutant M)
            u hu.2.1 hγ hsmall hgap hu.2.2.2
          have hdist := kkDistance_reducing_commutants_after_alignment
            (faithfulCyclicSpace M) (countableDiagonalAlgebra M) (countableDiagonalAlgebra N)
            (countableDiagonal_isII1 M hM) (countableDiagonal_isII1 N hN)
            (faithfulCyclic_projection_mem_diagonal_commutant M) u hu.2.1 hγ hsmall hgap hu.2.2.2
          rw [faithfulCyclic_diagonal_corner_eq, ← he.2.2.2] at hnear hdist
          exact ⟨P, e, he.1, he.2.1, he.2.2.1, hnear, hdist⟩)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCommonPositionConstruction
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixCentralVectorSpace_complete _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Constructed common tracial position for an increasing matrix subfactor

This proves the instance of CCSSWW, Lemma 4.10, used by the finite-factor
application. The common algebra is the actual increasing full-matrix closure.
-/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  {M N R : VonNeumannAlgebra H}

theorem exists_commonTracialPosition_of_matrixStages_oai
    (hRM : R ≤ M) (hRN : R ≤ N)
    (hM : IsII1Factor M.toStarSubalgebra) (hN : IsII1Factor N.toStarSubalgebra)
    (A : ℕ → FiniteMatrixStage R)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (hgen : FiniteMatrixStage.generatedVonNeumann A = R)
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    {γ : ℝ} (hγ : 0 < γ) (hsmall : γ < 174 / 1000000000000000)
    (hMN : NearInclusion M N γ) (hNM : NearInclusion N M γ) :
    Nonempty (CommonTracialPositionData M N R hRM hRN γ (faithfulCyclicSpace M)) := by
  obtain ⟨P, e, hP, he, hcomp, hnear, hdist⟩ :=
    exists_initial_cyclic_commutant_neighbor (H := H) M N R hRM hRN hM hN
      (γ := γ) hγ (by linarith) hMN hNM
  let C := cyclicCommonAlgebra M R hRM
  have hCL : C ≤ faithfulCyclicAlgebra M := cyclicCommon_le M R hRM
  let f : Algebra R →⋆ₐ[ℂ] Algebra P := e.toStarAlgHom.comp (coordinateInclusion hRN)
  have hf : ∀ r, (f r).val = faithfulCyclicHom M (coordinateInclusion hRM r) := he
  have hCP : C ≤ P := cyclicCommon_le_neighbor M R hRM P f hf
  have he' : ∀ r, e (coordinateInclusion hRN r) =
      coordinateInclusion hCP (cyclicCommonEquiv M R hRM r) :=
    cyclicCommon_neighbor_restrict M R hRM P f hf
  obtain ⟨p⟩ := exists_faithfulCyclic_standardTracialPosition M hM
  have hi : ∀ T ∈ faithfulCyclicAlgebra M, (∀ r ∈ C, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : faithfulCyclicSpace M →L[ℂ] faithfulCyclicSpace M) :=
    relative_ambient_scalar_of_common_equivs hRM hCL
      (faithfulCyclicEquiv M) (cyclicCommonEquiv M R hRM)
      (cyclicCommon_restrict M R hRM) hirr
  exact exists_commonPositionData_of_matrix_cyclic_neighbor hRM hRN hCL hCP
    (faithfulCyclicEquiv M) e (cyclicCommonEquiv M R hRM)
    (cyclicCommon_restrict M R hRM) he' p hP (fun n => (A n).size)
    (normalImageMatrixUnits (cyclicCommonHom M R hRM) A)
    (cyclicCommonMatrixUnits_mono M R hRM A hA)
    (cyclicCommonMatrixUnits_generated M R hRM A hA hgen)
    hi hγ hsmall hMN hNM (fun a b _ hb => hcomp a b hb) hnear hdist

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.exists_commonTracialPosition_of_matrixStages_oai.{u} := @OAI.KadisonKastler.exists_commonTracialPosition_of_matrixStages_oai.{u}
