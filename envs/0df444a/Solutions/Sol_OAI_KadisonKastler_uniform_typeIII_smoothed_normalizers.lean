-- Prove2me | solution 1 for OAI.KadisonKastler.uniform_typeIII_smoothed_normalizers
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:18:04.661571+00:00
-- url     : https://prove2.me/submissions/5f6a8092-63d7-4271-b9a8-fb3c575892e8

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
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
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
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
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
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
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K065
import Definitions.Def_Q260K066
import Theorems.Thm_OAI_KadisonKastler_TypeIIIFactor_exists_nonzero_projection_partition
import Theorems.Thm_OAI_KadisonKastler_exists_normalizer_of_smoothed_approximation
import Theorems.Thm_OAI_KadisonKastler_normalizer_distance_quadratic
import Theorems.Thm_OAI_KadisonKastler_uniform_typeIII_infinitesimal_bound

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommutatorRangeError
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The unit-ball defect in the infinitesimal normalizer estimate -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commutatorRangeError_bddAbove (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    BddAbove ((fun x : Algebra M =>
      Metric.infDist (commutatorAlong M.toStarSubalgebra.subtype T x) (M : Set (H →L[ℂ] H))) ''
        {x | ‖x‖ ≤ 1}) := by
  refine ⟨2 * ‖T‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  calc
    _ ≤ dist (commutatorAlong M.toStarSubalgebra.subtype T x) 0 :=
      Metric.infDist_le_dist_of_mem M.zero_mem
    _ = ‖T * x.val - x.val * T‖ := by rw [dist_zero_right, commutatorAlong_apply]; rfl
    _ ≤ ‖T‖ * ‖x‖ + ‖x‖ * ‖T‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ 2 * ‖T‖ := by
      have hx' : ‖x‖ ≤ 1 := hx
      nlinarith [norm_nonneg T, norm_nonneg x]

theorem commutatorRangeError_nonneg (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    0 ≤ commutatorRangeError M T := by
  exact Metric.infDist_nonneg.trans (le_csSup (commutatorRangeError_bddAbove M T)
    ⟨0, by simp, rfl⟩)

theorem commutatorRangeError_bounds_unitBall (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (x : Algebra M) (hx : ‖x‖ ≤ 1) :
    Metric.infDist (commutatorAlong M.toStarSubalgebra.subtype T x) (M : Set (H →L[ℂ] H)) ≤
      commutatorRangeError M T :=
  le_csSup (commutatorRangeError_bddAbove M T) ⟨x, hx, rfl⟩

theorem commutator_approximation_of_rangeError_lt (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) {δ : ℝ} (hδ : commutatorRangeError M T < δ) :
    ∀ x : Algebra M, ∃ y : Algebra M,
      ‖T * x.val - x.val * T - y.val‖ ≤ δ * ‖x‖ := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact ⟨0, by simp⟩
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let u : Algebra M := (‖x‖⁻¹ : ℂ) • x
  have hu : ‖u‖ ≤ 1 := by
    dsimp [u]
    rw [norm_smul]
    change ‖((‖x‖ : ℂ)⁻¹)‖ * ‖x‖ ≤ 1
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hxpos, inv_mul_cancel₀ hxpos.ne']
  have hdist := (commutatorRangeError_bounds_unitBall M T u hu).trans_lt hδ
  obtain ⟨y, hy, hnear⟩ := (Metric.infDist_lt_iff (show (M : Set (H →L[ℂ] H)).Nonempty from
    ⟨0, M.zero_mem⟩)).mp hdist
  refine ⟨(‖x‖ : ℂ) • (⟨y, hy⟩ : Algebra M), ?_⟩
  let D := commutatorAlong M.toStarSubalgebra.subtype T
  have hxu : (‖x‖ : ℂ) • u = x := by
    change (‖x‖ : ℂ) • ((‖x‖ : ℂ)⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hxpos.ne'), one_smul]
  have he : D x - (‖x‖ : ℂ) • y = (‖x‖ : ℂ) • (D u - y) := by
    calc
      D x - (‖x‖ : ℂ) • y = D ((‖x‖ : ℂ) • u) - (‖x‖ : ℂ) • y := by rw [hxu]
      _ = (‖x‖ : ℂ) • (D u - y) := by rw [map_smul, smul_sub]
  change ‖D x - (‖x‖ : ℂ) • y‖ ≤ _
  rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
  have hnear' : ‖D u - y‖ < δ := by simpa only [dist_eq_norm] using hnear
  nlinarith

universe u

attribute [local instance] OAI.KadisonKastler.rangeErrorSourceOrder
attribute [local instance] OAI.KadisonKastler.rangeErrorSourceStarOrder
theorem uniform_typeIII_selfAdjoint_infinitesimal_estimate
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ P : MatrixTypeIIIFactorModel.{u},
      PublishedBlockCommutantApproximation (Algebra P.M) P.H) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : MatrixTypeIIIFactorModel.{u},
      ∀ T : P.H →L[ℂ] P.H, IsSelfAdjoint T →
        Metric.infDist T (selfAdjointAlgebraCommutantSum P.M) ≤ C * commutatorRangeError P.M T := by
  obtain ⟨C, hC, hbound⟩ := uniform_typeIII_infinitesimal_bound hSpectral hCompare hSakai hDistance
  refine ⟨C, hC, fun P T hT => ?_⟩
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  have hδ : commutatorRangeError P.M T < r / C :=
    (lt_div_iff₀ hC).mpr (by nlinarith)
  have h := hbound P T hT (r / C) ((commutatorRangeError_nonneg P.M T).trans hδ.le)
    (commutator_approximation_of_rangeError_lt P.M T hδ)
  exact h.trans_eq (by field_simp)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Normalizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- Unitaries belonging to the algebra normalize it. -/
theorem conjugates_self_of_mem {P : VonNeumannAlgebra H}
    {a : unitary (H →L[ℂ] H)} (ha : (a : H →L[ℂ] H) ∈ P) :
    Conjugates a P P := by
  change unitaryConj a '' (P : Set (H →L[ℂ] H)) = (P : Set (H →L[ℂ] H))
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem ha hx) (star_mem ha)
  · intro hy
    refine ⟨unitaryConj (star a) y, ?_, ?_⟩
    · exact mul_mem (mul_mem (star_mem ha) hy)
        (by simpa only [Unitary.coe_star, star_star] using ha)
    · simpa only [star_star] using unitaryConj_star_unitaryConj (star a) y

/-- Unitaries in the commutant act trivially on the algebra by conjugation. -/
theorem unitaryConj_eq_self_of_mem_commutant {P : VonNeumannAlgebra H}
    {b : unitary (H →L[ℂ] H)} (hb : (b : H →L[ℂ] H) ∈ P.commutant)
    {x : H →L[ℂ] H} (hx : x ∈ P) : unitaryConj b x = x := by
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp hb x hx
  rw [unitaryConj, ← hcomm, mul_assoc,
    Unitary.mul_star_self_of_mem b.property, mul_one]

theorem conjugates_self_of_mem_commutant {P : VonNeumannAlgebra H}
    {b : unitary (H →L[ℂ] H)} (hb : (b : H →L[ℂ] H) ∈ P.commutant) :
    Conjugates b P P := by
  change unitaryConj b '' (P : Set (H →L[ℂ] H)) = (P : Set (H →L[ℂ] H))
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [unitaryConj_eq_self_of_mem_commutant hb hy] using hy
  · intro hx
    exact ⟨x, hx, unitaryConj_eq_self_of_mem_commutant hb hx⟩

/-- A product of an algebra unitary and a commutant unitary normalizes the algebra. -/
theorem conjugates_self_of_separate_factors {P : VonNeumannAlgebra H}
    {a b : unitary (H →L[ℂ] H)} (ha : (a : H →L[ℂ] H) ∈ P)
    (hb : (b : H →L[ℂ] H) ∈ P.commutant) : Conjugates (a * b) P P :=
  (conjugates_self_of_mem_commutant hb).trans (conjugates_self_of_mem ha)

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InfinitesimalExponentiation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Exponentiating the infinitesimal normalizer estimate -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem one_mem_separateUnitaryProducts (M : VonNeumannAlgebra H) :
    1 ∈ separateUnitaryProducts M := by
  exact ⟨1, 1, M.one_mem, M.commutant.one_mem, by simp⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizerPathBarrier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The continuous barrier in the approximate-normalizer path argument -/

namespace KadisonKastler

theorem continuous_quadratic_barrier {I : Set ℝ} (hI : IsPreconnected I)
    (hzero : 0 ∈ I) (b : ℝ → ℝ) (hb : ContinuousOn b I) (hbzero : b 0 = 0)
    (hnonneg : ∀ t ∈ I, 0 ≤ b t) {A L r : ℝ}
    (hA : A < r / 2) (hL : 0 ≤ L) (hr : 0 < r) (hLr : L * r ≤ 1 / 2)
    (hquad : ∀ t ∈ I, b t < 2 * r → b t ≤ A + L * (b t) ^ 2) :
    ∀ t ∈ I, b t ≤ 2 * A := by
  have hsmall : ∀ t ∈ I, b t < r := by
    intro t ht
    by_contra hnot
    have hrt : r ≤ b t := le_of_not_gt hnot
    obtain ⟨s, hs, hsr⟩ := hI.intermediate_value₂ hzero ht hb continuousOn_const
      (show b 0 ≤ r by rw [hbzero]; exact hr.le) hrt
    have hq := hquad s hs (by rw [hsr]; linarith)
    rw [hsr] at hq
    have hbound := mul_le_mul_of_nonneg_right hLr hr.le
    nlinarith
  intro t ht
  have hbt := hsmall t ht
  have hq := hquad t ht (by linarith)
  have hb0 := hnonneg t ht
  have hlinear : L * b t ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hbt.le hL).trans hLr
  have hbound := mul_le_mul_of_nonneg_right hlinear hb0
  nlinarith

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreMatrixData
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable equivalent projection families give full matrix corners

The input here is actual projection and partial-isometry data in a represented
von Neumann algebra.  No existence of a semifinite decomposition is assumed as
a published input.  Once such a decomposition has been constructed, the
matrix-corner machinery applies to the explicit operators `v i * star (v j)`.
-/

namespace KadisonKastler

open Generator.Tracial
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

namespace FullMatrixCorner

theorem ofEquivalentProjectionFamily_entry_mem
    (E : Submodule ℂ H) [CompleteSpace E]
    (p : ℕ → AlgebraProjection M) (v : ℕ → Algebra M)
    (hvi : ∀ i, star (v i) * v i = (p 0).val)
    (hvf : ∀ i, v i * star (v i) = (p i).val)
    (horth : Pairwise (fun i j => (p i).val * (p j).val = 0))
    (hp0 : ((p 0).val : H →L[ℂ] H) = E.starProjection)
    (htotal : ∀ x : H, HasSum (fun i => ((p i).val : H →L[ℂ] H) x) x)
    (i j : ℕ) :
    (ofEquivalentProjectionFamily E p v hvi hvf horth hp0 htotal).entry i j ∈ M :=
  (projectionFamilyEntry v i j).property

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIIMatrixCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable matrix corners in type III factors

The absence of nonzero finite projections gives a proper isometry. Its
wandering projections are nonzero and orthogonal. A projection supremum
completes them to a partition of one; the published comparison theorem
then joins the pieces by partial isometries.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped BigOperators Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- Countable full matrix corners exist in every separably acting type III
factor. Only the published comparison of nonzero projections is used. -/
theorem TypeIIIFactor.exists_fullMatrixCorner [TopologicalSpace.SeparableSpace H]
    (hM : TypeIIIFactor M) (hCompare : PublishedTypeIIIProjectionComparison.{u}) :
    ∃ p : AlgebraProjection M, p.val ≠ 0 ∧
      ∃ F : FullMatrixCorner (typeIIIInitialSpace p), ∀ i j, F.entry i j ∈ M := by
  obtain ⟨d, hd, ho, hsum⟩ := hM.exists_nonzero_projection_partition
  have ha : ∀ i, ∃ a : Algebra M, star a * a = 1 ∧ a * star a = (d i).val :=
    fun i => hCompare H M hM (d i).val (d i).property (hd i)
  choose a hai haf using ha
  let v (i : ℕ) : Algebra M := a i * star (a 0)
  have hvi (i : ℕ) : star (v i) * v i = (d 0).val := by
    change star (a i * star (a 0)) * (a i * star (a 0)) = (d 0).val
    rw [star_mul, star_star]
    calc
      _ = a 0 * (star (a i) * a i) * star (a 0) := by simp only [mul_assoc]
      _ = (d 0).val := by rw [hai, mul_one, haf]
  have hvf (i : ℕ) : v i * star (v i) = (d i).val := by
    change (a i * star (a 0)) * star (a i * star (a 0)) = (d i).val
    rw [star_mul, star_star]
    calc
      _ = a i * (star (a 0) * a 0) * star (a i) := by simp only [mul_assoc]
      _ = (d i).val := by rw [hai, mul_one, haf]
  let F := FullMatrixCorner.ofEquivalentProjectionFamily (typeIIIInitialSpace (d 0))
    d v hvi hvf ho (typeIIIInitialSpace_projection (d 0)) hsum
  exact ⟨d 0, hd 0, F,
    FullMatrixCorner.ofEquivalentProjectionFamily_entry_mem _ d v hvi hvf ho
      (typeIIIInitialSpace_projection (d 0)) hsum⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIIInfinitesimal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform infinitesimal estimate for all separably acting type III factors

The matrix corner is constructed from a proper isometry and the published
comparison theorem. The tolerance therefore precedes the Hilbert space and
factor without any matrix-corner hypothesis in the conclusion.
-/

namespace KadisonKastler

noncomputable section

universe u

attribute [local instance] OAI.KadisonKastler.typeIIIInfinitesimalSourceOrder
attribute [local instance] OAI.KadisonKastler.typeIIIInfinitesimalSourceStarOrder
theorem uniform_typeIII_selfAdjoint_estimate
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H,
        PublishedBlockCommutantApproximation (Algebra M) H) :
    ∃ K : ℝ, 0 < K ∧ ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [TopologicalSpace.SeparableSpace H], ∀ M : VonNeumannAlgebra H,
      TypeIIIFactor M → ∀ h : selfAdjoint (H →L[ℂ] H),
        Metric.infDist (h : H →L[ℂ] H) (selfAdjointAlgebraCommutantSum M) ≤
          K * commutatorRangeError M (h : H →L[ℂ] H) := by
  obtain ⟨K, hK, hbound⟩ := uniform_typeIII_selfAdjoint_infinitesimal_estimate
    hSpectral hCompare hSakai (fun P => hDistance P.H P.M)
  refine ⟨K, hK, ?_⟩
  intro H _ _ _ _ M hM h
  obtain ⟨p, _, F, hF⟩ := hM.exists_fullMatrixCorner hCompare
  let P : MatrixTypeIIIFactorModel := {
    H := H
    M := M
    isTypeIII := hM
    E := typeIIIInitialSpace p
    matrixCorner := F
    matrix_mem := hF }
  exact hbound P h h.property

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIINormalizerPath
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A uniform bound for paths of approximate normalizers of type III factors -/

namespace KadisonKastler

open scoped Topology

noncomputable section

universe u

attribute [local instance] OAI.KadisonKastler.typeIIIPathSourceOrder
attribute [local instance] OAI.KadisonKastler.typeIIIPathSourceStarOrder
theorem uniform_typeIII_approximate_normalizer_path
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H,
        PublishedBlockCommutantApproximation (Algebra M) H) :
    ∃ e0 C : ℝ, 0 < e0 ∧ 0 < C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [TopologicalSpace.SeparableSpace H],
      ∀ (M : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ (I : Set ℝ), IsPreconnected I → 0 ∈ I →
      ∀ (v : ℝ → unitary (H →L[ℂ] H)), ContinuousOn v I → v 0 = 1 →
      ∀ e : ℝ, 0 ≤ e → e < e0 →
      (∀ t ∈ I, ∀ x ∈ unitBall M, Metric.infDist (unitaryConj (v t) x)
        (M : Set (H →L[ℂ] H)) ≤ e) →
      ∀ t ∈ I, Metric.infDist ((v t : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
        (separateUnitaryProducts M) ≤ C * e := by
  obtain ⟨K, hK, hlinear⟩ := uniform_typeIII_selfAdjoint_estimate
    hSpectral hCompare hSakai hDistance
  let r : ℝ := min (1 / 4) (1 / (64 * K))
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hrquarter : r ≤ 1 / 4 := min_le_left _ _
  have hKr : K * r ≤ 1 / 64 := by
    calc
      K * r ≤ K * (1 / (64 * K)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK.le
      _ = 1 / 64 := by field_simp
  refine ⟨r / (4 * K), 2 * K, by positivity, by positivity, ?_⟩
  intro H _ _ _ _ M hM I hI hzero v hv hvzero e _ he hdefect t ht
  let b (s : ℝ) := Metric.infDist (v s : H →L[ℂ] H) (separateUnitaryProducts M)
  have hb : ContinuousOn b I :=
    (Metric.continuous_infDist_pt (separateUnitaryProducts M)).comp_continuousOn
      (continuous_subtype_val.comp_continuousOn hv)
  have hbzero : b 0 = 0 := by
    dsimp [b]
    rw [hvzero, OneMemClass.coe_one]
    exact Metric.infDist_zero_of_mem (one_mem_separateUnitaryProducts M)
  have hKe : K * e < r / 2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4 * K)).mp he
    nlinarith
  have hbarrier := continuous_quadratic_barrier hI hzero b hb hbzero
    (fun _ _ => Metric.infDist_nonneg) hKe (show 0 ≤ 16 * K by positivity) hr
    (show (16 * K) * r ≤ 1 / 2 by nlinarith) ?_
  · simpa only [b, mul_assoc] using hbarrier t ht
  · intro s hs hbs
    have hsmall : b s < 1 := by linarith
    exact normalizer_distance_quadratic M hK.le (hlinear H M hM) (v s)
      (hdefect s hs) hsmall

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SmoothedNormalizerPaths
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Exact normalizers from approximate-normalizer smoothing paths

The path estimate produces algebra/commutant products independently at each
smoothing scale. The UCP limit argument then recovers one exact normalizer
without requiring the chosen products, or the polar paths, to converge.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.smoothedPathStarOrder
private theorem exists_normalizer_of_infDist_lt
    (M : VonNeumannAlgebra H) (v : unitary (H →L[ℂ] H)) {a : ℝ}
    (ha : Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M) < a) :
    ∃ p : unitary (H →L[ℂ] H), Conjugates p M M ∧
      ‖(p : H →L[ℂ] H) - v‖ < a := by
  obtain ⟨p, hp, hvp⟩ := (Metric.infDist_lt_iff
    (show (separateUnitaryProducts M).Nonempty from
      ⟨1, one_mem_separateUnitaryProducts M⟩)).mp ha
  obtain ⟨b, c, hb, hc, rfl⟩ := hp
  refine ⟨b * c, conjugates_self_of_separate_factors hb hc, ?_⟩
  simpa only [dist_eq_norm, norm_sub_rev] using hvp

attribute [local instance] OAI.KadisonKastler.smoothedPathOrder
theorem exists_normalizer_of_smoothed_infDist
    (M : VonNeumannAlgebra H) (W : unitary (H →L[ℂ] H))
    (hCorrection : PublishedMultiplicationCorrection (unitaryConjugateAlgebra W M))
    (hCommutant : PublishedBlockCommutantApproximation
      (Algebra (unitaryConjugateAlgebra W M)) H)
    (E : ℕ → unitary (H →L[ℂ] H)) (Q : ℕ → H →L[ℂ] H)
    (hstar : ∀ x, Tendsto (fun n => star (Q n) x) atTop
      (𝓝 (star (W : H →L[ℂ] H) x)))
    {a d B g : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hB : 0 ≤ B)
    (hE : ∀ n, Metric.infDist (E n : H →L[ℂ] H) (separateUnitaryProducts M) < a)
    (hEQ : ∀ n, ‖(E n : H →L[ℂ] H) - Q n‖ ≤ d)
    (hQ : ∀ n, ‖Q n‖ ≤ B)
    (hsmall : (1 + B) * (a + d) < 1 / 1000)
    (hge : g + (1 + B) * (a + d) < 1)
    (hgap : kkDistance (unitaryConjugateAlgebra W M) M < g) :
    ∃ p : unitary (H →L[ℂ] H), Conjugates p M M ∧
      ‖(p : H →L[ℂ] H) - W‖ ≤ 128 * ((1 + B) * (a + d)) := by
  choose V hVM hVE using fun n => exists_normalizer_of_infDist_lt M (E n) (hE n)
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  apply exists_normalizer_of_smoothed_approximation M W hCorrection hCommutant ω
    V hVM Q (fun x => (hstar x).mono_left (Ultrafilter.of_le atTop)) hB (add_nonneg ha hd)
    hQ ?_ hsmall hge hgap
  intro n
  exact (norm_sub_le_norm_sub_add_norm_sub (V n : H →L[ℂ] H) (E n) (Q n)).trans
    (add_le_add (hVE n).le (hEQ n))

/-- Smoothing estimates give normalizers with constants chosen before
the Hilbert space and the type III factor. -/
theorem uniform_typeIII_smoothed_normalizers_oai
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H,
        PublishedBlockCommutantApproximation (Algebra M) H) :
    ∃ e0 K : ℝ, 0 < e0 ∧ 0 < K ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [TopologicalSpace.SeparableSpace H],
      ∀ (M : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ W : unitary (H →L[ℂ] H),
      PublishedMultiplicationCorrection (unitaryConjugateAlgebra W M) →
      ∀ (E : ℕ → ℝ → unitary (H →L[ℂ] H)) (Q : ℕ → H →L[ℂ] H)
        (t e d B g : ℝ),
      0 < e → e < e0 → 0 ≤ d → 0 ≤ B →
      (∀ n, Continuous (E n)) → (∀ n, E n 0 = 1) →
      (∀ n s, ∀ x ∈ unitBall M,
        Metric.infDist (unitaryConj (H := H) (E n s) x) (M : Set (H →L[ℂ] H)) ≤ e) →
      (∀ x, Tendsto (fun n => star (Q n) x) atTop (𝓝 (star (W : H →L[ℂ] H) x))) →
      (∀ n, ‖(E n t : H →L[ℂ] H) - Q n‖ ≤ d) →
      (∀ n, ‖Q n‖ ≤ B) →
      (1 + B) * ((K + 1) * e + d) < 1 / 1000 →
      g + (1 + B) * ((K + 1) * e + d) < 1 →
      kkDistance (unitaryConjugateAlgebra W M) M < g →
      ∃ p : unitary (H →L[ℂ] H), Conjugates p M M ∧
        ‖(p : H →L[ℂ] H) - W‖ ≤ 128 * ((1 + B) * ((K + 1) * e + d)) := by
  obtain ⟨e0, K, he0, hK, hpath⟩ := uniform_typeIII_approximate_normalizer_path
    hSpectral hCompare hSakai hDistance
  refine ⟨e0, K, he0, hK, ?_⟩
  intro H _ _ _ _ M hM W hCorrection E Q t e d B g he he0' hd hB hcont hzero
    hdefect hstar hEQ hQ hsmall hge hgap
  apply exists_normalizer_of_smoothed_infDist M W hCorrection (hDistance H _)
    (fun n => E n t) Q hstar (mul_nonneg (by linarith) he.le) hd hB ?_
    hEQ hQ hsmall hge hgap
  intro n
  have hb := hpath H M hM Set.univ isPreconnected_univ (Set.mem_univ 0)
    (E n) (hcont n).continuousOn (hzero n) e he.le he0'
    (fun s _ x hx => hdefect n s x hx) t (Set.mem_univ t)
  exact hb.trans_lt (by nlinarith)

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.uniform_typeIII_smoothed_normalizers_oai.{u} := @OAI.KadisonKastler.uniform_typeIII_smoothed_normalizers_oai.{u}
