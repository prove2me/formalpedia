-- Prove2me | solution 1 for OAI.KadisonKastler.uniform_typeIII_infinitesimal_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:14:34.806774+00:00
-- url     : https://prove2.me/submissions/eac09730-0c8f-4cd4-b20e-30767e444457

import Mathlib
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
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
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
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
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
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K028
import Definitions.Def_Q260K066
import Theorems.Thm_OAI_KadisonKastler_typeIII_eventually_approximate_algebra_add_commutant

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SelfAdjointApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Self-adjoint approximation by the algebra and its commutant -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem selfAdjointAlgebraCommutantSum_zero (M : VonNeumannAlgebra H) :
    0 ∈ selfAdjointAlgebraCommutantSum M :=
  ⟨0, 0, M.zero_mem, M.commutant.zero_mem, IsSelfAdjoint.zero _, IsSelfAdjoint.zero _,
    (zero_add 0).symm⟩

theorem selfAdjointAlgebraCommutantSum_add (M : VonNeumannAlgebra H)
    {s t : H →L[ℂ] H} (hs : s ∈ selfAdjointAlgebraCommutantSum M)
    (ht : t ∈ selfAdjointAlgebraCommutantSum M) :
    s + t ∈ selfAdjointAlgebraCommutantSum M := by
  obtain ⟨a, b, ha, hb, hsa, hsb, rfl⟩ := hs
  obtain ⟨c, d, hc, hd, hsc, hsd, rfl⟩ := ht
  exact ⟨a + c, b + d, M.add_mem ha hc, M.commutant.add_mem hb hd,
    hsa.add hsc, hsb.add hsd, by abel⟩

theorem selfAdjointAlgebraCommutantSum_smul (M : VonNeumannAlgebra H)
    (r : ℝ) {s : H →L[ℂ] H} (hs : s ∈ selfAdjointAlgebraCommutantSum M) :
    r • s ∈ selfAdjointAlgebraCommutantSum M := by
  obtain ⟨a, b, ha, hb, hsa, hsb, rfl⟩ := hs
  refine ⟨r • a, r • b, ?_, ?_, (show IsSelfAdjoint r from rfl).smul hsa,
    (show IsSelfAdjoint r from rfl).smul hsb, smul_add r a b⟩
  · rw [← Complex.coe_smul]
    exact M.smul_mem ha _
  · rw [← Complex.coe_smul]
    exact M.commutant.smul_mem hb _

theorem realPart_mem_vonNeumann (M : VonNeumannAlgebra H) {a : H →L[ℂ] H} (ha : a ∈ M) :
    (realPart a : H →L[ℂ] H) ∈ M := by
  rw [realPart_apply_coe, ← Complex.coe_smul]
  exact M.smul_mem (M.add_mem ha (star_mem (s := M.toStarSubalgebra) ha)) _

theorem exists_selfAdjoint_sum_approximation
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M.commutant) :
    ∃ s ∈ selfAdjointAlgebraCommutantSum M, ‖T - s‖ ≤ ‖T - (a + b)‖ := by
  let ra : H →L[ℂ] H := realPart a
  let rb : H →L[ℂ] H := realPart b
  refine ⟨ra + rb, ⟨ra, rb, realPart_mem_vonNeumann M ha,
    realPart_mem_vonNeumann M.commutant hb, (realPart a).property,
    (realPart b).property, rfl⟩, ?_⟩
  have he : T - (ra + rb) = (realPart (T - (a + b)) : H →L[ℂ] H) := by
    rw [map_sub, map_add]
    change T - (ra + rb) = (realPart T : H →L[ℂ] H) - (ra + rb)
    rw [hT.coe_realPart]
  rw [he]
  exact realPart.norm_le (T - (a + b))

theorem selfAdjoint_of_mem_algebraCommutantSum (M : VonNeumannAlgebra H)
    {s : H →L[ℂ] H} (hs : s ∈ selfAdjointAlgebraCommutantSum M) : IsSelfAdjoint s := by
  obtain ⟨a, b, _, _, ha, hb, rfl⟩ := hs
  exact ha.add hb

theorem commutator_mem_of_mem_algebraCommutantSum (M : VonNeumannAlgebra H)
    {s : H →L[ℂ] H} (hs : s ∈ selfAdjointAlgebraCommutantSum M)
    {x : H →L[ℂ] H} (hx : x ∈ M) : s * x - x * s ∈ M := by
  obtain ⟨a, b, ha, hb, _, _, rfl⟩ := hs
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp hb x hx
  have he : (a + b) * x - x * (a + b) = a * x - x * a := by
    rw [add_mul, mul_add, ← hcomm]
    abel
  rw [he]
  exact M.sub_mem (M.mul_mem ha hx) (M.mul_mem hx ha)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UniformInfinitesimalCutoff
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralVectorSpace_complete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A uniform infinitesimal cutoff for represented type III factors

The tolerance is chosen before the Hilbert space and factor. The estimate
uses a countable full matrix corner.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

attribute [local instance] OAI.KadisonKastler.uniformInfinitesimalSourceOrder
attribute [local instance] OAI.KadisonKastler.uniformInfinitesimalSourceStarOrder
theorem uniform_typeIII_infinitesimal_cutoff
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ P : MatrixTypeIIIFactorModel.{u},
      PublishedBlockCommutantApproximation (Algebra P.M) P.H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ P : MatrixTypeIIIFactorModel.{u},
      ∀ T : P.H →L[ℂ] P.H, IsSelfAdjoint T → ‖T‖ ≤ 2 →
        (∀ x : Algebra P.M, ∃ y : Algebra P.M,
          ‖T * (x : P.H →L[ℂ] P.H) - (x : P.H →L[ℂ] P.H) * T -
            (y : P.H →L[ℂ] P.H)‖ ≤ ε * ‖x‖) →
        ∃ a b : P.H →L[ℂ] P.H, a ∈ P.M ∧ b ∈ P.M.commutant ∧
          ‖T - (a + b)‖ < 1 := by
  classical
  by_contra! hbad
  have hex (j : ℕ) := hbad (1 / (j + 1 : ℝ)) (by positivity)
  choose P t hself hnorm happrox hfar using hex
  let T : VaryingBoundedSequence (fun j => (P j).H →L[ℂ] (P j).H) :=
    ⟨t, memℓp_infty ⟨2, by rintro _ ⟨j, rfl⟩; exact hnorm j⟩⟩
  have hT : IsSelfAdjoint T := by
    apply Subtype.ext
    funext j
    exact (hself j).star_eq
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hε : Tendsto (fun j : ℕ => 1 / (j + 1 : ℝ)) (ω : Filter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left hω
  have hεbound (j : ℕ) : 1 / (j + 1 : ℝ) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < (j + 1 : ℝ))).mpr
    norm_num
  have hevent := typeIII_eventually_approximate_algebra_add_commutant
    hSpectral hCompare hSakai (fun j => (P j).M) (fun j => (P j).isTypeIII)
    (fun j => hDistance (P j)) (fun j => (P j).E) (fun j => (P j).matrixCorner)
    (fun j => (P j).matrix_mem) ω T hT (fun j => 1 / (j + 1 : ℝ)) hε
    (fun j => by positivity) hεbound happrox 1 zero_lt_one
  obtain ⟨j, a, b, ha, hb, hab⟩ := hevent.exists
  exact (not_lt_of_ge (hfar j a b ha hb)) hab

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UniformInfinitesimalBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The uniform linear infinitesimal estimate with matrix-corner data

Subtract a self-adjoint approximating sum and normalize by its distance.
The bounded cutoff then contradicts any failure of the linear estimate.
No closedness of the algebra-plus-commutant sum is used.
-/

namespace KadisonKastler

noncomputable section

universe u

attribute [local instance] OAI.KadisonKastler.uniformInfinitesimalBoundSourceOrder
attribute [local instance] OAI.KadisonKastler.uniformInfinitesimalBoundSourceStarOrder
private theorem infinitesimal_bound_of_cutoff (P : MatrixTypeIIIFactorModel.{u})
    {ε : ℝ} (hε : 0 < ε)
    (hcut : ∀ D : P.H →L[ℂ] P.H, IsSelfAdjoint D → ‖D‖ ≤ 2 →
      (∀ x : Algebra P.M, ∃ y : Algebra P.M,
        ‖D * (x : P.H →L[ℂ] P.H) - (x : P.H →L[ℂ] P.H) * D -
          (y : P.H →L[ℂ] P.H)‖ ≤ ε * ‖x‖) →
      ∃ a b : P.H →L[ℂ] P.H, a ∈ P.M ∧ b ∈ P.M.commutant ∧
        ‖D - (a + b)‖ < 1)
    (T : P.H →L[ℂ] P.H) (hT : IsSelfAdjoint T) {δ : ℝ} (hδ : 0 ≤ δ)
    (happrox : ∀ x : Algebra P.M, ∃ y : Algebra P.M,
      ‖T * (x : P.H →L[ℂ] P.H) - (x : P.H →L[ℂ] P.H) * T -
        (y : P.H →L[ℂ] P.H)‖ ≤ δ * ‖x‖) :
    Metric.infDist T (selfAdjointAlgebraCommutantSum P.M) ≤ δ / ε := by
  let S := selfAdjointAlgebraCommutantSum P.M
  let d := Metric.infDist T S
  by_contra hle
  have hd : δ / ε < d := lt_of_not_ge hle
  have hdpos : 0 < d := (div_nonneg hδ hε.le).trans_lt hd
  have hS : S.Nonempty := ⟨0, selfAdjointAlgebraCommutantSum_zero P.M⟩
  obtain ⟨s, hs, hnear⟩ := (Metric.infDist_lt_iff hS).mp
    (show Metric.infDist T S < 2 * d by change d < 2 * d; linarith)
  have hnear' : ‖T - s‖ < 2 * d := by simpa only [dist_eq_norm] using hnear
  let D : P.H →L[ℂ] P.H := d⁻¹ • (T - s)
  have hD : IsSelfAdjoint D := (show IsSelfAdjoint (d⁻¹) from rfl).smul
    (hT.sub (selfAdjoint_of_mem_algebraCommutantSum P.M hs))
  have hDn : ‖D‖ ≤ 2 := by
    dsimp [D]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdpos)]
    have h := mul_le_mul_of_nonneg_left hnear'.le (inv_nonneg.mpr hdpos.le)
    have he : d⁻¹ * (2 * d) = 2 := by field_simp
    exact h.trans_eq he
  have hδd : d⁻¹ * δ ≤ ε := by
    have hlt : δ < d * ε := (div_lt_iff₀ hε).mp hd
    have hdiv : δ / d ≤ ε := (div_le_iff₀ hdpos).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  have hDapprox (x : Algebra P.M) : ∃ y : Algebra P.M,
      ‖D * (x : P.H →L[ℂ] P.H) - (x : P.H →L[ℂ] P.H) * D -
        (y : P.H →L[ℂ] P.H)‖ ≤ ε * ‖x‖ := by
    obtain ⟨y, hy⟩ := happrox x
    let c : Algebra P.M := ⟨s * x.val - x.val * s,
      commutator_mem_of_mem_algebraCommutantSum P.M hs x.property⟩
    refine ⟨(d⁻¹ : ℝ) • (y - c), ?_⟩
    have he : D * x.val - x.val * D - ((d⁻¹ : ℝ) • (y - c) : Algebra P.M) =
        (d⁻¹ : ℝ) • (T * x.val - x.val * T - y.val) := by
      change D * x.val - x.val * D - (d⁻¹ : ℝ) • (y.val - (s * x.val - x.val * s)) = _
      dsimp [D]
      rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, ← smul_sub]
      congr 1
      noncomm_ring
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdpos)]
    calc
      _ ≤ d⁻¹ * (δ * ‖x‖) := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hdpos.le)
      _ ≤ ε * ‖x‖ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hδd (norm_nonneg x)
  obtain ⟨a, b, ha, hb, hab⟩ := hcut D hD hDn hDapprox
  obtain ⟨s0, hs0, hDs0⟩ := exists_selfAdjoint_sum_approximation P.M D hD a b ha hb
  have hsmall : ‖D - s0‖ < 1 := hDs0.trans_lt hab
  have hresult : s + d • s0 ∈ S := selfAdjointAlgebraCommutantSum_add P.M hs
    (selfAdjointAlgebraCommutantSum_smul P.M d hs0)
  have hnorm : ‖T - (s + d • s0)‖ < d := by
    have hscale : d • D = T - s := by
      dsimp [D]
      rw [smul_smul, mul_inv_cancel₀ hdpos.ne', one_smul]
    have he : T - (s + d • s0) = d • (D - s0) := by
      rw [smul_sub, hscale]
      abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hdpos]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hsmall hdpos
  have hdist := Metric.infDist_le_dist_of_mem (x := T) hresult
  have hdist' : d ≤ ‖T - (s + d • s0)‖ := by
    simpa only [dist_eq_norm] using hdist
  exact (not_lt_of_ge hdist') hnorm

theorem uniform_typeIII_infinitesimal_bound_oai
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ P : MatrixTypeIIIFactorModel.{u},
      PublishedBlockCommutantApproximation (Algebra P.M) P.H) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : MatrixTypeIIIFactorModel.{u},
      ∀ T : P.H →L[ℂ] P.H, IsSelfAdjoint T → ∀ δ : ℝ, 0 ≤ δ →
        (∀ x : Algebra P.M, ∃ y : Algebra P.M,
          ‖T * (x : P.H →L[ℂ] P.H) - (x : P.H →L[ℂ] P.H) * T -
            (y : P.H →L[ℂ] P.H)‖ ≤ δ * ‖x‖) →
        Metric.infDist T (selfAdjointAlgebraCommutantSum P.M) ≤ C * δ := by
  obtain ⟨ε, hε, hcut⟩ := uniform_typeIII_infinitesimal_cutoff hSpectral hCompare hSakai hDistance
  refine ⟨ε⁻¹, inv_pos.mpr hε, fun P T hT δ hδ happrox => ?_⟩
  simpa only [div_eq_mul_inv, mul_comm] using
    infinitesimal_bound_of_cutoff P hε (hcut P) T hT hδ happrox

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.uniform_typeIII_infinitesimal_bound_oai.{u} := @OAI.KadisonKastler.uniform_typeIII_infinitesimal_bound_oai.{u}
