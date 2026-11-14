-- Prove2me | solution 1 for OAI.KadisonKastler.exists_bounded_graphRow_signal_scale
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:56:15.6492+00:00
-- url     : https://prove2.me/submissions/a37e1989-dfa0-4b6f-bdb8-fddf8ebdcbe8

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
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
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
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
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K035
import Theorems.Thm_OAI_KadisonKastler_clippedGraphRow_error_le_scale
import Theorems.Thm_OAI_KadisonKastler_exists_bounded_rescaledGraph_signal
import Theorems.Thm_OAI_KadisonKastler_exists_matrixGraphRow_cost_le_480
import Theorems.Thm_OAI_KadisonKastler_norm_clippedGraphRow_le

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomizedPairing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Extracting the scalar commutator from randomized rows

Finite Cauchy–Schwarz bounds the two row errors without a factor for the
number of random choices. Together with the scalar commutator estimate
this gives the constant 141 in the amplification argument.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators Topology

noncomputable section

variable {Ω H : Type*} [Fintype Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [InnerProductSpace ℂ H] in
theorem finiteRMS_nonneg (v : Ω → H) : 0 ≤ finiteRMS v := Real.sqrt_nonneg _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RandomizedRMS
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Elementary norm bounds for finite random vectors -/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {Ω H : Type*} [Fintype Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [InnerProductSpace ℂ H] in
/-- Finite root mean square is the normalized direct-sum norm. -/
theorem finiteRMS_eq_norm (v : Ω → H) :
    finiteRMS v = (Real.sqrt (Fintype.card Ω : ℝ))⁻¹ * ‖WithLp.toLp 2 v‖ := by
  unfold finiteRMS
  rw [Fintype.expect_eq_sum_div_card, Real.sqrt_div (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [← PiLp.norm_sq_eq_of_L2, Real.sqrt_sq (norm_nonneg _)]
  exact div_eq_inv_mul _ _

omit [InnerProductSpace ℂ H] in
/-- Minkowski's inequality for the finite random vectors in the row construction. -/
theorem finiteRMS_add_le (v w : Ω → H) :
    finiteRMS (fun i => v i + w i) ≤ finiteRMS v + finiteRMS w := by
  rw [finiteRMS_eq_norm, finiteRMS_eq_norm, finiteRMS_eq_norm, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  exact norm_add_le (WithLp.toLp 2 v) (WithLp.toLp 2 w)

omit [InnerProductSpace ℂ H] in
/-- Squaring finite root mean square recovers its average of squares. -/
theorem finiteRMS_sq (v : Ω → H) :
    (finiteRMS v) ^ 2 = 𝔼 i, ‖v i‖ ^ 2 :=
  Real.sq_sqrt (expect_nonneg (fun _ _ => sq_nonneg _))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RescaledTomitaGraph
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Rescaled Tomita graphs in a fixed two-coordinate Hilbert space

A fixed conjugation identifies the conjugate copy of the Hilbert space
with the original one. In these coordinates the graph vector is
`(x Ω, c J (x* Ω))`. The same identification is used for both algebras.
No closability or modular spectral theorem is needed for the closed
linear graph subspace or the elementary projection comparison below.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The defining weighted graph norm, with no restriction on the scale. -/
theorem norm_rescaledGraphVector_sq (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (x : H →L[ℂ] H) :
    ‖rescaledGraphVector J Ω c x‖ ^ 2 = ‖x Ω‖ ^ 2 + c ^ 2 * ‖star x Ω‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, rescaledGraphVector_zero, rescaledGraphVector_one,
    norm_smul, J.norm_map, Real.norm_eq_abs, mul_pow, sq_abs]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RescaledGraphAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The common unitary action on rescaled graphs

Left and right multiplication by common unitaries acts on graph vectors
through one unitary of the fixed two-coordinate Hilbert space. Thus each
closed graph reduces this unitary whenever the right action belongs to
the relevant commutant and has the prescribed value on the common vector.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem right_operator_on_algebra_vector
    (P : VonNeumannAlgebra H) (Ω : H) (a b : H →L[ℂ] H)
    (ha : a ∈ P.commutant) (x : Algebra P) (hΩ : a Ω = b Ω) :
    a (x.val Ω) = x.val (b Ω) := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp ha x.val x.property
  calc
    a (x.val Ω) = x.val (a Ω) :=
      (congrArg (fun T : H →L[ℂ] H => T Ω) hc).symm
    _ = x.val (b Ω) := by rw [hΩ]

/-- Exact action on graph vectors, before any closure argument. -/
theorem rescaledGraphAction_vector
    (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (Ω : H) (c : ℝ) (r s : unitary (H →L[ℂ] H))
    (hsright : conjugationOperator J (star (s : H →L[ℂ] H)) ∈ P.commutant)
    (hrright : conjugationOperator J (r : H →L[ℂ] H) ∈ P.commutant)
    (hsΩ : conjugationOperator J (star (s : H →L[ℂ] H)) Ω = (s : H →L[ℂ] H) Ω)
    (hrΩ : conjugationOperator J (r : H →L[ℂ] H) Ω = star (r : H →L[ℂ] H) Ω)
    (x : Algebra P) :
    (rescaledGraphAction J hJ r s :
      TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
      (rescaledGraphVector J Ω c x.val) =
        rescaledGraphVector J Ω c ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change (rescaledGraphAction J hJ r s :
        TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
        (rescaledGraphVector J Ω c x.val) 0 =
      rescaledGraphVector J Ω c ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) 0
    simp only [rescaledGraphAction, graphDiagonalUnitary_apply_zero,
      rescaledGraphVector_zero, Submonoid.coe_mul, mul_apply_eq_comp,
      conjugationUnitary_coe, Unitary.coe_star]
    rw [right_operator_on_algebra_vector P Ω _ _ hsright x hsΩ]
  · change (rescaledGraphAction J hJ r s :
        TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
        (rescaledGraphVector J Ω c x.val) 1 =
      rescaledGraphVector J Ω c ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) 1
    simp only [rescaledGraphAction, graphDiagonalUnitary_apply_one,
      rescaledGraphVector_one, conjugationUnitary_coe]
    rw [LinearMapClass.map_smul_of_tower]
    congr 1
    change J (star (s : H →L[ℂ] H)
      (conjugationOperator J (r : H →L[ℂ] H) (J (J (star x.val Ω))))) =
        J (star ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) Ω)
    rw [hJ]
    have hc := right_operator_on_algebra_vector P Ω _ _ hrright (star x) hrΩ
    change conjugationOperator J (r : H →L[ℂ] H) (star x.val Ω) =
      star x.val (star (r : H →L[ℂ] H) Ω) at hc
    rw [hc]
    simp only [star_mul, mul_apply_eq_comp]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphOrbitSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Actual orbit samples retaining the rescaled graph signal

The finite matrix moment estimate and the Hilbert sign selection are
combined here. The signal is the image of the graph vector under the
specified bounded operator; its invariance is derived from the common
unitary graph action.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Commutation with the unitary graph action preserves the signal on
an actual two-sided orbit. -/
theorem norm_graphSignal_unitaryDoubleOrbit
    (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (Ω : H) (c : ℝ) (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (u v : unitary (H →L[ℂ] H))
    (hvright : conjugationOperator J (v : H →L[ℂ] H) ∈ M.commutant)
    (huright : conjugationOperator J (u : H →L[ℂ] H) ∈ M.commutant)
    (hvΩ : conjugationOperator J (v : H →L[ℂ] H) Ω = star (v : H →L[ℂ] H) Ω)
    (huΩ : conjugationOperator J (u : H →L[ℂ] H) Ω = star (u : H →L[ℂ] H) Ω)
    (hT : T * (rescaledGraphAction J hJ u (star v) :
        TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
      (rescaledGraphAction J hJ u (star v) :
        TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) * T)
    (x : H →L[ℂ] H) (hx : x ∈ M) :
    ‖T (rescaledGraphVector J Ω c (unitaryDoubleOrbit x u v))‖ =
      ‖T (rescaledGraphVector J Ω c x)‖ := by
  have hf := rescaledGraphAction_vector M J hJ Ω c u (star v)
    (by simpa only [Unitary.coe_star, star_star] using hvright) huright
    (by simpa only [Unitary.coe_star, star_star] using hvΩ) huΩ ⟨x, hx⟩
  change (rescaledGraphAction J hJ u (star v) :
      TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
      (rescaledGraphVector J Ω c x) =
    rescaledGraphVector J Ω c (unitaryDoubleOrbit x u v) at hf
  rw [← hf]
  have he := congrArg (fun A : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H =>
    A (rescaledGraphVector J Ω c x)) hT
  simp only [mul_apply_eq_comp] at he
  rw [he, Unitary.norm_map]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphRowClipping
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A common spectral cutoff for a replicated graph row

The cutoff acts on the left square of the entire row. Its norm is bounded
independently of the number of columns, while its normalized graph error
is controlled by the two fourth-moment sums in `graphRowCost`.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {I : Type*} [Fintype I]

attribute [local instance] OAI.KadisonKastler.graphRowClipOrder
attribute [local instance] OAI.KadisonKastler.graphRowClipStarOrder
theorem graphRowSquare_nonneg (Y : I → H →L[ℂ] H) : 0 ≤ graphRowSquare Y := by
  apply Finset.sum_nonneg
  intro i _
  simpa only [star_star] using star_mul_self_nonneg (star (Y i))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphRowMetric
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The normalized graph metric of a rectangular operator row

The second graph coordinate loses its rescaling factor after summing the
adjoint column. This is the exact matrix-level estimate used with
complete near-inclusion, without an ordinary-gap amplification claim.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- A continuous operator acts contractively on finite RMS up to its norm. -/
theorem finiteRMS_apply_le {I K : Type*} [Fintype I]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (T : H →L[ℂ] K) (v : I → H) :
    finiteRMS (fun i => T (v i)) ≤ ‖T‖ * finiteRMS v := by
  apply (sq_le_sq₀ (finiteRMS_nonneg _) (mul_nonneg (norm_nonneg T) (finiteRMS_nonneg v))).mp
  rw [mul_pow, finiteRMS_sq, finiteRMS_sq, Finset.mul_expect]
  apply Finset.expect_le_expect
  intro i _
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (v i)) 2

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- Constant pointwise norm gives the same norm in finite RMS. -/
theorem finiteRMS_eq_of_norm_eq {I : Type*} [Fintype I] [Nonempty I]
    (v : I → H) {C : ℝ} (hC : 0 ≤ C) (hv : ∀ i, ‖v i‖ = C) : finiteRMS v = C := by
  unfold finiteRMS
  simp only [hv, Fintype.expect_const, Real.sqrt_sq hC]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FlattenedGraphRow
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A bounded replicated row retaining the graph signal

A single cutoff of the row square preserves algebra membership and loses
at most one thirty-second of the graph signal in normalized mean square.
The cutoff and the row norm are independent of the row length.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.flattenedRowOrder
local instance flattenedRowStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

theorem clippedGraphRow_mem (M : VonNeumannAlgebra H) {I : Type*} [Fintype I]
    (β : ℝ) (Y : I → H →L[ℂ] H) (hY : ∀ i, Y i ∈ M) (i : I) :
    clippedGraphRow β Y i ∈ M := by
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_algebra M
  have hA : graphRowSquare Y ∈ M := by
    exact M.toStarSubalgebra.sum_mem (fun i _ =>
      M.mul_mem (hY i) (M.toStarSubalgebra.star_mem' (hY i)))
  have hS : CFC.sqrt (graphRowSquare Y) ∈ M.toStarSubalgebra := by
    rw [CFC.sqrt_eq_real_sqrt _ (graphRowSquare_nonneg Y), cfcₙ_eq_cfc]
    exact cfc_mem (𝕜' := ℂ) (S := StarSubalgebra ℂ (H →L[ℂ] H))
      (s := M.toStarSubalgebra) _ hA
  exact M.mul_mem (cfc_mem (𝕜' := ℂ) (S := StarSubalgebra ℂ (H →L[ℂ] H))
    (s := M.toStarSubalgebra) _ hS) (hY i)

/-- Every left matrix translate of an algebra element has exactly the
same graph signal when the actual graph action commutes with the defect. -/
theorem matrixGraphRow_signal_eq (M : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (z : H →L[ℂ] H) (hz : z ∈ M)
    (hcomm : ∀ a, a ∈ E.algebra → conjugationOperator J (star a) ∈ M.commutant)
    (hvector : ∀ a, a ∈ E.algebra → conjugationOperator J (star a) Ω = a Ω)
    (hinvariant : ∀ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ E.algebra →
      T * (rescaledGraphAction J hJ u 1 : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
        (rescaledGraphAction J hJ u 1 : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) * T)
    {I : Type*} (ω : I → SignedPermutation (Fin d)) (i : I) :
    ‖T (rescaledGraphVector J Ω c (matrixGraphRow E z ω i))‖ =
      ‖T (rescaledGraphVector J Ω c z)‖ := by
  let u := matrixUnitSignedRepresentation E (ω i)
  have hu : (u : H →L[ℂ] H) ∈ E.algebra := matrixUnitSignedRepresentation_mem E _
  have hus := E.algebra.star_mem' hu
  have hf := norm_graphSignal_unitaryDoubleOrbit M J hJ Ω c T u 1
    (by simpa only [OneMemClass.coe_one, star_one] using hcomm 1 E.algebra.one_mem)
    (by simpa only [star_star] using hcomm _ hus)
    (by simpa only [OneMemClass.coe_one, star_one] using hvector 1 E.algebra.one_mem)
    (by simpa only [star_star] using hvector _ hus)
    (by simpa only [star_one] using hinvariant u hu) z hz
  simpa only [unitaryDoubleOrbit, OneMemClass.coe_one, star_one, mul_one, matrixGraphRow, u] using hf

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphScaleRows
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.graphCoordinateScale_one _root_.OAI.KadisonKastler.graphCoordinateScale_zero _root_.OAI.KadisonKastler.graphIsometry_one _root_.OAI.KadisonKastler.graphIsometry_zero _root_.OAI.KadisonKastler.graphReciprocalFlip_norm _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.tomitaGraphFirst_adjoint_apply _root_.OAI.KadisonKastler.tomitaGraphFirst_apply _root_.OAI.KadisonKastler.tomitaGraphFlip_one _root_.OAI.KadisonKastler.tomitaGraphFlip_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform row flattening at arbitrary large rescalings

Rounding the squared rescaling up changes the moment normalization by at
most a factor two. The same fixed row cutoff remains sufficient.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The retained signal estimate at every graph scale up to sqrt(k). -/
theorem clippedGraphRow_signal_le_scale {k : ℕ} (hk : 0 < k)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) {c : ℝ} (hc : c ^ 2 ≤ (k : ℝ))
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (Y : Fin k → H →L[ℂ] H) (hcost : graphRowCost Ω Y ≤ 16777216)
    (hsignal : ‖T‖ / 8 ≤ finiteRMS (fun i => T (rescaledGraphVector J Ω c (Y i)))) :
    ‖T‖ / 16 ≤ finiteRMS (fun i =>
      T (rescaledGraphVector J Ω c (clippedGraphRow 131072 Y i))) := by
  let v := fun i => T (rescaledGraphVector J Ω c (clippedGraphRow 131072 Y i))
  let w := fun i => T (rescaledGraphVector J Ω c (Y i - clippedGraphRow 131072 Y i))
  have he : (fun i => T (rescaledGraphVector J Ω c (Y i))) = (fun i => v i + w i) := by
    funext i
    have h := (rescaledGraphOperatorMap J Ω c).map_sub (Y i) (clippedGraphRow 131072 Y i)
    change rescaledGraphVector J Ω c (Y i - clippedGraphRow 131072 Y i) =
      rescaledGraphVector J Ω c (Y i) - rescaledGraphVector J Ω c (clippedGraphRow 131072 Y i) at h
    dsimp [v, w]
    rw [h, map_sub]
    abel
  have hw : finiteRMS w ≤ ‖T‖ * (1 / 32) :=
    (finiteRMS_apply_le T _).trans (mul_le_mul_of_nonneg_left
      (clippedGraphRow_error_le_scale hk J Ω hc Y hcost) (norm_nonneg T))
  rw [he] at hsignal
  have ht := finiteRMS_add_le v w
  change ‖T‖ / 16 ≤ finiteRMS v
  nlinarith [norm_nonneg T]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GraphScaleDirection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.PointedMatrixSites.wordOperator_cons _root_.OAI.KadisonKastler.PointedMatrixSites.wordVector_cons _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.centralVectorDefect_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.conjugateMatrixUnits_entry _root_.OAI.KadisonKastler.conjugateOperatorMap_apply _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.graphCoordinateScale_one _root_.OAI.KadisonKastler.graphCoordinateScale_zero _root_.OAI.KadisonKastler.graphIsometry_one _root_.OAI.KadisonKastler.graphIsometry_zero _root_.OAI.KadisonKastler.graphReciprocalFlip_norm _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rightVectorLinear_apply _root_.OAI.KadisonKastler.spatialMatrixAmplification_apply _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaGraphFirst_adjoint_apply _root_.OAI.KadisonKastler.tomitaGraphFirst_apply _root_.OAI.KadisonKastler.tomitaGraphFlip_one _root_.OAI.KadisonKastler.tomitaGraphFlip_zero _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Directional graph bounds at all scales at least one

The integer row length is the ceiling of the squared scale. Both its
moment cost and its graph metric remain uniformly controlled.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem exists_bounded_graphRow_signal_scale_oai
    (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ A ∈ M, (∀ n a, a ∈ (E n).algebra → a * A = A * a) →
      ∃ z : ℂ, A = z • (1 : H →L[ℂ] H))
    (hcentral : ∀ n a, a ∈ (E n).algebra → ∀ z ∈ M,
      inner ℂ Ω ((a * z) Ω) = inner ℂ Ω ((z * a) Ω))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {c : ℝ} (hc : 1 ≤ c) {k : ℕ} (hk : 0 < k)
    (hck : c ^ 2 ≤ (k : ℝ)) (hkc : (k : ℝ) ≤ 2 * c ^ 2)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) (hT : T ≠ 0)
    (hsupport : T * rescaledGraphProjection M J Ω (c) = T)
    (hcomm : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) ∈ M.commutant)
    (hvector : ∀ j a, a ∈ (E j).algebra → conjugationOperator J (star a) Ω = a Ω)
    (hinvariant : ∀ j (u v : unitary (H →L[ℂ] H)),
      (u : H →L[ℂ] H) ∈ (E j).algebra → (v : H →L[ℂ] H) ∈ (E j).algebra →
      T * (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
        (rescaledGraphAction J hJ u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) * T) :
    ∃ X : Fin k → H →L[ℂ] H, (∀ i, X i ∈ M) ∧ ‖operatorRow X‖ ≤ 131072 ∧
      ‖T‖ / 16 ≤ finiteRMS (fun i =>
        T (rescaledGraphVector J Ω (c) (X i))) := by
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hc2 : 1 ≤ c ^ 2 := by nlinarith
  have hs : T * rescaledGraphProjection M J Ω (Real.sqrt (c ^ 2)) = T := by
    simpa only [Real.sqrt_sq hc0] using hsupport
  obtain ⟨z, hznorm, hzgraph, hzsignal⟩ := exists_bounded_rescaledGraph_signal M Ω hΩ
    d E hmono hEM hirr hcentral J hJ hc2 T hT hs hcomm hvector
      (by simpa only [Real.sqrt_sq hc0] using hinvariant)
  simp only [Real.sqrt_sq hc0] at hzgraph hzsignal
  have hzsize : ‖z.val Ω‖ ^ 2 + k * ‖star z.val Ω‖ ^ 2 ≤ 480 := by
    rw [norm_rescaledGraphVector_sq] at hzgraph
    have hm := mul_le_mul_of_nonneg_right hkc (sq_nonneg ‖star z.val Ω‖)
    nlinarith [sq_nonneg ‖z.val Ω‖]
  obtain ⟨j, ω, hcost⟩ := exists_matrixGraphRow_cost_le_480 M Ω hΩ d E hmono hEM
    hirr hcentral hk z.val z.property hznorm hzsize
  let Y : Fin k → H →L[ℂ] H := matrixGraphRow (E j) z.val ω
  have hY : ∀ i, Y i ∈ M := fun i =>
    M.mul_mem (hEM j (matrixUnitSignedRepresentation_mem (E j) (ω i))) z.property
  have hnorm (i : Fin k) :
      ‖T (rescaledGraphVector J Ω (c) (Y i))‖ =
        ‖T (rescaledGraphVector J Ω (c) z.val)‖ :=
    matrixGraphRow_signal_eq M J hJ Ω _ T (E j) z.val z.property (hcomm j) (hvector j)
      (fun u hu => hinvariant j u 1 hu (E j).algebra.one_mem) ω i
  have hsig : ‖T‖ / 8 ≤ finiteRMS (fun i =>
      T (rescaledGraphVector J Ω (c) (Y i))) := by
    rw [finiteRMS_eq_of_norm_eq _ (norm_nonneg _) hnorm]
    exact hzsignal
  refine ⟨clippedGraphRow 131072 Y, clippedGraphRow_mem M _ Y hY,
    norm_clippedGraphRow_le (by norm_num) Y, ?_⟩
  exact clippedGraphRow_signal_le_scale hk J Ω hck T Y hcost hsig


end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_bounded_graphRow_signal_scale_oai.{u_1} := @OAI.KadisonKastler.exists_bounded_graphRow_signal_scale_oai.{u_1}
