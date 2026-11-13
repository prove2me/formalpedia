-- Prove2me | solution 1 for OAI.KadisonKastler.blockAlgebraDecomposition_coordinate_transport
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:06:40.990825+00:00
-- url     : https://prove2.me/submissions/0e0e9598-2c5d-4844-a33c-111ff0b8ef96

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
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
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K012
import Definitions.Def_Q260K015

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CanonicalAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial transport and the canonical infinite amplification

Transport into the initial coordinate preserves the unit balls and their
Hausdorff distance. The abstract diagonal action obtained from the matrix
units is exactly the coordinatewise action on the Hilbert direct sum.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem norm_spatialConjugate (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    ‖e.conjStarAlgEquiv T‖ = ‖T‖ :=
  NonUnitalStarAlgHom.norm_map e.conjStarAlgEquiv e.conjStarAlgEquiv.injective T

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BlockCoordinateTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Coordinate changes in a countable block decomposition -/

namespace KadisonKastler

noncomputable section

variable {E F : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, InnerProductSpace ℂ (F n)]
  (e : ∀ n, E n ≃ₗᵢ[ℂ] F n)

theorem hilbertSumCoordinateEquiv_symm_apply (f : lp F 2) (n : ℕ) :
    (hilbertSumCoordinateEquiv e).symm f n = (e n).symm (f n) := by
  apply (e n).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact congrArg (fun g : lp F 2 => g n) ((hilbertSumCoordinateEquiv e).apply_symm_apply f)

variable [∀ n, CompleteSpace (E n)] [∀ n, CompleteSpace (F n)]

theorem representsBlockOperators_coordinate_transport
    (R : ∀ n, E n →L[ℂ] E n) (T : lp E 2 →L[ℂ] lp E 2)
    (hT : RepresentsBlockOperators R T) :
    RepresentsBlockOperators (fun n => (e n).conjStarAlgEquiv (R n))
      ((hilbertSumCoordinateEquiv e).conjStarAlgEquiv T) := by
  intro f n
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    hilbertSumCoordinateEquiv_apply]
  rw [hT ((hilbertSumCoordinateEquiv e).symm f) n,
    hilbertSumCoordinateEquiv_symm_apply]

theorem blockAlgebraDecomposition_coordinate_transport_oai
    (M : ∀ n, VonNeumannAlgebra (E n)) (A : VonNeumannAlgebra (lp E 2))
    (hA : BlockAlgebraDecomposition M A) :
    BlockAlgebraDecomposition (fun n => spatialTransportAlgebra (e n) (M n))
      (spatialTransportAlgebra (hilbertSumCoordinateEquiv e) A) := by
  constructor
  · rintro _ ⟨T, hT, rfl⟩
    obtain ⟨R, hn, hR, ha⟩ := hA.decompose T hT
    refine ⟨fun n => (e n).conjStarAlgEquiv (R n), ?_, ?_,
      representsBlockOperators_coordinate_transport e R T ha⟩
    · intro n
      change ‖(e n).conjStarAlgEquiv (R n)‖ ≤
        ‖(hilbertSumCoordinateEquiv e).conjStarAlgEquiv T‖
      simpa only [norm_spatialConjugate] using hn n
    · intro n
      exact ⟨R n, hR n, rfl⟩
  · intro R C hC hn hR
    let S := fun n => (e n).conjStarAlgEquiv.symm (R n)
    have hSn (n : ℕ) : ‖S n‖ ≤ C := by
      simpa only [S, LinearIsometryEquiv.symm_conjStarAlgEquiv, norm_spatialConjugate] using hn n
    have hSM (n : ℕ) : S n ∈ M n :=
      (mem_spatialTransportAlgebra (e n) (M n) (R n)).mp (hR n)
    obtain ⟨T, hT, ha⟩ := hA.reconstruct S C hC hSn hSM
    refine ⟨(hilbertSumCoordinateEquiv e).conjStarAlgEquiv T, ⟨T, hT, rfl⟩, ?_⟩
    simpa only [S, StarAlgEquiv.apply_symm_apply] using
      representsBlockOperators_coordinate_transport e S T ha

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.blockAlgebraDecomposition_coordinate_transport_oai.{u_1, u_2} := @OAI.KadisonKastler.blockAlgebraDecomposition_coordinate_transport_oai.{u_1, u_2}
