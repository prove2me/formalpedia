-- Prove2me | solution 1 for OAI.KadisonKastler.publishedRealNestDistance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:10:13.583389+00:00
-- url     : https://prove2.me/submissions/b948294b-7c33-4fa2-8237-45a2cff70ac2

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Matrix.Composition
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Q260K012
import Definitions.Def_Q260K015

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertContractionFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Contractive factorization through a Hilbert-space operator

This is the range-extension step used for contractive block completions in
the finite-nest distance argument. The factor is constructed on the closed
range and extended by zero on its orthogonal complement.
-/

namespace KadisonKastler

noncomputable section

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace F] in
theorem operatorClosedRangeMap_dense (S : E →L[ℂ] F) :
    DenseRange (operatorClosedRangeMap S) := by
  apply Metric.denseRange_iff.mpr
  intro z ε hε
  obtain ⟨x, hx⟩ := Metric.mem_closure_range_iff.mp z.property ε hε
  exact ⟨x, hx⟩

/-- Norm domination gives a contractive factor on the entire middle Hilbert
space, including when the original operator has nonclosed range. -/
theorem exists_contraction_factor (S : E →L[ℂ] F) (T : E →L[ℂ] G)
    (h : ∀ x, ‖T x‖ ≤ ‖S x‖) :
    ∃ C : F →L[ℂ] G, ‖C‖ ≤ 1 ∧ C.comp S = T := by
  let W := S.toLinearMap.range.topologicalClosure
  let s := operatorClosedRangeMap S
  let c : W →L[ℂ] G := T.toLinearMap.extendOfNorm s.toLinearMap
  have hs : DenseRange s := operatorClosedRangeMap_dense S
  have hn : ∀ x, ‖T.toLinearMap x‖ ≤ (1 : ℝ) * ‖s.toLinearMap x‖ := by
    intro x
    change ‖T x‖ ≤ 1 * ‖S x‖
    simpa only [one_mul] using h x
  have hc : ‖c‖ ≤ 1 := LinearMap.opNorm_extendOfNorm_le hs zero_le_one hn
  refine ⟨c.comp W.orthogonalProjectionOnto, ?_, ?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hc W.orthogonalProjectionOnto_norm_le (norm_nonneg W.orthogonalProjectionOnto)
        zero_le_one).trans_eq (mul_one 1))
  · apply ContinuousLinearMap.ext
    intro x
    change c (W.orthogonalProjectionOnto (S x)) = T x
    have hp : W.orthogonalProjectionOnto (S x) = s x :=
      W.orthogonalProjectionOnto_mem_subspace_eq_self (s x)
    rw [hp]
    exact LinearMap.extendOfNorm_eq hs ⟨1, hn⟩ x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IsometryComplement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Complementary projection of an isometric embedding

The formulas below retain the concrete adjoint of the embedding, as needed
for a contractive lift with prescribed first coordinate.
-/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {E K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem adjoint_isometry_apply (V : E →ₗᵢ[ℂ] K) (x : E) :
    V.toContinuousLinearMap.adjoint (V x) = x := by
  exact congrArg (fun T : E →L[ℂ] E => T x) V.adjoint_comp_self

theorem isometryComplement_adjoint (V : E →ₗᵢ[ℂ] K) :
    (isometryComplement V).adjoint = isometryComplement V := by
  simp [isometryComplement, ContinuousLinearMap.adjoint_one]

theorem adjoint_isometry_complement (V : E →ₗᵢ[ℂ] K) (z : K) :
    V.toContinuousLinearMap.adjoint (isometryComplement V z) = 0 := by
  simp only [isometryComplement, sub_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply, map_sub]
  change V.toContinuousLinearMap.adjoint z -
    V.toContinuousLinearMap.adjoint (V (V.toContinuousLinearMap.adjoint z)) = 0
  rw [adjoint_isometry_apply, sub_self]

theorem norm_isometryComplement_sq (V : E →ₗᵢ[ℂ] K) (z : K) :
    ‖isometryComplement V z‖ ^ 2 = ‖z‖ ^ 2 - ‖V.toContinuousLinearMap.adjoint z‖ ^ 2 := by
  change ‖z - V (V.toContinuousLinearMap.adjoint z)‖ ^ 2 = _
  rw [norm_sub_sq (𝕜 := ℂ)]
  have hi : inner ℂ z (V (V.toContinuousLinearMap.adjoint z)) =
      inner ℂ (V.toContinuousLinearMap.adjoint z) (V.toContinuousLinearMap.adjoint z) :=
    (V.toContinuousLinearMap.adjoint_inner_left _ _).symm
  rw [hi, inner_self_eq_norm_sq, V.norm_map]
  ring

theorem isometryComplement_norm_le (V : E →ₗᵢ[ℂ] K) :
    ‖isometryComplement V‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_isometryComplement_sq]
  exact sub_le_self _ (sq_nonneg _)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ComplementaryContractionLift
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A contractive lift perpendicular to a prescribed isometry

This is the geometric completion step: the unused norm in one coordinate
supports a new column perpendicular to the already prescribed column.
-/

namespace KadisonKastler

noncomputable section

variable {E F G K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem exists_complementary_contraction_lift
    (V : E →ₗᵢ[ℂ] K) (J : F →ₗᵢ[ℂ] K) (B : G →L[ℂ] F)
    (h : ∀ y, ‖V.toContinuousLinearMap.adjoint (J y)‖ ^ 2 +
      ‖B.adjoint y‖ ^ 2 ≤ ‖y‖ ^ 2) :
    ∃ Y : G →L[ℂ] K, ‖Y‖ ≤ 1 ∧
      J.toContinuousLinearMap.adjoint.comp Y = B ∧
      V.toContinuousLinearMap.adjoint.comp Y = 0 := by
  let Q := isometryComplement V
  let W := Q.comp J.toContinuousLinearMap
  have hW (y : F) : ‖W y‖ ^ 2 =
      ‖y‖ ^ 2 - ‖V.toContinuousLinearMap.adjoint (J y)‖ ^ 2 := by
    change ‖isometryComplement V (J y)‖ ^ 2 = _
    rw [norm_isometryComplement_sq, J.norm_map]
  have hdom (y : F) : ‖B.adjoint y‖ ≤ ‖W y‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hW]
    linarith [h y]
  obtain ⟨L, hL, hLW⟩ := exists_contraction_factor W B.adjoint hdom
  let Y := Q.comp L.adjoint
  refine ⟨Y, ?_, ?_, ?_⟩
  · have hLa : ‖L.adjoint‖ ≤ 1 := by
      simpa only [ContinuousLinearMap.adjoint.norm_map] using hL
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (isometryComplement_norm_le V) hLa (norm_nonneg L.adjoint) zero_le_one).trans_eq
        (mul_one 1))
  · have hadj := congrArg ContinuousLinearMap.adjoint hLW
    simpa only [W, ContinuousLinearMap.adjoint_comp, Q, isometryComplement_adjoint,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc] using hadj
  · apply ContinuousLinearMap.ext
    intro z
    exact adjoint_isometry_complement V (L.adjoint z)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertBlockCompletion
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Contractive completion of a Hilbert-space operator block

A contractive row and a contractive column with the same corner have a
common contractive completion. The construction uses the defect isometry
and the complementary lift, and is the finite completion step for nests.
-/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem firstCoordinateIsometry_adjoint (z : WithLp 2 (F × E)) :
    (firstCoordinateIsometry (E := E) (F := F)).toContinuousLinearMap.adjoint z = z.fst := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [firstCoordinateIsometry, WithLp.prod_inner_apply]

theorem exists_contractive_block_completion
    (A : E →L[ℂ] F) (B : G →L[ℂ] F) (C : E →L[ℂ] H)
    (hrow : ∀ y, ‖A.adjoint y‖ ^ 2 + ‖B.adjoint y‖ ^ 2 ≤ ‖y‖ ^ 2)
    (hcol : ∀ x, ‖A x‖ ^ 2 + ‖C x‖ ^ 2 ≤ ‖x‖ ^ 2) :
    ∃ D : G →L[ℂ] H, ∀ x z,
      ‖A x + B z‖ ^ 2 + ‖C x + D z‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖z‖ ^ 2 := by
  have hA : ‖A‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [one_mul]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith [hcol x, sq_nonneg ‖C x‖]
  let V := defectIsometry A hA
  let J : F →ₗᵢ[ℂ] WithLp 2 (F × E) := firstCoordinateIsometry
  have hJV : J.toContinuousLinearMap.adjoint.comp V.toContinuousLinearMap = A := by
    ext x
    rw [ContinuousLinearMap.comp_apply, firstCoordinateIsometry_adjoint]
    rfl
  have hVJ (y : F) : V.toContinuousLinearMap.adjoint (J y) = A.adjoint y := by
    have h := congrArg ContinuousLinearMap.adjoint hJV
    have hp := congrArg (fun T : F →L[ℂ] E => T y) h
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap] using hp
  obtain ⟨Y, hY, hJY, hVY⟩ := exists_complementary_contraction_lift V J B (by
    intro y
    rw [hVJ]
    exact hrow y)
  have hCD (x : E) : ‖C x‖ ≤ ‖operatorDefect A x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_operatorDefect_sq A hA]
    linarith [hcol x]
  obtain ⟨R, hR, hRD⟩ := exists_contraction_factor (operatorDefect A) C hCD
  let D := R.comp ((WithLp.sndL 2 ℂ F E).comp Y)
  refine ⟨D, ?_⟩
  intro x z
  let w := V x + Y z
  have hw₁ : w.fst = A x + B z := by
    have h := congrArg (fun T : G →L[ℂ] F => T z) hJY
    rw [ContinuousLinearMap.comp_apply, firstCoordinateIsometry_adjoint] at h
    change A x + (Y z).fst = A x + B z
    rw [h]
  have hw₂ : R w.snd = C x + D z := by
    have h := congrArg (fun T : E →L[ℂ] H => T x) hRD
    change R (operatorDefect A x) = C x at h
    change R (operatorDefect A x + (Y z).snd) = C x + R (Y z).snd
    rw [map_add, h]
  have horth : inner ℂ (V x) (Y z) = 0 := by
    change inner ℂ (V.toContinuousLinearMap x) (Y z) = 0
    rw [← V.toContinuousLinearMap.adjoint_inner_right]
    have h := congrArg (fun T : G →L[ℂ] E => T z) hVY
    change V.toContinuousLinearMap.adjoint (Y z) = 0 at h
    rw [h, inner_zero_right]
  have hnY : ‖Y z‖ ≤ ‖z‖ := by
    simpa only [one_mul] using Y.le_of_opNorm_le hY z
  have hnR : ‖R w.snd‖ ≤ ‖w.snd‖ := by
    simpa only [one_mul] using R.le_of_opNorm_le hR w.snd
  calc
    _ = ‖w.fst‖ ^ 2 + ‖R w.snd‖ ^ 2 := by rw [hw₁, hw₂]
    _ ≤ ‖w.fst‖ ^ 2 + ‖w.snd‖ ^ 2 := by gcongr
    _ = ‖w‖ ^ 2 := (WithLp.prod_norm_sq_eq_of_L2 w).symm
    _ = ‖x‖ ^ 2 + ‖Y z‖ ^ 2 := by
      change ‖V x + Y z‖ ^ 2 = _
      rw [norm_add_sq (𝕜 := ℂ), horth, V.norm_map]
      simp
    _ ≤ ‖x‖ ^ 2 + ‖z‖ ^ 2 := by gcongr

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionNormDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Squared-norm decompositions for nested projections -/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem projection_apply_norm_le {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    ‖P x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using P.le_of_opNorm_le (hP.norm_le P) x

theorem projection_complement_inner {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    inner ℂ (P x) ((1 - P) x) = 0 := by
  have hs : P.adjoint = P := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hP.isSelfAdjoint.star_eq
  have hz : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hP.isIdempotentElem.eq, sub_self]
  rw [← P.adjoint_inner_right, hs]
  change inner ℂ x ((P * (1 - P)) x) = 0
  rw [hz, zero_apply, inner_zero_right]

theorem projection_norm_sq_decomposition {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (x : H) :
    ‖P x‖ ^ 2 + ‖(1 - P) x‖ ^ 2 = ‖x‖ ^ 2 := by
  calc
    _ = ‖P x + (1 - P) x‖ ^ 2 := by
      simpa only [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
          (projection_complement_inner hP x)).symm
    _ = ‖x‖ ^ 2 := by simp

theorem nested_projection_reverse {P R : H →L[ℂ] H}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (hPR : P * R = P) :
    R * P = P := by
  have h := congrArg star hPR
  simpa only [star_mul, hP.isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq] using h

theorem nested_projection_norm_sq_eq {P R : H →L[ℂ] H}
    (hP : IsStarProjection P) (hPR : P * R = P) (x : H) :
    ‖P x‖ ^ 2 + ‖(R - P) x‖ ^ 2 = ‖R x‖ ^ 2 := by
  have hs : P.adjoint = P := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hP.isSelfAdjoint.star_eq
  have hz : P * (R - P) = 0 := by
    rw [mul_sub, hPR, hP.isIdempotentElem.eq, sub_self]
  have hi : inner ℂ (P x) ((R - P) x) = 0 := by
    rw [← P.adjoint_inner_right, hs]
    change inner ℂ x ((P * (R - P)) x) = 0
    rw [hz, zero_apply, inner_zero_right]
  calc
    _ = ‖P x + (R - P) x‖ ^ 2 := by
      simpa only [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi).symm
    _ = ‖R x‖ ^ 2 := by simp

theorem nested_projection_norm_sq {P R : H →L[ℂ] H}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (hPR : P * R = P) (x : H) :
    ‖P x‖ ^ 2 + ‖(R - P) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [nested_projection_norm_sq_eq hP hPR]
  calc
    _ ≤ ‖x‖ ^ 2 := by gcongr; exact projection_apply_norm_le hR x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NestCornerExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Extending a contractive corner across one nest projection -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem extend_contractive_nest_corner
    (P R Q T X : H →L[ℂ] H)
    (hP : IsStarProjection P) (hR : IsStarProjection R) (hQ : IsStarProjection Q)
    (hPR : P * R = P) (hX : ‖X‖ ≤ 1) (hXP : X * P = X)
    (hmatch : Q * X = Q * T * P) (hTR : ‖Q * T * R‖ ≤ 1) :
    ∃ Y : H →L[ℂ] H, ‖Y‖ ≤ 1 ∧ Y * P = X ∧ Y * R = Y ∧ Q * Y = Q * T * R := by
  let E := R - P
  let A := Q * X
  let B := Q * T * E
  let C := (1 - Q) * X
  have hRP := nested_projection_reverse hP hR hPR
  have hEP : E * P = 0 := by
    simp only [E, sub_mul, hRP, hP.isIdempotentElem.eq, sub_self]
  have hER : E * R = E := by
    simp only [E, sub_mul, hR.isIdempotentElem.eq, hPR]
  have hEE : E * E = E := by
    change E * (R - P) = E
    rw [mul_sub, hER, hEP, sub_zero]
  have hXR : X * R = X := by
    rw [← hXP, mul_assoc, hPR, hXP]
  have hAdjA : A.adjoint = P * star T * Q := by
    change star (Q * X) = _
    rw [hmatch, star_mul, star_mul, hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq]
    simp only [mul_assoc]
  have hAdjB : B.adjoint = E * star T * Q := by
    change star (Q * T * E) = _
    simp only [E, star_mul, star_sub, hP.isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq,
      hQ.isSelfAdjoint.star_eq, mul_assoc]
  have hrow : ∀ y, ‖A.adjoint y‖ ^ 2 + ‖B.adjoint y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    intro y
    rw [hAdjA, hAdjB]
    change ‖P ((star T * Q) y)‖ ^ 2 + ‖(R - P) ((star T * Q) y)‖ ^ 2 ≤ _
    rw [nested_projection_norm_sq_eq hP hPR]
    have hn : ‖R * star T * Q‖ ≤ 1 := by
      have hs : star (Q * T * R) = R * star T * Q := by
        simp only [star_mul, hQ.isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq, mul_assoc]
      rw [← hs, norm_star]
      exact hTR
    have hb : ‖R ((star T * Q) y)‖ ≤ ‖y‖ := by
      simpa only [one_mul, mul_apply_eq_comp] using (R * star T * Q).le_of_opNorm_le hn y
    gcongr
  have hcol : ∀ x, ‖A x‖ ^ 2 + ‖C x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    intro x
    change ‖Q (X x)‖ ^ 2 + ‖(1 - Q) (X x)‖ ^ 2 ≤ _
    rw [projection_norm_sq_decomposition hQ]
    have hn : ‖X x‖ ≤ ‖x‖ := by simpa only [one_mul] using X.le_of_opNorm_le hX x
    gcongr
  obtain ⟨D, hD⟩ := exists_contractive_block_completion A B C hrow hcol
  let Y := X + B + (1 - Q) * D * E
  have hYP : Y * P = X := by
    simp only [Y, B, add_mul, mul_assoc, hXP, hEP, mul_zero, add_zero]
  have hYR : Y * R = Y := by
    simp only [Y, B, add_mul, mul_assoc, hXR, hER]
  have hQY : Q * Y = Q * T * R := by
    have hz : Q * (1 - Q) = 0 := by
      rw [mul_sub, mul_one, hQ.isIdempotentElem.eq, sub_self]
    simp only [Y, B, mul_add, ← mul_assoc, hQ.isIdempotentElem.eq, hz, zero_mul, add_zero]
    rw [hmatch]
    dsimp only [E]
    noncomm_ring
  refine ⟨Y, ?_, hYP, hYR, hQY⟩
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hAx : A (P x) = A x := by
    change (Q * X * P) x = (Q * X) x
    rw [mul_assoc, hXP]
  have hBx : B (E x) = B x := by
    change (Q * T * E * E) x = (Q * T * E) x
    rw [mul_assoc, hEE]
  have hCx : C (P x) = C x := by
    change ((1 - Q) * X * P) x = ((1 - Q) * X) x
    rw [mul_assoc, hXP]
  have hb := hD (P x) (E x)
  rw [hAx, hBx, hCx] at hb
  have hfirst : Q (Y x) = A x + B x := by
    have hqb : Q * B = B := by
      simp only [B, ← mul_assoc, hQ.isIdempotentElem.eq]
    have hz : Q * (1 - Q) = 0 := by
      rw [mul_sub, mul_one, hQ.isIdempotentElem.eq, sub_self]
    change (Q * Y) x = _
    simp only [Y, mul_add, ← mul_assoc, hz, zero_mul, add_zero, hqb, add_apply]
    rfl
  have hsecond : (1 - Q) (Y x) = (1 - Q) (C x + D (E x)) := by
    have hqb : (1 - Q) * B = 0 := by
      simp only [B, ← mul_assoc, sub_mul, one_mul, hQ.isIdempotentElem.eq, sub_self, zero_mul]
    change ((1 - Q) * Y) x = _
    simp only [Y, mul_add, ← mul_assoc, hqb, add_zero,
      hQ.one_sub.isIdempotentElem.eq, add_apply]
    have hc : (1 - Q) * C = C := by
      simp only [C, ← mul_assoc, hQ.one_sub.isIdempotentElem.eq]
    simp only [map_add]
    change C x + (1 - Q) (D (E x)) = ((1 - Q) * C) x + (1 - Q) (D (E x))
    rw [hc]
  calc
    ‖Y x‖ ^ 2 = ‖Q (Y x)‖ ^ 2 + ‖(1 - Q) (Y x)‖ ^ 2 :=
      (projection_norm_sq_decomposition hQ (Y x)).symm
    _ ≤ ‖A x + B x‖ ^ 2 + ‖C x + D (E x)‖ ^ 2 := by
      rw [hfirst, hsecond]
      gcongr
      exact projection_apply_norm_le hQ.one_sub _
    _ ≤ ‖P x‖ ^ 2 + ‖E x‖ ^ 2 := hb
    _ ≤ ‖x‖ ^ 2 := nested_projection_norm_sq hP hR hPR x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteNestCompletion
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Contractive completion for a finite chain of projections -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem extend_finite_projection_chain (T : H →L[ℂ] H)
    (L : List (H →L[ℂ] H))
    (hchain : L.Pairwise (fun P R => P * R = P))
    (hdata : ∀ R ∈ L, IsStarProjection R ∧ ‖(1 - R) * T * R‖ ≤ 1)
    (P X : H →L[ℂ] H) (hP : IsStarProjection P)
    (hbase : ∀ R ∈ L, P * R = P)
    (hX : ‖X‖ ≤ 1) (hXP : X * P = X)
    (hmatch : (1 - P) * X = (1 - P) * T * P) :
    ∃ Y : H →L[ℂ] H, ‖Y‖ ≤ 1 ∧ Y * P = X ∧
      ∀ R ∈ L, (1 - R) * Y * R = (1 - R) * T * R := by
  induction L generalizing P X with
  | nil => exact ⟨X, hX, hXP, by simp⟩
  | cons R L ih =>
    obtain ⟨hRL, hchainL⟩ := List.pairwise_cons.mp hchain
    obtain ⟨hR, hTR⟩ := hdata R (by simp)
    have hPR : P * R = P := hbase R (by simp)
    have hRP := nested_projection_reverse hP hR hPR
    have hQP : (1 - R) * P = 0 := by rw [sub_mul, one_mul, hRP, sub_self]
    have hQQ : (1 - R) * (1 - P) = 1 - R := by
      rw [mul_sub, mul_one, hQP, sub_zero]
    have hnext : (1 - R) * X = (1 - R) * T * P := by
      calc
        _ = (1 - R) * ((1 - P) * X) := by rw [← mul_assoc, hQQ]
        _ = (1 - R) * ((1 - P) * T * P) := by rw [hmatch]
        _ = _ := by rw [← mul_assoc, ← mul_assoc, hQQ]
    obtain ⟨Z, hZ, hZP, hZR, hQZ⟩ :=
      extend_contractive_nest_corner P R (1 - R) T X hP hR hR.one_sub hPR hX hXP hnext hTR
    obtain ⟨Y, hY, hYR, hrest⟩ := ih hchainL
      (fun S hS => hdata S (by simp [hS])) R Z hR hRL hZ hZR hQZ
    refine ⟨Y, hY, ?_, ?_⟩
    · calc
        Y * P = Y * (R * P) := by rw [hRP]
        _ = Z * P := by rw [← mul_assoc, hYR]
        _ = X := hZP
    · intro S hS
      rcases List.mem_cons.mp hS with rfl | hS
      · rw [mul_assoc, hYR, hQZ]
      · exact hrest S hS

theorem finite_projection_chain_completion (T : H →L[ℂ] H)
    (L : List (H →L[ℂ] H))
    (hchain : L.Pairwise (fun P R => P * R = P))
    (hdata : ∀ R ∈ L, IsStarProjection R ∧ ‖(1 - R) * T * R‖ ≤ 1) :
    ∃ X : H →L[ℂ] H, ‖X‖ ≤ 1 ∧
      ∀ R ∈ L, (1 - R) * X * R = (1 - R) * T * R := by
  obtain ⟨X, hX, _, hfix⟩ := extend_finite_projection_chain T L hchain hdata 0 0
    (IsStarProjection.zero (H →L[ℂ] H)) (by simp) (by simp) (by simp) (by simp)
  exact ⟨X, hX, hfix⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RealNestCompletion
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Simultaneous contractive completion along a real-indexed nest

Finite chains are completed explicitly. A bounded weak operator limit over
finite subsets imposes all the prescribed lower corners at once.
-/

namespace KadisonKastler

open Filter Generator.Tracial
open scoped Topology InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_real_nest_completion
    (P : ℝ → H →L[ℂ] H) (hP : ∀ a, IsStarProjection (P a))
    (hmono : ∀ a b, a ≤ b → P a * P b = P a)
    (T : H →L[ℂ] H) (hT : ∀ a, ‖(1 - P a) * T * P a‖ ≤ 1)
    (s : Finset ℝ) :
    ∃ X : H →L[ℂ] H, ‖X‖ ≤ 1 ∧
      ∀ a ∈ s, (1 - P a) * X * P a = (1 - P a) * T * P a := by
  classical
  let L := (s.sort (· ≤ ·)).map P
  have hchain : L.Pairwise (fun Q R => Q * R = Q) :=
    List.pairwise_map.mpr ((s.pairwise_sort (· ≤ ·)).imp (fun hab => hmono _ _ hab))
  have hdata : ∀ R ∈ L, IsStarProjection R ∧ ‖(1 - R) * T * R‖ ≤ 1 := by
    rintro R hR
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hR
    exact ⟨hP a, hT a⟩
  obtain ⟨X, hX, hfix⟩ := finite_projection_chain_completion T L hchain hdata
  refine ⟨X, hX, ?_⟩
  intro a ha
  exact hfix (P a) (List.mem_map.mpr ⟨a, (s.mem_sort (· ≤ ·)).mpr ha, rfl⟩)

theorem real_nest_contractive_completion
    (P : ℝ → H →L[ℂ] H) (hP : ∀ a, IsStarProjection (P a))
    (hmono : ∀ a b, a ≤ b → P a * P b = P a)
    (T : H →L[ℂ] H) (hT : ∀ a, ‖(1 - P a) * T * P a‖ ≤ 1) :
    ∃ X : H →L[ℂ] H, ‖X‖ ≤ 1 ∧
      ∀ a, (1 - P a) * X * P a = (1 - P a) * T * P a := by
  classical
  choose X hX hfix using finite_real_nest_completion P hP hmono T hT
  let ω := Ultrafilter.of (atTop : Filter (Finset ℝ))
  obtain ⟨Y, hY, ht⟩ := exists_weak_operator_ultralimit ω X 1 zero_le_one hX
  refine ⟨Y, hY, ?_⟩
  intro a
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  let Q := 1 - P a
  change inner ℂ y (Q (Y (P a x))) = inner ℂ y (Q (T (P a x)))
  rw [← Q.adjoint_inner_left, ← Q.adjoint_inner_left]
  have he : ∀ᶠ s : Finset ℝ in (ω : Filter (Finset ℝ)),
      (1 - P a) * X s * P a = (1 - P a) * T * P a := by
    apply (show (ω : Filter (Finset ℝ)) ≤ atTop from Ultrafilter.of_le atTop)
    exact Filter.eventually_atTop.mpr ⟨{a}, fun s hs => hfix s a (hs (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))⟩
  have heq : ∀ᶠ s : Finset ℝ in (ω : Filter (Finset ℝ)),
      inner ℂ (Q.adjoint y) (X s (P a x)) = inner ℂ (Q.adjoint y) (T (P a x)) := by
    filter_upwards [he] with s hs
    rw [Q.adjoint_inner_left, Q.adjoint_inner_left]
    exact congrArg (fun S : H →L[ℂ] H => inner ℂ y (S x)) hs
  exact tendsto_nhds_unique (ht (P a x) (Q.adjoint y))
    (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RealNestDistanceConstruction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The required real-nest distance theorem

Arveson's distance formula is proved here in the precise approximation
form used by the application. Finite contractive block completions and
weak operator compactness supply a correction with norm at most the nest
defect. No nest-distance theorem is assumed.
-/

namespace KadisonKastler

noncomputable section

universe u

theorem publishedRealNestDistance_oai : PublishedRealNestDistance.{u} := by
  intro H _ _ _ P hP hmono T δ η hδ hη hdefect
  by_cases hzero : δ = 0
  · subst δ
    refine ⟨T, ?_, ?_⟩
    · intro a
      exact norm_eq_zero.mp (le_antisymm (hdefect a) (norm_nonneg _))
    · simpa using hη
  have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hzero)
  let U : H →L[ℂ] H := (δ⁻¹ : ℝ) • T
  have hU : ∀ a, ‖(1 - P a) * U * P a‖ ≤ 1 := by
    intro a
    calc
      _ = δ⁻¹ * ‖(1 - P a) * T * P a‖ := by
        simp only [U, mul_smul_comm, smul_mul_assoc, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hδpos)]
      _ ≤ δ⁻¹ * δ := mul_le_mul_of_nonneg_left (hdefect a) (inv_nonneg.mpr hδ)
      _ = 1 := inv_mul_cancel₀ hzero
  obtain ⟨X, hX, hfix⟩ := real_nest_contractive_completion P hP hmono U hU
  have hc (a : ℝ) : (1 - P a) * ((δ : ℝ) • X) * P a = (1 - P a) * T * P a := by
    simp only [mul_smul_comm, smul_mul_assoc]
    rw [hfix a]
    simp only [U, mul_smul_comm, smul_mul_assoc, smul_smul, mul_inv_cancel₀ hzero, one_smul]
  let S := T - (δ : ℝ) • X
  refine ⟨S, ?_, ?_⟩
  · intro a
    change (1 - P a) * (T - (δ : ℝ) • X) * P a = 0
    rw [mul_sub, sub_mul, hc, sub_self]
  · have he : S - T = -((δ : ℝ) • X) := by dsimp only [S]; abel
    calc
      ‖S - T‖ = δ * ‖X‖ := by
        rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
      _ ≤ δ := by nlinarith
      _ < δ + η := lt_add_of_pos_right δ hη

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.publishedRealNestDistance_oai.{u} := @OAI.KadisonKastler.publishedRealNestDistance_oai.{u}
