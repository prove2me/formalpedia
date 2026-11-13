-- Prove2me | solution 1 for OAI.KadisonKastler.completelyBoundedBy_offDiagonal_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:04:30.802462+00:00
-- url     : https://prove2.me/submissions/1280e483-c79c-4f6e-a00f-9059053ed5d5

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Definitions.Def_Q260K015

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCorrection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Rectangular matrix estimates for multiplication correction

The inverse and corrected-map bounds used in the UCP criterion hold at
every rectangular C⋆-matrix size. The source and target may be represented
in a third ambient C⋆-algebra.
-/

namespace KadisonKastler

variable {A B C : Type*}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C] in
/-- Entrywise application respects composition on rectangular matrices. -/
theorem matrix_map_comp (F : A →ₗ[ℂ] B) (G : B →ₗ[ℂ] C) {p q : ℕ}
    (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (G.comp F) X = CStarMatrix.mapₗ G (CStarMatrix.mapₗ F X) := by
  ext i j
  rfl

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BlockAmplification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Complete bounds for the off-diagonal commutator construction

Reordering the two finite matrix indices turns an amplification of
`b ↦ [0,-b;b,0]` into the same off-diagonal matrix over a matrix algebra.
Its norm is therefore exactly the norm of the original amplification.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem norm_matrixBlockSwap (n : Type*) [Fintype n] [DecidableEq n]
    (X : CStarMatrix n n (CStarMatrix (Fin 2) (Fin 2) B)) :
    ‖matrixBlockSwap n X‖ = ‖X‖ :=
  NonUnitalStarAlgHom.norm_map (matrixBlockSwap n) (matrixBlockSwap n).injective X

theorem matrixBlockSwap_offDiagonal (n : Type*) [Fintype n] [DecidableEq n]
    (X : CStarMatrix n n B) :
    matrixBlockSwap n (CStarMatrix.mapₗ offDiagonalLinearMap X) =
      blockOffDiagonal (-X) X := by
  ext i j v w
  fin_cases i <;> fin_cases j <;> rfl

/-- The signed off-diagonal map preserves every square matrix norm. -/
theorem norm_map_offDiagonal_square {n : Type*} [Fintype n] [DecidableEq n]
    (X : CStarMatrix n n B) :
    ‖CStarMatrix.mapₗ offDiagonalLinearMap X‖ = ‖X‖ := by
  rw [← norm_matrixBlockSwap n, matrixBlockSwap_offDiagonal, norm_blockOffDiagonal]
  simp

/-- The same exact norm identity holds for rectangular amplifications. -/
theorem norm_map_offDiagonal {m n : Type*} [Fintype m] [Fintype n]
    (X : CStarMatrix m n B) :
    ‖CStarMatrix.mapₗ offDiagonalLinearMap X‖ = ‖X‖ := by
  classical
  calc
    _ = ‖rectangularCorner (CStarMatrix.mapₗ offDiagonalLinearMap X)‖ :=
      (norm_rectangularCorner _).symm
    _ = ‖CStarMatrix.mapₗ offDiagonalLinearMap (rectangularCorner X)‖ := by
      rw [rectangularCorner_map]
    _ = ‖rectangularCorner X‖ := norm_map_offDiagonal_square _
    _ = ‖X‖ := norm_rectangularCorner X

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The off-diagonal construction preserves exactly the complete bound. -/
theorem completelyBoundedBy_offDiagonal_iff_oai (F : A →ₗ[ℂ] B) (e : ℝ) :
    CompletelyBoundedBy (offDiagonalLinearMap.comp F) e ↔ CompletelyBoundedBy F e := by
  constructor <;> intro h p q X
  · have hX := h p q X
    rwa [matrix_map_comp, norm_map_offDiagonal] at hX
  · rw [matrix_map_comp, norm_map_offDiagonal]
    exact h p q X

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.completelyBoundedBy_offDiagonal_iff_oai.{u_1, u_2} := @OAI.KadisonKastler.completelyBoundedBy_offDiagonal_iff_oai.{u_1, u_2}
