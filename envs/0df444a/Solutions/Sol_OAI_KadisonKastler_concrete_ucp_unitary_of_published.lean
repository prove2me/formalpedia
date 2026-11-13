-- Prove2me | solution 1 for OAI.KadisonKastler.concrete_ucp_unitary_of_published
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:07:04.050599+00:00
-- url     : https://prove2.me/submissions/b8c7e06c-5833-41a2-816a-7a6e182728c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K012
import Definitions.Def_Q260K013
import Definitions.Def_Q260K015
import Theorems.Thm_OAI_KadisonKastler_concrete_ucp_starEquiv_of_published

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompletelyBounded
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
-- module Solutions.OAIQ075_KS.KadisonKastler_BlockMatrices
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.pairedRepresentation_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Two-by-two C⋆-matrix norm formulas

The diagonal embedding is a faithful star representation, so its norm is
the supremum norm. Multiplying by the flip unitary gives the corresponding
off-diagonal formula.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The lower-left entry of an operator commuting with a diagonal pair
is an intertwiner for that pair. -/
theorem block_commute_intertwines (D : CStarMatrix (Fin 2) (Fin 2) A) (a b : A)
    (h : D * blockDiagonal a b = blockDiagonal a b * D) :
    D 1 0 * a = b * D 1 0 := by
  have he := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) A => M 1 0) h
  simp only [CStarMatrix.mul_apply, Fin.sum_univ_two] at he
  change D 1 0 * a + D 1 1 * 0 = 0 * D 0 0 + b * D 1 0 at he
  simpa using he

/-- Closeness to the flip controls the lower-left intertwiner. -/
theorem norm_lowerLeft_sub_one_le (D : CStarMatrix (Fin 2) (Fin 2) A) :
    ‖D 1 0 - 1‖ ≤ ‖D - (blockFlip (A := A) : CStarMatrix (Fin 2) (Fin 2) A)‖ := by
  have h := CStarMatrix.norm_entry_le_norm
    (M := D - (blockFlip (A := A) : CStarMatrix (Fin 2) (Fin 2) A)) (i := 1) (j := 0)
  simp only [CStarMatrix.sub_apply] at h
  simpa [blockFlip] using h

end

end KadisonKastler

end OAI
end

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

omit [PartialOrder B] [StarOrderedRing B] in
theorem offDiagonalLinearMap_apply (b : B) :
    offDiagonalLinearMap b = blockOffDiagonal (-b) b := rfl

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
theorem completelyBoundedBy_offDiagonal_iff (F : A →ₗ[ℂ] B) (e : ℝ) :
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

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Polar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Polar unitaries close to the identity

We construct the polar factor of an invertible element using the positive
square root supplied by continuous functional calculus.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A : Type*} [CStarAlgebra A]

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Inverting a unit close to one gives the usual geometric-series bound. -/
theorem norm_unit_inv_le_of_near_one [Nontrivial A] (t : Aˣ)
    (ht : ‖(t : A) - 1‖ < 1) :
    ‖((t⁻¹ : Aˣ) : A)‖ ≤ (1 - ‖(t : A) - 1‖)⁻¹ := by
  have hpos : 0 < 1 - ‖(t : A) - 1‖ := sub_pos.mpr ht
  have hidentity : ((t⁻¹ : Aˣ) : A) - 1 =
      ((t⁻¹ : Aˣ) : A) * (1 - (t : A)) := by
    rw [mul_sub, mul_one, Units.inv_mul]
  have htriangle := norm_le_norm_sub_add (((t⁻¹ : Aˣ) : A)) (1 : A)
  have hproduct := norm_mul_le (((t⁻¹ : Aˣ) : A)) (1 - (t : A))
  rw [← hidentity, norm_sub_rev (1 : A) (t : A)] at hproduct
  rw [norm_one] at htriangle
  have hbound : (1 - ‖(t : A) - 1‖) * ‖((t⁻¹ : Aˣ) : A)‖ ≤ 1 := by nlinarith
  simpa only [mul_one] using (le_inv_mul_iff₀ hpos).mpr hbound

/-- A positive unit with upper bounds on its norm and inverse lies within
the same radius of the identity. -/
theorem norm_positive_unit_sub_one_le [Nontrivial A] (s : Aˣ) (hs : 0 ≤ (s : A)) {r : ℝ}
    (hr : 0 ≤ r) (hr₁ : r < 1) (hnorm : ‖(s : A)‖ ≤ 1 + r)
    (hinv : ‖((s⁻¹ : Aˣ) : A)‖ ≤ (1 - r)⁻¹) :
    ‖(s : A) - 1‖ ≤ r := by
  have hrepr : cfc (fun x : ℝ => x - 1) (s : A) = (s : A) - 1 := by
    rw [cfc_sub (fun x : ℝ => x) (fun _ : ℝ => 1) (s : A),
      cfc_id' ℝ (s : A), cfc_const_one ℝ (s : A)]
  rw [← hrepr]
  apply norm_cfc_le hr
  intro x hx
  have hx₀ : 0 ≤ x := spectrum_nonneg_of_nonneg hs hx
  have hxne : x ≠ 0 := by
    intro hzero
    exact spectrum.zero_notMem ℝ s.isUnit (hzero ▸ hx)
  have hxpos : 0 < x := lt_of_le_of_ne hx₀ (Ne.symm hxne)
  have hxupper : x ≤ 1 + r :=
    (Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans hnorm)
  have hxinv : x⁻¹ ≤ (1 - r)⁻¹ :=
    (Real.le_norm_self (x⁻¹)).trans
      ((spectrum.norm_le_norm_of_mem (spectrum.inv₀_mem_inv hx)).trans hinv)
  have hxlower : 1 - r ≤ x :=
    (inv_le_inv₀ hxpos (sub_pos.mpr hr₁)).mp hxinv
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Taking the absolute value of a unit does not increase its distance from
one, provided that distance is less than one. -/
theorem norm_abs_sub_one_le [Nontrivial A] (t : Aˣ)
    (ht : ‖(t : A) - 1‖ < 1) :
    ‖CFC.abs (t : A) - 1‖ ≤ ‖(t : A) - 1‖ := by
  obtain ⟨u, hu⟩ := exists_unitary_mul_abs t
  let s : Aˣ := (isUnit_abs t).unit
  have hs : (s : A) = CFC.abs (t : A) := (isUnit_abs t).unit_spec
  have hdecomp : (u : A) * (s : A) = (t : A) := by rwa [hs]
  have hinveq : ((s⁻¹ : Aˣ) : A) = ((t⁻¹ : Aˣ) : A) * (u : A) := by
    calc
      ((s⁻¹ : Aˣ) : A) =
          (((t⁻¹ : Aˣ) : A) * (t : A)) * ((s⁻¹ : Aˣ) : A) := by simp
      _ = (((t⁻¹ : Aˣ) : A) * ((u : A) * (s : A))) * ((s⁻¹ : Aˣ) : A) := by
        rw [hdecomp]
      _ = ((t⁻¹ : Aˣ) : A) * (u : A) := by
        simp only [mul_assoc, Units.mul_inv, mul_one]
  have hsinv : ‖((s⁻¹ : Aˣ) : A)‖ = ‖((t⁻¹ : Aˣ) : A)‖ := by
    rw [hinveq, CStarRing.norm_mul_coe_unitary]
  have hsnorm : ‖(s : A)‖ ≤ 1 + ‖(t : A) - 1‖ := by
    rw [hs, CFC.norm_abs]
    have h := norm_le_norm_sub_add (t : A) (1 : A)
    simpa only [norm_one, add_comm] using h
  rw [← hs]
  apply norm_positive_unit_sub_one_le s (by rw [hs]; exact CFC.abs_nonneg _)
    (norm_nonneg _) ht hsnorm
  rw [hsinv]
  exact norm_unit_inv_le_of_near_one t ht

/-- The polar unitary of a unit close to one is within twice that distance
of one. -/
theorem exists_polar_unitary_near_one_of_unit [Nontrivial A] (t : Aˣ)
    (ht : ‖(t : A) - 1‖ < 1) :
    ∃ u : unitary A, (u : A) * CFC.abs (t : A) = (t : A) ∧
      ‖(u : A) - 1‖ ≤ 2 * ‖(t : A) - 1‖ := by
  obtain ⟨u, hu⟩ := exists_unitary_mul_abs t
  refine ⟨u, hu, ?_⟩
  have hdiff : (u : A) - (t : A) = (u : A) * (1 - CFC.abs (t : A)) := by
    rw [mul_sub, mul_one, hu]
  calc
    ‖(u : A) - 1‖ ≤ ‖(u : A) - (t : A)‖ + ‖(t : A) - 1‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖1 - CFC.abs (t : A)‖ + ‖(t : A) - 1‖ := by
      rw [hdiff, CStarRing.norm_coe_unitary_mul]
    _ ≤ ‖(t : A) - 1‖ + ‖(t : A) - 1‖ := by
      apply add_le_add _ le_rfl
      simpa only [norm_sub_rev] using norm_abs_sub_one_le t ht
    _ = 2 * ‖(t : A) - 1‖ := by ring

/-- Every element within distance one of the identity has a unitary polar
factor within twice its original distance of the identity. -/
theorem exists_polar_unitary_near_one (T : A) (hT : ‖T - 1‖ < 1) :
    ∃ u : unitary A, (u : A) * CFC.abs T = T ∧ ‖(u : A) - 1‖ ≤ 2 * ‖T - 1‖ := by
  nontriviality A
  let t : Aˣ := Units.ofNearby 1 T (by simpa using hT)
  have ht : (t : A) = T := rfl
  simpa only [ht] using exists_polar_unitary_near_one_of_unit t (by rwa [ht])

end Ordered

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Intertwiner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Passing an intertwiner to its polar unitary

An invertible intertwiner of star representations has a unitary polar
factor which intertwines the same representations. Combining this with
the polar estimate gives the near-identity unitary used in the manuscript.
-/

namespace KadisonKastler

open scoped CStarAlgebra

variable {S B : Type*}
  [Ring S]
  [StarRing S]
  [_root_.Algebra ℂ S]
  [CStarAlgebra B]

/-- Taking adjoints reverses the intertwining relation. -/
theorem star_intertwines (ρ θ : S →⋆ₐ[ℂ] B) {T : B}
    (hT : ∀ x, T * ρ x = θ x * T) (x : S) :
    star T * θ x = ρ x * star T := by
  have h := congrArg star (hT (star x))
  simpa only [star_mul, map_star, star_star] using h.symm

/-- The square of the absolute value of an intertwiner commutes with the
source representation. -/
theorem intertwiner_star_mul_self_commute (ρ θ : S →⋆ₐ[ℂ] B) {T : B}
    (hT : ∀ x, T * ρ x = θ x * T) (x : S) :
    Commute (star T * T) (ρ x) := by
  change (star T * T) * ρ x = ρ x * (star T * T)
  calc
    (star T * T) * ρ x = star T * (T * ρ x) := mul_assoc _ _ _
    _ = star T * (θ x * T) := by rw [hT]
    _ = (star T * θ x) * T := (mul_assoc _ _ _).symm
    _ = (ρ x * star T) * T := by rw [star_intertwines ρ θ hT]
    _ = ρ x * (star T * T) := mul_assoc _ _ _

section Ordered

variable [PartialOrder B] [StarOrderedRing B]

/-- Continuous functional calculus passes the intertwiner commutation
relation to its absolute value. -/
theorem intertwiner_abs_commute (ρ θ : S →⋆ₐ[ℂ] B) {T : B}
    (hT : ∀ x, T * ρ x = θ x * T) (x : S) :
    Commute (CFC.abs T) (ρ x) := by
  exact (intertwiner_star_mul_self_commute ρ θ hT x).cfcₙ_nnreal NNReal.sqrt

/-- A unitary factor in the polar decomposition of an invertible
intertwiner remains an intertwiner. -/
theorem polar_unitary_intertwines (ρ θ : S →⋆ₐ[ℂ] B) {T : B}
    (hunit : IsUnit T) (hT : ∀ x, T * ρ x = θ x * T)
    (u : unitary B) (hpolar : (u : B) * CFC.abs T = T) (x : S) :
    (u : B) * ρ x = θ x * (u : B) := by
  have habs : IsUnit (CFC.abs T) := by
    obtain ⟨t, rfl⟩ := hunit
    exact isUnit_abs t
  apply habs.mul_right_cancel
  calc
    ((u : B) * ρ x) * CFC.abs T = (u : B) * (ρ x * CFC.abs T) := mul_assoc _ _ _
    _ = (u : B) * (CFC.abs T * ρ x) := by rw [(intertwiner_abs_commute ρ θ hT x).eq]
    _ = ((u : B) * CFC.abs T) * ρ x := (mul_assoc _ _ _).symm
    _ = θ x * T := by rw [hpolar, hT]
    _ = (θ x * (u : B)) * CFC.abs T := by rw [mul_assoc, hpolar]

end Ordered

/-- A near-identity star intertwiner produces a near-identity unitary
intertwiner. Only the existence of the original intertwiner is assumed. -/
theorem exists_near_unitary_intertwiner (ρ θ : S →⋆ₐ[ℂ] B) {T : B}
    (hT : ∀ x, T * ρ x = θ x * T) (hnear : ‖T - 1‖ < 1) :
    ∃ u : unitary B, (∀ x, (u : B) * ρ x = θ x * (u : B)) ∧
      ‖(u : B) - 1‖ ≤ 2 * ‖T - 1‖ := by
  let := CStarAlgebra.spectralOrder B
  let := CStarAlgebra.spectralOrderedRing B
  nontriviality B
  have hunit : IsUnit T := (Units.ofNearby 1 T (by simpa using hnear)).isUnit
  obtain ⟨u, hpolar, hnorm⟩ := exists_polar_unitary_near_one T hnear
  exact ⟨u, polar_unitary_intertwines ρ θ hunit hT u hpolar, hnorm⟩

/-- Unitary conjugation obtained from a near-identity star intertwiner. -/
theorem exists_near_unitary_conjugating (ρ θ : S →⋆ₐ[ℂ] B) {T : B}
    (hT : ∀ x, T * ρ x = θ x * T) (hnear : ‖T - 1‖ < 1) :
    ∃ u : unitary B, (∀ x, (u : B) * ρ x * star (u : B) = θ x) ∧
      ‖(u : B) - 1‖ ≤ 2 * ‖T - 1‖ := by
  obtain ⟨u, hu, hnorm⟩ := exists_near_unitary_intertwiner ρ θ hT hnear
  refine ⟨u, ?_, hnorm⟩
  intro x
  rw [hu, mul_assoc, Unitary.mul_star_self_of_mem u.property, mul_one]

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PairedRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CompletelyBoundedBy.toContinuousLinearMap_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.representedInnerDerivation_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Close representations from the published commutant-distance formula

The explicit input `PublishedBlockCommutantApproximation` is the block
specialization of Arveson's distance formula, in the form of Christensen,
*Perturbations of operator algebras II*, Indiana Univ. Math. J. 26 (1977),
Proposition 2.1. See also Christensen--Sinclair--Smith--White,
*Perturbations of C*-algebraic invariants*, GAFA 20 (2010), equation (2.1),
and Cameron et al., *Kadison--Kastler stable factors* (2014), equation (2.2).

The 2010 formulation applies to represented C*-algebras. Passing through
the quotient by the representation kernel gives the formulation below
with the complete bound on the source algebra. No normality is required.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {R : Type*}
  [Ring R]
  [_root_.Algebra ℂ R]

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem innerDerivation_flip_diagonal (a b : B) :
    innerDerivation (blockFlip (A := B) : CStarMatrix (Fin 2) (Fin 2) B)
      (blockDiagonal a b) = offDiagonalLinearMap (a - b) := by
  rw [offDiagonalLinearMap_apply]
  ext i j
  simp only [innerDerivation_apply, CStarMatrix.sub_apply, CStarMatrix.mul_apply,
    Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [blockFlip, blockDiagonal, blockOffDiagonal]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem pairedRepresentation_commutator_bound (ρ θ : A →⋆ₐ[ℂ] B) {e : ℝ}
    (hclose : CompletelyBoundedBy (ρ.toAlgHom.toLinearMap - θ.toAlgHom.toLinearMap) e) :
    CompletelyBoundedBy
      ((innerDerivation (blockFlip (A := B) : CStarMatrix (Fin 2) (Fin 2) B)).comp
        (pairedRepresentation ρ θ).toAlgHom.toLinearMap) e := by
  have hid :
      (innerDerivation (blockFlip (A := B) : CStarMatrix (Fin 2) (Fin 2) B)).comp
        (pairedRepresentation ρ θ).toAlgHom.toLinearMap =
      offDiagonalLinearMap.comp (ρ.toAlgHom.toLinearMap - θ.toAlgHom.toLinearMap) := by
    apply LinearMap.ext
    intro x
    change innerDerivation
      (blockFlip (A := B) : CStarMatrix (Fin 2) (Fin 2) B)
      (pairedRepresentation ρ θ x) = offDiagonalLinearMap (ρ x - θ x)
    rw [pairedRepresentation_apply]
    exact innerDerivation_flip_diagonal (ρ x) (θ x)
  rw [hid]
  exact (completelyBoundedBy_offDiagonal_iff _ e).mpr hclose

variable (A) (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] OAI.KadisonKastler.instStarOrderedRingContinuousLinearMapComplexId_solutions
variable {A K}

attribute [local instance] OAI.KadisonKastler.instPartialOrderContinuousLinearMapComplexId_solutions
/-- Completely close representations are conjugate by a unitary close
to the identity, conditional only on the published distance formula. -/
theorem close_representations_of_published
    (hPublished : PublishedBlockCommutantApproximation A K)
    (ρ θ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) {e : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 4)
    (hclose : CompletelyBoundedBy (ρ.toAlgHom.toLinearMap - θ.toAlgHom.toLinearMap) e) :
    ∃ u : unitary (K →L[ℂ] K),
      (∀ x, (u : K →L[ℂ] K) * ρ x * star (u : K →L[ℂ] K) = θ x) ∧
      ‖(u : K →L[ℂ] K) - 1‖ ≤ 4 * e := by
  by_cases hezero : e = 0
  · have heq : ∀ x, ρ x = θ x := by
      intro x
      have h := hclose 1 1 (CStarMatrix.toOneByOne (Fin 1) ℂ A x)
      rw [hezero, zero_mul] at h
      have hm := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
      have hx := congrArg (fun M : CStarMatrix (Fin 1) (Fin 1) (K →L[ℂ] K) => M 0 0) hm
      change ρ x - θ x = 0 at hx
      exact sub_eq_zero.mp hx
    exact ⟨1, by simpa using heq, by simp [hezero]⟩
  have hep : 0 < e := lt_of_le_of_ne he (Ne.symm hezero)
  let π := pairedRepresentation ρ θ
  let S : CStarMatrix (Fin 2) (Fin 2) (K →L[ℂ] K) :=
    blockFlip (A := K →L[ℂ] K)
  obtain ⟨D, hcomm, hDS⟩ := hPublished π S e he
    (pairedRepresentation_commutator_bound ρ θ hclose) (2 * e) (by linarith)
  have hT : ∀ x, D 1 0 * ρ x = θ x * D 1 0 := by
    intro x
    exact block_commute_intertwines D (ρ x) (θ x)
      (by simpa only [π, pairedRepresentation_apply] using hcomm x)
  have hTnorm : ‖D 1 0 - 1‖ < 2 * e :=
    (norm_lowerLeft_sub_one_le D).trans_lt hDS
  have hnear : ‖D 1 0 - 1‖ < 1 := by linarith
  obtain ⟨u, hu, hnorm⟩ := exists_near_unitary_conjugating ρ θ hT hnear
  exact ⟨u, hu, by linarith⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConcreteUCP
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The UCP criterion for concrete von Neumann algebras

The ordinary Kadison--Kastler gap supplies precisely the reverse unit-ball
approximation used in the UCP range argument.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.instStarOrderedRingContinuousLinearMapComplexId_solutions_1
attribute [local instance] OAI.KadisonKastler.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_2
attribute [local instance] OAI.KadisonKastler.instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_2
/-- An intertwining star-algebra equivalence gives equality of the
concrete algebras after unitary conjugation. -/
theorem conjugates_of_starEquiv {M N : VonNeumannAlgebra H}
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) (u : unitary (H →L[ℂ] H))
    (hθ : ∀ x : Algebra M,
      (u : H →L[ℂ] H) * algebraInclusion M x * star (u : H →L[ℂ] H) =
        algebraInclusion N (θ x)) :
    Conjugates u M N := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [show unitaryConj u x = algebraInclusion N (θ ⟨x, hx⟩) from hθ ⟨x, hx⟩]
    exact (θ ⟨x, hx⟩).property
  · intro y hy
    obtain ⟨x, hx⟩ := θ.surjective ⟨y, hy⟩
    change θ x = ⟨y, hy⟩ at hx
    refine ⟨(x : H →L[ℂ] H), x.property, ?_⟩
    change (u : H →L[ℂ] H) * algebraInclusion M x * star (u : H →L[ℂ] H) = y
    rw [hθ, hx]
    rfl

attribute [local instance] OAI.KadisonKastler.instPartialOrderContinuousLinearMapComplexId_solutions_1
/-- The unitary-conjugacy conclusion of the UCP criterion for concrete
algebras. Both published inputs are explicit, while positivity,
surjectivity, correction estimates, and polar implementation are proved. -/
theorem concrete_ucp_unitary_of_published_oai {M N : VonNeumannAlgebra H}
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (φ : Algebra M →CP Algebra N) (hφ : φ 1 = 1)
    {e g : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000) (hge : g + e < 1)
    (hclose : CompletelyBoundedBy
      ((algebraInclusion N).toAlgHom.toLinearMap.comp φ.toLinearMap -
        (algebraInclusion M).toAlgHom.toLinearMap) e)
    (hgap : kkDistance M N < g) :
    ∃ u : unitary (H →L[ℂ] H),
      Conjugates u M N ∧ ‖(u : H →L[ℂ] H) - 1‖ ≤ 128 * e := by
  obtain ⟨θ, hθ⟩ := concrete_ucp_starEquiv_of_published hCorrection φ hφ
    he he₁ hge hclose hgap
  let θrep : Algebra M →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    (algebraInclusion N).comp θ.toStarAlgHom
  have hrep : θrep.toAlgHom.toLinearMap =
      (algebraInclusion N).toAlgHom.toLinearMap.comp θ.toAlgEquiv.toLinearMap := by
    ext x
    rfl
  have hreverse : CompletelyBoundedBy
      ((algebraInclusion M).toAlgHom.toLinearMap - θrep.toAlgHom.toLinearMap)
      (32 * e) := by
    intro p q X
    have h := hθ p q X
    rw [matrix_map_sub] at h
    rw [hrep, matrix_map_sub]
    simpa only [norm_sub_rev] using h
  obtain ⟨u, hu, hnorm⟩ := close_representations_of_published hCommutant
    (algebraInclusion M) θrep (by positivity) (by linarith) hreverse
  refine ⟨u, conjugates_of_starEquiv θ u hu, ?_⟩
  linarith

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.concrete_ucp_unitary_of_published_oai.{u} := @OAI.KadisonKastler.concrete_ucp_unitary_of_published_oai.{u}
