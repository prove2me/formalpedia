-- Prove2me | solution 1 for OAI.KadisonKastler.HaagerupBound.finiteCochainAverage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:59:07.553321+00:00
-- url     : https://prove2.me/submissions/5c5e69df-6905-4ea0-9ae8-31989b928b08

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Definitions.Def_Q260K015

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteMatrixBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Finite index changes for the rectangular matrix estimates used in row averaging. -/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Independent changes of row and column indices preserve the matrix norm. -/
theorem norm_reindex_rectangular {ι κ ι' κ' : Type*}
    [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (e : ι ≃ ι') (d : κ ≃ κ') (X : CStarMatrix ι κ A) :
    ‖CStarMatrix.reindexₗ ℂ A e d X‖ = ‖X‖ := by
  classical
  have he : rectangularCorner (CStarMatrix.reindexₗ ℂ A e d X) =
      CStarMatrix.reindexₐ ℂ A (Equiv.sumCongr e d) (rectangularCorner X) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  calc
    _ = ‖rectangularCorner (CStarMatrix.reindexₗ ℂ A e d X)‖ :=
      (norm_rectangularCorner _).symm
    _ = ‖CStarMatrix.reindexₐ ℂ A (Equiv.sumCongr e d) (rectangularCorner X)‖ :=
      congrArg norm he
    _ = ‖rectangularCorner X‖ := NonUnitalStarAlgHom.norm_map
      (CStarMatrix.reindexₐ ℂ A (Equiv.sumCongr e d)).toStarAlgHom
      (CStarMatrix.reindexₐ ℂ A (Equiv.sumCongr e d)).injective _
    _ = ‖X‖ := norm_rectangularCorner X

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteHaagerupBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Finite index changes for bilinear amplifications. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem finiteBilinearProduct_reindex (f : A →ₗ[ℂ] A →ₗ[ℂ] A)
    {ι κ τ ι' κ' τ' : Type*} [Fintype κ] [Fintype κ']
    (e : ι ≃ ι') (d : κ ≃ κ') (g : τ ≃ τ')
    (X : CStarMatrix ι κ A) (Y : CStarMatrix κ τ A) :
    CStarMatrix.reindexₗ ℂ A e g (finiteBilinearProduct f X Y) =
      finiteBilinearProduct f (CStarMatrix.reindexₗ ℂ A e d X)
        (CStarMatrix.reindexₗ ℂ A d g Y) := by
  ext i j
  apply Fintype.sum_equiv d
  intro k
  change f (X (e.symm i) k) (Y k (g.symm j)) =
    f (X (e.symm i) (d.symm (d k))) (Y (d.symm (d k)) (g.symm j))
  rw [d.symm_apply_apply]

theorem HaagerupBound.finite {f : A →ₗ[ℂ] A →ₗ[ℂ] A} {c : ℝ}
    (hf : HaagerupBound f c) {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ]
    (X : CStarMatrix ι κ A) (Y : CStarMatrix κ τ A) :
    ‖finiteBilinearProduct f X Y‖ ≤ c * ‖X‖ * ‖Y‖ := by
  classical
  let e := Fintype.equivFin ι
  let d := Fintype.equivFin κ
  let g := Fintype.equivFin τ
  have h := hf _ _ _ (CStarMatrix.reindexₗ ℂ A e d X)
    (CStarMatrix.reindexₗ ℂ A d g Y)
  change ‖finiteBilinearProduct f (CStarMatrix.reindexₗ ℂ A e d X)
    (CStarMatrix.reindexₗ ℂ A d g Y)‖ ≤ _ at h
  rwa [← finiteBilinearProduct_reindex, norm_reindex_rectangular,
    norm_reindex_rectangular, norm_reindex_rectangular] at h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteRowCochains
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.finiteBilinearProduct_add _root_.OAI.KadisonKastler.finiteBilinearProduct_add_left _root_.OAI.KadisonKastler.finiteBilinearProduct_add_right _root_.OAI.KadisonKastler.finiteBilinearProduct_apply _root_.OAI.KadisonKastler.finiteBilinearProduct_mul _root_.OAI.KadisonKastler.finiteBilinearProduct_smul _root_.OAI.KadisonKastler.finiteBilinearProduct_sub _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Complete norm bounds for the finite cochain averages. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq ι]

omit [Fintype κ] [Fintype τ] in
theorem finiteBilinearProduct_rowReplication_apply (f : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (X : CStarMatrix τ ι A) (r : κ → A) (i : τ) (jk : ι × κ) :
    finiteBilinearProduct f X (rowReplication r) i jk = f (X i jk.1) (r jk.2) := by
  change (∑ j, f (X i j) (if j = jk.1 then r jk.2 else 0)) = _
  simp [apply_ite]

omit [Fintype τ] in
/-- The cochain average at a matrix is a bilinear amplification followed by
multiplication with the adjoint of the replicated row. -/
theorem finiteCochainAverage_matrix (r : κ → A) (f : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (X : CStarMatrix τ ι A) :
    CStarMatrix.mapₗ (finiteCochainAverage r f) X =
      finiteBilinearProduct f X (rowReplication r) * (rowReplication r).conjTranspose := by
  ext i j
  change (∑ k, f (X i j) (r k) * star (r k)) =
    ∑ jk : ι × κ, finiteBilinearProduct f X (rowReplication r) i jk *
      star (rowReplication r j jk)
  simp_rw [finiteBilinearProduct_rowReplication_apply]
  simp only [Fintype.sum_prod_type, rowReplication_apply]
  simp_rw [apply_ite star, star_zero, mul_ite, mul_zero]
  simp

variable [PartialOrder A] [StarOrderedRing A]

/-- A normalized row produces a linear cochain with no loss of complete norm. -/
theorem HaagerupBound.finiteCochainAverage_oai {f : A →ₗ[ℂ] A →ₗ[ℂ] A} {c : ℝ}
    (hf : HaagerupBound f c) (hc : 0 ≤ c)
    (r : κ → A) (hr : ∑ k, r k * star (r k) = 1) :
    CompletelyBoundedBy (finiteCochainAverage r f) c := by
  intro p q X
  have hb := rowReplication_norm_bounds (ι := Fin q) r hr
  rw [finiteCochainAverage_matrix]
  calc
    _ ≤ ‖finiteBilinearProduct f X (rowReplication r)‖ * ‖(rowReplication r).conjTranspose‖ :=
      rectangular_norm_mul_le_finite _ _
    _ ≤ (c * ‖X‖ * ‖rowReplication r‖) * ‖(rowReplication r).conjTranspose‖ := by
      exact mul_le_mul_of_nonneg_right (hf.finite _ _) (norm_nonneg _)
    _ ≤ c * ‖X‖ := by
      calc
        _ ≤ (c * ‖X‖ * 1) * 1 := by gcongr; exacts [hb.1, hb.2]
        _ = _ := by ring

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_3} : type_of% @OAI.KadisonKastler.HaagerupBound.finiteCochainAverage_oai.{u_1, u_3} := @OAI.KadisonKastler.HaagerupBound.finiteCochainAverage_oai.{u_1, u_3}
