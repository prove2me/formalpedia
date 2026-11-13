-- Prove2me | solution 1 for OAI.KadisonKastler.finiteAveragedDifferential_defect_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:09:00.429409+00:00
-- url     : https://prove2.me/submissions/0f85b831-733b-4489-b402-b37de8b4f93f

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
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCochainDifferential
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Hochschild matrix identities with arbitrary finite intermediate indices. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- Algebraic associativity survives every rectangular matrix amplification. -/
theorem finiteBilinearProduct_assoc (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y z, m (m x y) z = m x (m y z)) {p r s q : Type*} [Fintype r] [Fintype s]
    (X : CStarMatrix p r A) (Y : CStarMatrix r s A)
    (Z : CStarMatrix s q A) :
    finiteBilinearProduct m (finiteBilinearProduct m X Y) Z =
      finiteBilinearProduct m X (finiteBilinearProduct m Y Z) := by
  ext i l
  simp only [finiteBilinearProduct_apply, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hm _ _ _

theorem rectangular_mul_assoc_finite {p r s q : Type*} [Fintype r] [Fintype s]
    (X : CStarMatrix p r A) (Y : CStarMatrix r s A)
    (Z : CStarMatrix s q A) : (X * Y) * Z = X * (Y * Z) := by
  ext i l
  change (∑ k, (∑ j, X i j * Y j k) * Z k l) =
    ∑ j, X i j * (∑ k, Y j k * Z k l)
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- The Maurer--Cartan identity, with its signs fixed for the correction step. -/
theorem finiteMatrixDifferential_defect (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y z, m (m x y) z = m x (m y z)) {p r s q : Type*} [Fintype r] [Fintype s]
    (X : CStarMatrix p r A) (Y : CStarMatrix r s A)
    (Z : CStarMatrix s q A) :
    let f := m - LinearMap.mul ℂ A
    finiteMatrixDifferential f X Y Z =
      finiteBilinearProduct f (finiteBilinearProduct f X Y) Z -
        finiteBilinearProduct f X (finiteBilinearProduct f Y Z) := by
  let f := m - LinearMap.mul ℂ A
  have hm' : m = LinearMap.mul ℂ A + f := by dsimp [f]; abel
  have he := finiteBilinearProduct_assoc m hm X Y Z
  rw [hm'] at he
  simp only [finiteBilinearProduct_add, finiteBilinearProduct_mul, finiteBilinearProduct_add_left,
    finiteBilinearProduct_add_right, rectangular_mul_assoc_finite] at he
  dsimp only [finiteMatrixDifferential]
  change X * finiteBilinearProduct f Y Z - finiteBilinearProduct f (X * Y) Z +
      finiteBilinearProduct f X (Y * Z) - finiteBilinearProduct f X Y * Z = _
  have he' := congrArg (fun T => T - (X * Y) * Z -
    finiteBilinearProduct f (X * Y) Z - finiteBilinearProduct f X Y * Z -
    finiteBilinearProduct f X (finiteBilinearProduct f Y Z)) he
  rw [← rectangular_mul_assoc_finite] at he'
  symm
  convert he' using 1 <;> first | (with_reducible_and_instances rfl) | (abel)

variable [PartialOrder A] [StarOrderedRing A]

theorem finiteMatrixDifferential_defect_bound
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y z, m (m x y) z = m x (m y z)) {c : ℝ} (hc : 0 ≤ c)
    (hf : HaagerupBound (m - LinearMap.mul ℂ A) c) {p r s q : Type*} [Fintype p] [Fintype r] [Fintype s] [Fintype q]
    (X : CStarMatrix p r A) (Y : CStarMatrix r s A)
    (Z : CStarMatrix s q A) :
    ‖finiteMatrixDifferential (m - LinearMap.mul ℂ A) X Y Z‖ ≤
      2 * c ^ 2 * ‖X‖ * ‖Y‖ * ‖Z‖ := by
  rw [finiteMatrixDifferential_defect m hm]
  calc
    _ ≤ ‖finiteBilinearProduct (m - LinearMap.mul ℂ A)
          (finiteBilinearProduct (m - LinearMap.mul ℂ A) X Y) Z‖ +
        ‖finiteBilinearProduct (m - LinearMap.mul ℂ A) X
          (finiteBilinearProduct (m - LinearMap.mul ℂ A) Y Z)‖ := norm_sub_le _ _
    _ ≤ c * (c * ‖X‖ * ‖Y‖) * ‖Z‖ + c * ‖X‖ * (c * ‖Y‖ * ‖Z‖) := by
      apply add_le_add
      · exact (hf.finite _ Z).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hf.finite X Y) hc) (norm_nonneg Z))
      · exact (hf.finite X _).trans (mul_le_mul_of_nonneg_left
          (hf.finite Y Z) (mul_nonneg hc (norm_nonneg X)))
    _ = _ := by ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteRowAverages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Finite row averages, their composition law, and the cochain identity.
These are the algebraic operations of Christensen--Sinclair row averaging.
No existence of an invariant averaging projection is assumed here. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The cochain residual is exactly a module defect minus the averaged
Hochschild differential. The module defect vanishes at an invariant limit. -/
theorem finiteCochainAverage_residual (r : ι → A)
    (hr : ∑ i, r i * star (r i) = 1) (f : A →ₗ[ℂ] A →ₗ[ℂ] A) (x y : A) :
    f x y - linearCoboundary (finiteCochainAverage r f) x y =
      finiteRightAverage r (f x) y - finiteCochainAverage r f x * y -
        ∑ i, cochainDifferential f x y (r i) * star (r i) := by
  simp only [linearCoboundary_apply, finiteCochainAverage_apply, finiteRightAverage_apply,
    cochainDifferential, sub_mul, add_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, hr, mul_one]
  abel

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RowCochainResidual
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The finite-row residual has a quadratic bound after removing its module defect. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem finiteAveragedDifferential_apply {κ : Type*} [Fintype κ] (r : κ → A)
    (hr : ∑ k, r k * star (r k) = 1) (f : A →ₗ[ℂ] A →ₗ[ℂ] A) (x y : A) :
    finiteAveragedDifferential r f x y =
      ∑ k, cochainDifferential f x y (r k) * star (r k) := by
  have h := finiteCochainAverage_residual r hr f x y
  change (finiteRightAverage r (f x) y - finiteCochainAverage r f x * y) -
    (f x y - linearCoboundary (finiteCochainAverage r f) x y) = _
  rw [h]
  abel

theorem cochainDifferential_zero (f : A →ₗ[ℂ] A →ₗ[ℂ] A) (x y : A) :
    cochainDifferential f x y 0 = 0 := by simp [cochainDifferential]

theorem finiteMatrixDifferential_apply (f : A →ₗ[ℂ] A →ₗ[ℂ] A)
    {p r s q : Type*} [Fintype r] [Fintype s]
    (X : CStarMatrix p r A) (Y : CStarMatrix r s A) (Z : CStarMatrix s q A)
    (i : p) (l : q) :
    finiteMatrixDifferential f X Y Z i l =
      ∑ j, ∑ k, cochainDifferential f (X i j) (Y j k) (Z k l) := by
  simp only [finiteMatrixDifferential, CStarMatrix.sub_apply, CStarMatrix.add_apply,
    CStarMatrix.mul_apply, finiteBilinearProduct_apply, map_sum, LinearMap.sum_apply,
    Finset.mul_sum, Finset.sum_mul, cochainDifferential, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun k j => f (X i j * Y j k) (Z k l)),
    Finset.sum_comm (f := fun k j => f (X i j) (Y j k) * Z k l)]

/-- Exact matrix identity for the averaged Hochschild differential. -/
theorem finiteAveragedDifferential_matrix {κ : Type*} [Fintype κ]
    (r : κ → A) (hr : ∑ k, r k * star (r k) = 1)
    (f : A →ₗ[ℂ] A →ₗ[ℂ] A) {p t q : ℕ}
    (X : CStarMatrix (Fin p) (Fin t) A) (Y : CStarMatrix (Fin t) (Fin q) A) :
    bilinearProduct (finiteAveragedDifferential r f) X Y =
      finiteMatrixDifferential f X Y (rowReplication r) * (rowReplication r).conjTranspose := by
  ext i j
  simp only [bilinearProduct_apply, finiteAveragedDifferential_apply r hr,
    CStarMatrix.mul_apply, CStarMatrix.conjTranspose_apply, finiteMatrixDifferential_apply,
    Fintype.sum_prod_type, rowReplication_apply]
  simp_rw [apply_ite]
  simp only [star_zero, cochainDifferential_zero, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]


variable [PartialOrder A] [StarOrderedRing A]

/-- Averaging the differential of an associative multiplication defect
costs at most twice the square of its complete norm. -/
theorem finiteAveragedDifferential_defect_bound_oai {κ : Type*} [Fintype κ]
    (r : κ → A) (hr : ∑ k, r k * star (r k) = 1)
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (hm : ∀ x y z, m (m x y) z = m x (m y z))
    {c : ℝ} (hc : 0 ≤ c) (hf : HaagerupBound (m - LinearMap.mul ℂ A) c) :
    HaagerupBound (finiteAveragedDifferential r (m - LinearMap.mul ℂ A)) (2 * c ^ 2) := by
  intro p t q X Y
  have hb := rowReplication_norm_bounds (ι := Fin q) r hr
  rw [finiteAveragedDifferential_matrix r hr]
  calc
    _ ≤ ‖finiteMatrixDifferential (m - LinearMap.mul ℂ A) X Y (rowReplication r)‖ *
        ‖(rowReplication r).conjTranspose‖ := rectangular_norm_mul_le_finite _ _
    _ ≤ (2 * c ^ 2 * ‖X‖ * ‖Y‖ * ‖rowReplication r‖) *
        ‖(rowReplication r).conjTranspose‖ :=
      mul_le_mul_of_nonneg_right
        (finiteMatrixDifferential_defect_bound m hm hc hf X Y _) (norm_nonneg _)
    _ ≤ 2 * c ^ 2 * ‖X‖ * ‖Y‖ := by
      calc
        _ ≤ (2 * c ^ 2 * ‖X‖ * ‖Y‖ * 1) * 1 := by gcongr; exacts [hb.1, hb.2]
        _ = _ := by ring

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.finiteAveragedDifferential_defect_bound_oai.{u_1, u_2} := @OAI.KadisonKastler.finiteAveragedDifferential_defect_bound_oai.{u_1, u_2}
