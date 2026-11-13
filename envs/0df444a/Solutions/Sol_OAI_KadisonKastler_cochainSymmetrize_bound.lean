-- Prove2me | solution 1 for OAI.KadisonKastler.cochainSymmetrize_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:08:36.414413+00:00
-- url     : https://prove2.me/submissions/f602a7d8-3c60-4270-85d5-df5afbb6c80c

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Complex
import Definitions.Def_Q260K013

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OperatorCochainStar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Involution symmetrization of operator-valued cochains -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem matrix_cochainSharp (D : A →ₗ[ℂ] A) {p q : ℕ}
    (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (cochainSharp D) X =
      (CStarMatrix.mapₗ D X.conjTranspose).conjTranspose := by
  ext i j
  rfl


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RectangularRowNorm
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Rectangular row norm estimates on finite Hilbert C-star modules. -/

namespace KadisonKastler

noncomputable section

open scoped WithCStarModule InnerProductSpace
open CStarModule

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]


/-- Transposition to the adjoint column does not increase the rectangular norm. -/
theorem norm_conjTranspose_le_finite (Y : CStarMatrix ι κ A) :
    ‖Y.conjTranspose‖ ≤ ‖Y‖ := by
  have hs := rectangular_norm_sq_le Y.conjTranspose
  have he : Y.conjTranspose.conjTranspose = Y := by ext i j; simp
  rw [he] at hs
  have hm := rectangular_norm_mul_le_finite Y.conjTranspose Y
  nlinarith [norm_nonneg Y, norm_nonneg Y.conjTranspose]

/-- Conjugate transpose preserves every rectangular matrix norm. -/
theorem norm_conjTranspose_finite (X : CStarMatrix ι κ A) : ‖X.conjTranspose‖ = ‖X‖ := by
  apply le_antisymm (norm_conjTranspose_le_finite X)
  have h := norm_conjTranspose_le_finite X.conjTranspose
  have he : X.conjTranspose.conjTranspose = X := by ext i j; simp
  rwa [he] at h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CochainStarBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Involution symmetrization preserves cochain bounds in the represented algebra. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem cochainSharp_bound {D : A →ₗ[ℂ] A} {c : ℝ}
    (hD : CompletelyBoundedBy D c) : CompletelyBoundedBy (cochainSharp D) c := by
  intro p q X
  rw [matrix_cochainSharp, norm_conjTranspose_finite]
  simpa only [norm_conjTranspose_finite] using hD q p X.conjTranspose

theorem cochainSymmetrize_bound_oai
    {D : A →ₗ[ℂ] A} {c : ℝ}
    (hD : CompletelyBoundedBy D c) : CompletelyBoundedBy (cochainSymmetrize D) c := by
  intro p q X
  have he : CStarMatrix.mapₗ (cochainSymmetrize D) X =
      (1/2 : ℂ) • (CStarMatrix.mapₗ D X + CStarMatrix.mapₗ (cochainSharp D) X) := by
    ext i j
    rfl
  rw [he, norm_smul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  calc
    (1/2 : ℝ) * ‖CStarMatrix.mapₗ D X + CStarMatrix.mapₗ (cochainSharp D) X‖ ≤
        (1/2 : ℝ) * (c * ‖X‖ + c * ‖X‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (norm_add_le _ _).trans (add_le_add (hD p q X) (cochainSharp_bound hD p q X))
    _ = _ := by ring


end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.cochainSymmetrize_bound_oai.{u_1} := @OAI.KadisonKastler.cochainSymmetrize_bound_oai.{u_1}
