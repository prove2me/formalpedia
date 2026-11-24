-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.etaK_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:50:19.835798+00:00
-- url     : https://prove2.me/submissions/02a43381-6897-4db4-bed7-494cd4493585

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourBProdIteratedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplittingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConditionProductSplitting
import Theorems.Thm_GlobalTheory_JR_WeilProd_norm_split
import Theorems.Thm_GlobalTheory_T_unramifiedValuationParitySign_character_kernel_norms


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilProd
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilProd
theorem _root_.solution [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (s : A.Kˣ) :
    A.etaK s = A₁.etaK (eK s).1 * A₂.etaK (eK s).2 := by
  have hu : IsUnit (eK (s : A.K)) := s.isUnit.map eK
  have h₁ : Algebra.norm F (eK s).1 ≠ 0 := ((Prod.isUnit_iff.1 hu).1.map (Algebra.norm F)).ne_zero
  have h₂ : Algebra.norm F (eK s).2 ≠ 0 := ((Prod.isUnit_iff.1 hu).2.map (Algebra.norm F)).ne_zero
  simp only [Et.etaK]
  rw [norm_split A A₁ A₂ eK, (GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E).1 _ _ h₁ h₂]
end GlobalTheory.JR.WeilProd
