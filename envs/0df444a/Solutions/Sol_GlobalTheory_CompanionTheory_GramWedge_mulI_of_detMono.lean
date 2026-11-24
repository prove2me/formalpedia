-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:21:26.455126+00:00
-- url     : https://prove2.me/submissions/99f401ab-5538-4618-87d0-cc9e77e2b4ba

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityInfinitePlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_GramWedge_posSemidef_smul_gram_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_GramWedge_gram_mul_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GramWedge
namespace GlobalTheory.CompanionTheory.GramWedge
theorem _root_.solution : DetMono → MulI := by
  intro hm ι ι' κ _ _ _ _ A
  refine ⟨fun g => ?_, fun s => ?_, fun s => ?_⟩
  · have h := hm κ _ _ (posSemidef_conjTranspose_mul_self (g * A)) (posSemidef_smul_gram_sub g A)
    rw [det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at h
    exact h
  · simp only [nI]
    rw [gram_mul_det, Complex.re_ofReal_mul, mul_comm]
  · have h := gram_mul_det (1 : Matrix κ κ ℂ) s
    simp only [Matrix.one_mul, conjTranspose_one, Matrix.mul_one, det_one, mul_one] at h
    simp only [nI]
    rw [h, Complex.ofReal_re]
end GlobalTheory.CompanionTheory.GramWedge
