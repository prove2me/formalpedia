-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.exists_ringEquiv_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:56:28.63451+00:00
-- url     : https://prove2.me/submissions/5d04737a-8bac-454f-8e8f-265be20edc3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Theorems.Thm_GlobalTheory_GaloisDescent_exists_ringEquiv_of_isTranscendenceBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Cardinal
open GlobalTheory GlobalTheory.GaloisDescent
namespace GlobalTheory.GaloisDescent
theorem _root_.solution {F L : Type*} [Field F] [Field L] [Algebra F L] [IsAlgClosed L]
    (τ : F ≃+* F) : ∃ σ : L ≃+* L, ∀ a, σ (algebraMap F L a) = algebraMap F L (τ a) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F L
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_isTranscendenceBasis hs hs (mapEquiv s τ)
  refine ⟨σ, fun a => ?_⟩
  simpa using hσ (C a)
end GlobalTheory.GaloisDescent
