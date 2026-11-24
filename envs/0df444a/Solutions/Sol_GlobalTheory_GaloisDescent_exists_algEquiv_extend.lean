-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.exists_algEquiv_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:17:10.180431+00:00
-- url     : https://prove2.me/submissions/24002d53-d212-494a-9e3a-bec6e0aff31d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Theorems.Thm_GlobalTheory_GaloisDescent_exists_ringEquiv_extend

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
theorem _root_.solution {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F]
    [Algebra F L] [Algebra K L] [IsScalarTower K F L] [IsAlgClosed L]
    (τ : F ≃ₐ[K] F) : ∃ σ : L ≃ₐ[K] L, ∀ a, σ (algebraMap F L a) = algebraMap F L (τ a) := by
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_extend (L := L) τ.toRingEquiv
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun k => ?_, hσ⟩
  rw [IsScalarTower.algebraMap_apply K F L, hσ]
  congr 1
  exact τ.commutes k
end GlobalTheory.GaloisDescent
