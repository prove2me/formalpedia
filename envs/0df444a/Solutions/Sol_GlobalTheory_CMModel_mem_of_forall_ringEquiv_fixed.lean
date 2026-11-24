-- Prove2me | solution 1 for GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:04:03.490054+00:00
-- url     : https://prove2.me/submissions/0301f7f0-c95a-43e3-bc62-3ede0456917f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIntermediateFieldOfForallComplexAutFixed
import Theorems.Thm_GlobalTheory_GaloisDescent_complex_mem_range_of_forall_algEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMModel
namespace GlobalTheory.CMModel
theorem _root_.solution :
    ∀ (F : IntermediateField ℚ ℂ) (x : ℂ),
      (∀ σ : ℂ ≃+* ℂ, (∀ y ∈ F, σ y = y) → σ x = x) → x ∈ F := fun F x hx ↦ by
  obtain ⟨y, rfl⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := F) x
    fun σ ↦ hx σ.toRingEquiv fun y hy ↦ σ.commutes ⟨y, hy⟩
  exact y.2
end GlobalTheory.CMModel
