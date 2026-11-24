-- Prove2me | solution 1 for GlobalTheory.Cyc.FontW.Dv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:53.654149+00:00
-- url     : https://prove2.me/submissions/e408a747-d1e1-4fb9-8f6d-65e1dbda6a8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight
import Theorems.Thm_GlobalTheory_Cyc_FontW_mem_Dv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FontW
namespace GlobalTheory.Cyc.FontW
theorem _root_.solution {l r : ℕ} {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (a : A) {x : M}
    (hx : x ∈ Dv l r M) : a • x ∈ Dv l r M := by
  obtain ⟨y, rfl⟩ := mem_Dv.1 hx
  exact mem_Dv.2 ⟨a • y, smul_comm _ _ _⟩
end GlobalTheory.Cyc.FontW
