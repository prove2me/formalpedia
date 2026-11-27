-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.mem_unip_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:00.742952+00:00
-- url     : https://prove2.me/submissions/2aee6c54-f888-4e69-9bcc-3189d5340c61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_PFlag_lieN_le_lieQ
import Theorems.Thm_GlobalTheory_Tw_PFlag_mem_stab_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
open GlobalTheory.Tw.PFlag
variable {n : ℕ} {k : Type} [Field k] {F : PFlag n k}
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution {g : GL (Fin n) k} : g ∈ F.unip ↔ g.val - 1 ∈ F.lieN := by
  refine ⟨fun h => h.2, fun h => ⟨mem_stab_iff.2 ?_, h⟩⟩
  simpa using add_mem (lieN_le_lieQ h) one_mem_lieQ
end GlobalTheory.Tw.PFlag
