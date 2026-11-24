-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.mem_stab_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:54:36.65073+00:00
-- url     : https://prove2.me/submissions/fec3f2f9-01b5-4cae-9b04-38fc8f042e19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_PFlag_mem_stab_iff_map

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
theorem _root_.solution {g : GL (Fin n) k} : g ∈ F.stab ↔ g.val ∈ F.lieQ := by
  refine ⟨fun h => h.1, fun h => mem_stab_iff_map.2 fun V hV => ?_⟩
  refine Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨v, hv, rfl⟩; exact h V hV v hv) ?_
  refine (Submodule.equivMapOfInjective _ (fun v w hvw => ?_) V).finrank_eq.symm
  have := congrArg (g⁻¹.val *ᵥ ·) hvw
  simpa [mulVec_mulVec] using this
end GlobalTheory.Tw.PFlag
