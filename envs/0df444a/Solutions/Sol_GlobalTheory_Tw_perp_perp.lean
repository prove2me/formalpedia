-- Prove2me | solution 1 for GlobalTheory.Tw.perp_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:42:30.50032+00:00
-- url     : https://prove2.me/submissions/6a917caf-c3f9-4d59-a3af-f404d52ea1eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_dot_star_comm_zero
import Theorems.Thm_GlobalTheory_Tw_eq_zero_of_mem_perp
import Theorems.Thm_GlobalTheory_Tw_sup_perp

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
variable {n : ℕ}
namespace GlobalTheory.Tw
theorem _root_.solution (V : Submodule ℂ (Fin n → ℂ)) : perp (perp V) = V := by
  have h1 : V ≤ perp (perp V) := fun v hv w hw => dot_star_comm_zero (hw v hv)
  refine le_antisymm (fun z hz => ?_) h1
  obtain ⟨v, hv, u, hu, rfl⟩ := Submodule.mem_sup.1 ((sup_perp V).ge (Submodule.mem_top (x := z)))
  have : u = 0 := eq_zero_of_mem_perp hu (by simpa using sub_mem hz (h1 hv))
  simpa [this] using hv
end GlobalTheory.Tw
