-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommSplit.compr_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:24:26.007576+00:00
-- url     : https://prove2.me/submissions/54e8aedd-8ac2-4017-86cc-19e986215c82

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankAdjoinLeAdd
import Theorems.Thm_GlobalTheory_CompanionTheory_CommSplit_compr_eq_restrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommSplit
open Module
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CommSplit
theorem _root_.solution (W W' : Submodule ℂ V) (hc : IsCompl W W') (t : ℂ) :
    compr W W' hc (algebraMap ℂ (End ℂ V) t) = algebraMap ℂ (End ℂ W) t := by
  have hb : ∀ w ∈ W, algebraMap ℂ (End ℂ V) t w ∈ W := fun w hw => by
    rw [Module.algebraMap_end_apply]
    exact W.smul_mem t hw
  rw [compr_eq_restrict W W' hc _ hb]
  ext w
  simp [Module.algebraMap_end_apply]
end GlobalTheory.CompanionTheory.CommSplit
