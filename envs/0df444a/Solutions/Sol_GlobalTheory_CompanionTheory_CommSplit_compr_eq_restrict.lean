-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommSplit.compr_eq_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:32.275025+00:00
-- url     : https://prove2.me/submissions/4cc64021-cbea-4079-820d-cccb0f10a691

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankAdjoinLeAdd
import Theorems.Thm_GlobalTheory_CompanionTheory_CommSplit_compr_of_inv

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
theorem _root_.solution (W W' : Submodule ℂ V) (hc : IsCompl W W') (b : End ℂ V)
    (hb : ∀ w ∈ W, b w ∈ W) : compr W W' hc b = b.restrict hb := by
  refine LinearMap.ext fun w => ?_
  rw [compr_of_inv W W' hc b hb w]
  rfl
end GlobalTheory.CompanionTheory.CommSplit
