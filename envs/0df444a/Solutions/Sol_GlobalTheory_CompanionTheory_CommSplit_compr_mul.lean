-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommSplit.compr_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:24:28.664175+00:00
-- url     : https://prove2.me/submissions/4fed4d42-b7d6-402b-b67c-0090d9b9223c

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
theorem _root_.solution (W W' : Submodule ℂ V) (hc : IsCompl W W') (b c : End ℂ V)
    (hcW : ∀ w ∈ W, c w ∈ W) :
    compr W W' hc (b * c) = compr W W' hc b * compr W W' hc c := by
  refine LinearMap.ext fun w => ?_
  rw [Module.End.mul_apply, compr_of_inv W W' hc c hcW w]
  rfl
end GlobalTheory.CompanionTheory.CommSplit
