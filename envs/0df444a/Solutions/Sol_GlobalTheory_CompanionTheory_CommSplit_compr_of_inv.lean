-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommSplit.compr_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:16.713331+00:00
-- url     : https://prove2.me/submissions/3b378f0e-cb95-45ab-bd75-622850ee69ac

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankAdjoinLeAdd

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
    (hb : ∀ w ∈ W, b w ∈ W) (w : W) : compr W W' hc b w = ⟨b w, hb w w.2⟩ := by
  show W.linearProjOfIsCompl W' hc (b w) = _
  exact Submodule.linearProjOfIsCompl_apply_left hc ⟨b w, hb w w.2⟩
end GlobalTheory.CompanionTheory.CommSplit
