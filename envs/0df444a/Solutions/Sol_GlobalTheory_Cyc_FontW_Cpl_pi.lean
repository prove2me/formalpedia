-- Prove2me | solution 1 for GlobalTheory.Cyc.FontW.Cpl.pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:52.55536+00:00
-- url     : https://prove2.me/submissions/4974c9ba-0325-4816-aeda-eac050e27e4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight
import Theorems.Thm_GlobalTheory_Cyc_FontW_mem_Dv
import Theorems.Thm_GlobalTheory_Cyc_FontW_Dv_map

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
namespace Cpl
theorem _root_.solution {l : ℕ} {M : Type*} [AddCommGroup M] (ι : Type*) (h : Cpl l M) : Cpl l (ι → M) := by
  refine ⟨fun x hx => funext fun i => ?_, fun f hf => ?_⟩
  · exact h.1 _ fun r => Dv_map (Pi.evalAddMonoidHom (fun _ : ι => M) i) (hx r)
  · choose L hL using fun i => h.2 (fun r => f r i) fun r =>
      Dv_map (Pi.evalAddMonoidHom (fun _ : ι => M) i) (hf r)
    refine ⟨L, fun r => ?_⟩
    choose y hy using fun i => mem_Dv.1 (hL i r)
    exact mem_Dv.2 ⟨y, funext hy⟩
end Cpl
end GlobalTheory.Cyc.FontW
