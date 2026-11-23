-- Prove2me | solution 1 for GlobalTheory.Cyc.FontW.Cpl.equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:53.87412+00:00
-- url     : https://prove2.me/submissions/9ce00aa4-d94a-498f-b740-2abea5b8649a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight
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
theorem _root_.solution {l : ℕ} {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] (e : M ≃+ M')
    (h : Cpl l M') : Cpl l M := by
  refine ⟨fun x hx => ?_, fun f hf => ?_⟩
  · exact e.injective (by rw [map_zero]; exact h.1 _ fun r => Dv_map e (hx r))
  · obtain ⟨L, hL⟩ := h.2 (fun r => e (f r)) fun r => by
      rw [← map_sub]; exact Dv_map e (hf r)
    refine ⟨e.symm L, fun r => ?_⟩
    have := Dv_map e.symm (hL r)
    rwa [map_sub, e.symm_apply_apply] at this
end Cpl
end GlobalTheory.Cyc.FontW
