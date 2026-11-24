-- Prove2me | solution 1 for GlobalTheory.Chamber.IsPar.wt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:26:19.642828+00:00
-- url     : https://prove2.me/submissions/680a9869-b451-4073-a7f3-f845da8560f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_InverseChamberMap
import Theorems.Thm_GlobalTheory_Chamber_vecSpan_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace ContDiff Classical
open GlobalTheory GlobalTheory.Chamber
variable {k : ℕ}
namespace GlobalTheory.Chamber
namespace IsPar
theorem _root_.solution {P Q : Finset (SV k)} (h : IsPar P) (e : Q ⊆ P) {u : SV k} (hu : u ∈ P \ Q) : wt Q u ≠ 0 :=
  fun h0 => h.vec_notMem (mem_sdiff.1 hu).1 (vecSpan_mono (fun v hv => mem_erase.2
    ⟨fun (e' : v = u) => (mem_sdiff.1 hu).2 (e' ▸ hv), e hv⟩) (sub_eq_zero.1 h0 ▸ Submodule.starProjection_apply_mem _ _))
end IsPar
end GlobalTheory.Chamber
