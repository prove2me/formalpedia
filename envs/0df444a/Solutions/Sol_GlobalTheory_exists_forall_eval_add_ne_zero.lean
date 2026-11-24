-- Prove2me | solution 1 for GlobalTheory.exists_forall_eval_add_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:42:31.287029+00:00
-- url     : https://prove2.me/submissions/9b597558-95a6-4b8f-84a9-bc73b472508e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_InfinitePowCharEqOneOfAdditiveFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k : Type} [Field k] [Infinite k] {Q : Polynomial k}
    (hQ : Q ≠ 0) (S : Finset k) : ∃ β : k, ∀ c ∈ S, Q.eval (c + β) ≠ 0 := by
  classical
  obtain ⟨β, hβ⟩ := Infinite.exists_notMem_finset
    ((S ×ˢ Q.roots.toFinset).image (fun x : k × k => x.2 - x.1))
  refine ⟨β, fun c hc h => hβ ?_⟩
  refine Finset.mem_image.2 ⟨(c, c + β), ?_, by simp⟩
  simp [hc, hQ, h]
end GlobalTheory
