-- Prove2me | solution 1 for GlobalTheory.OrbitAvg.avgH_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:17:29.268494+00:00
-- url     : https://prove2.me/submissions/612d8ff1-b6c2-4fc8-b288-98051be5abca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitAvg
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)
namespace GlobalTheory.OrbitAvg
theorem _root_.solution (D : Submodule ℂ V) (hD : ∀ l ∈ L, ∀ x ∈ D, π l x ∈ D) (H : Subgroup L)
    [H.FiniteIndex] {x : V} (hx : x ∈ D) : avgH π L H x ∈ D := by
  classical
  haveI := Fintype.ofFinite (L ⧸ H)
  unfold avgH
  rw [finsum_eq_sum_of_fintype]
  exact D.smul_mem _ (D.sum_mem fun q _ => hD _ (q.out).2 x hx)
end GlobalTheory.OrbitAvg
