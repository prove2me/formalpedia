-- Prove2me | solution 1 for GlobalTheory.CosetEuler.p_shift_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:35.514834+00:00
-- url     : https://prove2.me/submissions/1d720c57-e0fd-4cda-8642-087e947da03d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CosetEuler
variable {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)]
namespace GlobalTheory.CosetEuler
theorem _root_.solution {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} (hpe : ∀ v a, p v (e v a) = a)
    (v : ι) (g : G) : p v (shift e p v g) = 1 := by
  simp [shift, hpe]
end GlobalTheory.CosetEuler
