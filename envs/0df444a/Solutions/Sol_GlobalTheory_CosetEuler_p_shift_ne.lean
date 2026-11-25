-- Prove2me | solution 1 for GlobalTheory.CosetEuler.p_shift_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:49.951477+00:00
-- url     : https://prove2.me/submissions/fe8bd9a9-2527-4427-9dbf-9fda68ea96b4

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
theorem _root_.solution {e : ∀ v, L v →* G} {p : ∀ v, G →* L v}
    (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1) {u v : ι} (h : u ≠ v) (g : G) :
    p u (shift e p v g) = p u g := by
  simp [shift, hpe' u v h]
end GlobalTheory.CosetEuler
