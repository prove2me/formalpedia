-- Prove2me | solution 1 for GlobalTheory.ShufflePositions.pos_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:11.153047+00:00
-- url     : https://prove2.me/submissions/d831b0be-9b2c-4275-858a-a19fd173474a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CountBindWordShuffleByPositions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory
open GlobalTheory.ShufflePositions
variable {A : Type} [DecidableEq A]
omit [DecidableEq A]
namespace GlobalTheory.ShufflePositions
theorem _root_.solution {n : ℕ} (w : Fin (n + 1) → A) (p : Fin (n + 1) → Bool) :
    ((List.finRange (n + 1)).filter p).map w =
      (if p 0 then [w 0] else []) ++
        ((List.finRange n).filter fun j => p j.succ).map (fun j => w j.succ) := by
  rw [List.finRange_succ, List.filter_cons, List.filter_map]
  cases h0 : p 0
  · simp [List.map_map, Function.comp_def]
  · simp [List.map_map, Function.comp_def]
end GlobalTheory.ShufflePositions
