-- Prove2me | solution 1 for GlobalTheory.RelationPowers.rel_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:57:45.608056+00:00
-- url     : https://prove2.me/submissions/1e45341d-0386-4db2-be35-17b8925294d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RelProdPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RelationPowers
namespace GlobalTheory.RelationPowers
theorem _root_.solution {G U : Type} [Monoid G] [Monoid U] (R : G → U → Prop) (h1 : R 1 1)
    (hmul : ∀ (x x' : G) (c c' : U), R x c → R x' c' → R (x * x') (c * c'))
    (x : G) (c : U) (h : R x c) (k : ℕ) : R (x ^ k) (c ^ k) := by
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact hmul _ _ _ _ ih h
end GlobalTheory.RelationPowers
