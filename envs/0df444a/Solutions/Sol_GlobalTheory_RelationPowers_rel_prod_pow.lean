-- Prove2me | solution 1 for GlobalTheory.RelationPowers.rel_prod_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:18:02.892078+00:00
-- url     : https://prove2.me/submissions/2f45f764-b1c2-4005-a995-8d56c9db71b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RelProdPow
import Theorems.Thm_GlobalTheory_RelationPowers_rel_pow

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
theorem _root_.solution {G U : Type} [Monoid G] [CommMonoid U] (R : G → U → Prop) (h1 : R 1 1)
    (hmul : ∀ (x x' : G) (c c' : U), R x c → R x' c' → R (x * x') (c * c'))
    (n : ℕ) (y : Fin n → G) (c : Fin n → U) (a : Fin n → ℕ) (h : ∀ i, R (y i) (c i)) :
    R (List.prod (List.ofFn fun i : Fin n => y i ^ a i)) (∏ i : Fin n, c i ^ a i) := by
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    exact hmul _ _ _ _ (rel_pow R h1 hmul _ _ (h 0) _)
      (ih (fun i => y i.succ) (fun i => c i.succ) (fun i => a i.succ) (fun i => h i.succ))
end GlobalTheory.RelationPowers
