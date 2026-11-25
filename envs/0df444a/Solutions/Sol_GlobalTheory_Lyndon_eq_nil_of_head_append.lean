-- Prove2me | solution 1 for GlobalTheory.Lyndon.eq_nil_of_head_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:44:21.501839+00:00
-- url     : https://prove2.me/submissions/f3e46c6a-659b-40ec-a839-0cc6e249f600

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_lt_of_isLyndon
import Theorems.Thm_GlobalTheory_Lyndon_le_append
import Theorems.Thm_GlobalTheory_Lyndon_exists_suffix_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Shuffle
open GlobalTheory.Lyndon
variable {A : Type} [LinearOrder A]
namespace GlobalTheory.Lyndon
theorem _root_.solution {l t r : List A} {L : List (List A)} (hL : IsFactors (l :: L))
    (hp : IsLyndon (l ++ t)) (e : L.flatten = t ++ r) : t = [] := by
  by_contra ht
  obtain ⟨s, q, h1, h2, h3⟩ :=
    exists_suffix_le l L (List.pairwise_cons.1 hL.2).1 t r ht e.symm
  have h4 : l ++ t < q :=
    lt_of_isLyndon hp (u := l ++ s) (by simp [(hL.1 l (by simp)).1]) h1 (by simp [h2])
  exact absurd (h4.trans_le (h3.trans (le_append l t))) (lt_irrefl _)
end GlobalTheory.Lyndon
