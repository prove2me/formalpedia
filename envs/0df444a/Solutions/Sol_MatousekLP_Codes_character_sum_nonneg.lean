-- Prove2me | solution 1 for MatousekLP.Codes.character_sum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T03:54:19.231371+00:00
-- url     : https://prove2.me/submissions/603cbeaf-9d2b-4eca-9e26-589bc357d943

import Definitions.Def_MatousekLP_Codes_Basic
import Mathlib

open Finset MatousekLP.Codes

namespace CharSumAux

lemma neg_one_pow_card_filter {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (-1 : ℤ) ^ (s.filter p).card = ∏ j ∈ s, if p j then (-1 : ℤ) else 1 := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

/-- The sign `(-1)^(u·v)` as a product over coordinates. -/
lemma sign_dot {n : ℕ} (u v : Word n) :
    (-1 : ℤ) ^ dot u v = ∏ j, if (u j = true ∧ v j = true) then (-1 : ℤ) else 1 := by
  unfold dot
  exact neg_one_pow_card_filter _ _

lemma sign_xor_bool (a b c : Bool) :
    (if (xor a b = true ∧ c = true) then (-1 : ℤ) else 1) =
      (if (a = true ∧ c = true) then (-1 : ℤ) else 1) *
        (if (b = true ∧ c = true) then (-1 : ℤ) else 1) := by
  cases a <;> cases b <;> cases c <;> simp

lemma sign_dot_xor {n : ℕ} (w w' v : Word n) :
    (-1 : ℤ) ^ dot (xorWord w w') v = (-1 : ℤ) ^ dot w v * (-1 : ℤ) ^ dot w' v := by
  rw [sign_dot, sign_dot, sign_dot, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => sign_xor_bool (w j) (w' j) (v j)

end CharSumAux

open CharSumAux in
theorem solution {n : ℕ} (C : Finset (Word n)) (v : Word n) :
    0 ≤ ∑ p ∈ C ×ˢ C, (-1 : ℤ) ^ dot (xorWord p.1 p.2) v := by
  have h : ∑ p ∈ C ×ˢ C, (-1 : ℤ) ^ dot (xorWord p.1 p.2) v
      = (∑ w ∈ C, (-1 : ℤ) ^ dot w v) * (∑ w ∈ C, (-1 : ℤ) ^ dot w v) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    exact Finset.sum_congr rfl fun p _ => sign_dot_xor _ _ _
  rw [h]
  exact mul_self_nonneg _
