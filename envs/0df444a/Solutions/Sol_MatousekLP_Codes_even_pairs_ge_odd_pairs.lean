-- Prove2me | solution 1 for MatousekLP.Codes.even_pairs_ge_odd_pairs
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T03:54:53.47831+00:00
-- url     : https://prove2.me/submissions/4f5fdc69-8142-4306-b7e1-46dca13df22f

import Definitions.Def_MatousekLP_Codes_Basic
import Mathlib

open Finset MatousekLP.Codes

namespace EvenOddAux

lemma neg_one_pow_card_filter {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (-1 : ℤ) ^ (s.filter p).card = ∏ j ∈ s, if p j then (-1 : ℤ) else 1 := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

/-- `(-1)^(restricted distance)` factors through the two words. -/
lemma sign_restrictedDist {n : ℕ} (I : Finset (Fin n)) (w w' : Word n) :
    (-1 : ℤ) ^ restrictedDist I w w' =
      (∏ i ∈ I, if w i = true then (-1 : ℤ) else 1) *
        (∏ i ∈ I, if w' i = true then (-1 : ℤ) else 1) := by
  unfold restrictedDist
  rw [neg_one_pow_card_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases w i <;> cases w' i <;> simp

end EvenOddAux

open EvenOddAux in
theorem solution {n : ℕ} (I : Finset (Fin n)) (C : Finset (Word n)) :
    #{p ∈ C ×ˢ C | Odd (restrictedDist I p.1 p.2)} ≤
      #{p ∈ C ×ˢ C | Even (restrictedDist I p.1 p.2)} := by
  set f : Word n → ℤ := fun w => ∏ i ∈ I, if w i = true then (-1 : ℤ) else 1
  -- the signed count is a perfect square
  have hsq : ∑ p ∈ C ×ˢ C, (-1 : ℤ) ^ restrictedDist I p.1 p.2 = (∑ w ∈ C, f w) * (∑ w ∈ C, f w) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    exact Finset.sum_congr rfl fun p _ => sign_restrictedDist I _ _
  -- the signed count is (#even) - (#odd)
  have hsplit : ∑ p ∈ C ×ˢ C, (-1 : ℤ) ^ restrictedDist I p.1 p.2 =
      (#{p ∈ C ×ˢ C | Even (restrictedDist I p.1 p.2)} : ℤ) -
        #{p ∈ C ×ˢ C | Odd (restrictedDist I p.1 p.2)} := by
    have h1 : ∀ p ∈ C ×ˢ C, (-1 : ℤ) ^ restrictedDist I p.1 p.2 =
        if Even (restrictedDist I p.1 p.2) then 1 else -1 := by
      intro p _
      split_ifs with h
      · exact h.neg_one_pow
      · exact (Nat.not_even_iff_odd.mp h).neg_one_pow
    rw [Finset.sum_congr rfl h1, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    simp only [nsmul_eq_mul, mul_one, mul_neg]
    have : (C ×ˢ C).filter (fun p => ¬ Even (restrictedDist I p.1 p.2)) =
        (C ×ˢ C).filter (fun p => Odd (restrictedDist I p.1 p.2)) :=
      Finset.filter_congr fun p _ => Nat.not_even_iff_odd
    rw [this]
    ring
  have hnn : (0 : ℤ) ≤ (#{p ∈ C ×ˢ C | Even (restrictedDist I p.1 p.2)} : ℤ) -
      #{p ∈ C ×ˢ C | Odd (restrictedDist I p.1 p.2)} := by
    rw [← hsplit, hsq]; exact mul_self_nonneg _
  exact_mod_cast sub_nonneg.mp hnn
