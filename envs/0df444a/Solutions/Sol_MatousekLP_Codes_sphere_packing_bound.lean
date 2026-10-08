-- Prove2me | solution 1 for MatousekLP.Codes.sphere_packing_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T04:38:07.502128+00:00
-- url     : https://prove2.me/submissions/03780deb-94ee-490a-bd2d-327e0de31fb9

import Definitions.Def_MatousekLP_Codes_Basic
import Mathlib

open Finset MatousekLP.Codes

namespace SpherePackingAux

/-- The Hamming ball of radius `r` around `c`. -/
def ball {n : ℕ} (c : Word n) (r : ℕ) : Finset (Word n) :=
  univ.filter fun w => hammingDist c w ≤ r

/-- Flip the coordinates of `c` in `S`. -/
def flip {n : ℕ} (c : Word n) (S : Finset (Fin n)) : Word n :=
  fun i => if i ∈ S then !c i else c i

lemma diffSet_flip {n : ℕ} (c : Word n) (S : Finset (Fin n)) :
    (univ.filter fun i => c i ≠ flip c S i) = S := by
  ext i; by_cases h : i ∈ S <;> simp [flip, h]

lemma flip_diffSet {n : ℕ} (c w : Word n) : flip c (univ.filter fun i => c i ≠ w i) = w := by
  funext i
  by_cases h : c i = w i
  · simp [flip, h]
  · simp only [flip, mem_filter, mem_univ, true_and, h, not_false_eq_true, if_true]
    cases hc : c i <;> cases hw : w i <;> simp_all

lemma card_ball {n : ℕ} (c : Word n) (r : ℕ) :
    (ball c r).card = ∑ i ∈ range (r + 1), n.choose i := by
  classical
  -- `ball c r` is in bijection with the subsets of `Fin n` of size at most `r`
  have hbij : (ball c r).card = (univ.filter fun S : Finset (Fin n) => S.card ≤ r).card := by
    refine Finset.card_nbij' (fun w => univ.filter fun i => c i ≠ w i) (flip c) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [ball, mem_filter, mem_univ, true_and, coe_filter, Set.mem_setOf_eq] at hw ⊢
      simpa [hammingDist] using hw
    · intro S hS
      simp only [ball, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hS ⊢
      have : hammingDist c (flip c S) = S.card := by
        rw [hammingDist, diffSet_flip]
      omega
    · intro w _; exact flip_diffSet c w
    · intro S _; exact diffSet_flip c S
  rw [hbij]
  have hsplit : (univ.filter fun S : Finset (Fin n) => S.card ≤ r) =
      (range (r + 1)).biUnion fun i => powersetCard i (univ : Finset (Fin n)) := by
    ext S; simp [mem_powersetCard, Nat.lt_succ_iff]
  rw [hsplit, card_biUnion]
  · exact sum_congr rfl fun i _ => by rw [card_powersetCard, card_univ, Fintype.card_fin]
  · intro i _ j _ hij
    exact disjoint_left.mpr fun S hSi hSj => hij ((mem_powersetCard.mp hSi).2.symm.trans
      (mem_powersetCard.mp hSj).2)

end SpherePackingAux

open SpherePackingAux in
theorem solution (n r : ℕ) :
    A n (2 * r + 1) ≤ 2 ^ n / ∑ i ∈ Finset.range (r + 1), n.choose i := by
  classical
  set V := ∑ i ∈ Finset.range (r + 1), n.choose i
  have hV : 0 < V := Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨0, by simp, by simp⟩
  unfold A
  apply Finset.sup_le
  intro C hC
  have hdist := (Finset.mem_filter.mp hC).2
  rw [Nat.le_div_iff_mul_le hV]
  -- the balls around codewords are pairwise disjoint
  have hdisj : (C : Set (Word n)).PairwiseDisjoint fun c => ball c r := by
    intro c hc c' hc' hne
    refine disjoint_left.mpr fun w hw hw' => ?_
    simp only [ball, mem_filter, mem_univ, true_and] at hw hw'
    have := hdist c hc c' hc' hne
    have htri := hammingDist_triangle c w c'
    rw [hammingDist_comm w c'] at htri
    omega
  calc C.card * V = ∑ c ∈ C, (ball c r).card := by
        rw [Finset.sum_congr rfl fun c _ => card_ball c r, Finset.sum_const, smul_eq_mul]
    _ = (C.biUnion fun c => ball c r).card := (card_biUnion hdisj).symm
    _ ≤ (univ : Finset (Word n)).card := card_le_univ _
    _ = 2 ^ n := by simp
