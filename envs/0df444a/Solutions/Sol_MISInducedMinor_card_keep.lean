-- Prove2me | solution 1 for MISInducedMinor.card_keep
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:42:02.522677+00:00
-- url     : https://prove2.me/submissions/295c7d04-4648-44c6-bcf1-42755f58fc63

import Definitions.Def_MISInducedMinor_GF
import Definitions.Def_MISInducedMinor_addTerm

set_option autoImplicit false

namespace Aux_MIScardkeep

open MISInducedMinor

theorem edge_lt {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (e : Fin n × Fin n)
    (he : e ∈ edgeList F) : e.1 < e.2 := by
  unfold edgeList at he
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and] at he
  obtain ⟨a, b, hbe⟩ := he
  split_ifs at hbe with h
  · simp only [Option.some.injEq] at hbe
    subst hbe
    exact h.1

theorem card_fin_Ico (m lo hi : ℕ) (h : hi ≤ m) :
    (Finset.univ.filter (fun c : Fin m => lo ≤ c.val ∧ c.val < hi)).card = hi - lo := by
  rw [← Finset.card_map Fin.valEmbedding, ← Nat.card_Ico lo hi]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply, Finset.mem_Ico]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact hc
  · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩

theorem cnt (m lo hi : ℕ) (P : Fin m → Prop) [DecidablePred P]
    (hP : ∀ c : Fin m, P c ↔ lo ≤ c.val ∧ c.val < hi) (h : hi ≤ m) :
    (Finset.univ.filter P).card = hi - lo := by
  rw [Finset.filter_congr (fun c _ => hP c)]
  exact card_fin_Ico m lo hi h

theorem row_count (n a b : ℕ) (hab : a < b) (hb : b < n) (s : Fin 2) :
    (∑ c : Fin (2 * n - 1), ∑ l : Fin 2,
      (if ((c.val = 2 * a ∧ l = s) ∨ (c.val = 2 * b ∧ l ≠ s) ∨
        (2 * a < c.val ∧ c.val < 2 * b)) then 1 else 0)) = 4 * (b - a) := by
  rw [Finset.sum_comm, Fin.sum_univ_two, Finset.sum_boole, Finset.sum_boole]
  fin_cases s
  · rw [cnt (2 * n - 1) (2 * a) (2 * b) _ (fun c => by simp; omega) (by omega),
      cnt (2 * n - 1) (2 * a + 1) (2 * b + 1) _ (fun c => by simp; omega) (by omega)]
    simp only [Nat.cast_id]
    omega
  · rw [cnt (2 * n - 1) (2 * a + 1) (2 * b + 1) _ (fun c => by simp; omega) (by omega),
      cnt (2 * n - 1) (2 * a) (2 * b) _ (fun c => by simp; omega) (by omega)]
    simp only [Nat.cast_id]
    omega

theorem range_double (g : ℕ → ℕ) (L : ℕ) :
    ∑ r ∈ Finset.range (2 * L), g (r / 2) = 2 * ∑ t ∈ Finset.range L, g t := by
  induction L with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    rw [show (2 * k + 1) / 2 = k by omega, show (2 * k) / 2 = k by omega]
    ring

def half {L : ℕ} (r : Fin (2 * L)) : Fin L := ⟨r.val / 2, by omega⟩
def par {L : ℕ} (r : Fin (2 * L)) : Fin 2 := ⟨r.val % 2, by omega⟩

end Aux_MIScardkeep

open MISInducedMinor Aux_MIScardkeep in
theorem solution (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    Nat.card ↥(keep F) = 8 * addTerm F := by
  classical
  set L := (edgeList F).length with hL
  have hlt : ∀ t : Fin L, ((edgeList F).get t).1.val < ((edgeList F).get t).2.val :=
    fun t => edge_lt F _ (List.get_mem _ _)
  have hmem : ∀ (r : Fin (2 * L)) (c : Fin (2 * n - 1)) (l : Fin 2),
      (r, c, l) ∈ keep F ↔
        ((c.val = 2 * ((edgeList F).get (half r)).1.val ∧
            l = par r) ∨
          (c.val = 2 * ((edgeList F).get (half r)).2.val ∧
            l ≠ par r) ∨
          (2 * ((edgeList F).get (half r)).1.val < c.val ∧
            c.val < 2 * ((edgeList F).get (half r)).2.val)) := by
    intro r c l
    unfold keep
    constructor
    · rintro ⟨t, s, hr, hq⟩
      have hr' : r.val = 2 * t.val + s.val := hr
      have hs2 := s.2
      have ht : t = half r := Fin.ext (by simp only [half]; omega)
      have hs : s = par r := Fin.ext (by simp only [par]; omega)
      subst ht hs
      exact hq
    · intro hq
      refine ⟨half r, par r, ?_, hq⟩
      show r.val = 2 * (r.val / 2) + r.val % 2
      omega
  have hrow : ∀ r : Fin (2 * L),
      (∑ c : Fin (2 * n - 1), ∑ l : Fin 2, (if (r, c, l) ∈ keep F then 1 else 0)) =
        4 * (((edgeList F).get (half r)).2.val -
          ((edgeList F).get (half r)).1.val) := by
    intro r
    simp only [hmem]
    exact row_count n _ _ (hlt _) (((edgeList F).get (half r)).2.2) _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun r _ => hrow r)]
  let g : ℕ → ℕ := fun t => if h : t < L then
    4 * (((edgeList F).get ⟨t, h⟩).2.val - ((edgeList F).get ⟨t, h⟩).1.val) else 0
  have h1 : (∑ r : Fin (2 * L), 4 * (((edgeList F).get (half r)).2.val -
          ((edgeList F).get (half r)).1.val)) =
      ∑ r : Fin (2 * L), g (r.val / 2) := by
    apply Finset.sum_congr rfl
    intro r _
    have : r.val / 2 < L := by omega
    simp only [g, dif_pos this, half]
  rw [h1, Fin.sum_univ_eq_sum_range (fun r => g (r / 2)), range_double,
    ← Fin.sum_univ_eq_sum_range]
  have h2 : (∑ t : Fin L, g t.val) =
      ∑ t : Fin L, 4 * (((edgeList F).get t).2.val - ((edgeList F).get t).1.val) := by
    apply Finset.sum_congr rfl
    intro t _
    simp only [g, dif_pos t.2, Fin.eta]
  rw [h2, ← Finset.mul_sum]
  unfold addTerm
  have h3 : (∑ t : Fin L, (((edgeList F).get t).2.val - ((edgeList F).get t).1.val)) =
      ((edgeList F).map fun e => e.2.val - e.1.val).sum := by
    rw [← Fin.sum_univ_fun_getElem]
    rfl
  rw [h3]
  ring
