-- Prove2me | solution 1 for HarelTarjan.SymOrder.lemma3_ancestor_number
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-03T09:06:52.681657+00:00
-- url     : https://prove2.me/submissions/890d5a1e-ebe4-426f-a293-b27e01bfaabe

import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym
import Theorems.Thm_HarelTarjan_SymOrder_lemma1_height_eq_max_pow_two_dvd
import Theorems.Thm_HarelTarjan_SymOrder_lemma2_descendants_range

open HarelTarjan.SymOrder

private theorem odd_block_center (a b p : ℕ) (hp : 0 < p)
    (hpa : p ∣ a) (hna : ¬ p * 2 ∣ a)
    (hlo : a + 1 ≤ b + p) (hhi : b + 1 ≤ a + p) :
    a = (p * 2) * (b / (p * 2)) + p := by
  obtain ⟨t, rfl⟩ := hpa
  have ht : ¬ 2 ∣ t := by
    intro ht
    obtain ⟨k, hk⟩ := ht
    apply hna
    exact ⟨k, by rw [hk]; ring⟩
  have htodd : t = 2 * (t / 2) + 1 := by omega
  have ha : p * t = (t / 2) * (p * 2) + p := by
    calc
      p * t = p * (2 * (t / 2) + 1) := congrArg (p * ·) htodd
      _ = _ := by ring
  have hb : b / (p * 2) = t / 2 := Nat.div_eq_of_lt_le
    (by nlinarith [hlo]) (by nlinarith [hhi])
  rw [hb, ha]
  ring

theorem solution {d : ℕ} (v : Vertex d) (h : ℕ) (hvh : height v ≤ h)
    (hhd : h ≤ d) :
    (∃ u : Vertex d, IsAncestor u v ∧ height u = h) ∧
      ∀ u : Vertex d, IsAncestor u v → height u = h →
        sym u = 2 ^ (h + 1) * (sym v / 2 ^ (h + 1)) + 2 ^ h := by
  constructor
  · refine ⟨ancestorAtDepth v (d - h), ?_, ?_⟩
    · exact List.take_prefix _ _
    · change d - (v.1.take (d - h)).length = h
      rw [List.length_take]
      have hv := v.2
      unfold height at hvh
      omega
  · intro u huv hu
    have hi := (lemma2_descendants_range u v).mp huv
    have hd := lemma1_height_eq_max_pow_two_dvd u
    rw [hu] at hi hd
    rw [pow_succ] at hd ⊢
    exact odd_block_center (sym u) (sym v) (2 ^ h) (by positivity)
      hd.1 hd.2 hi.1 hi.2
