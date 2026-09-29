-- Prove2me | solution 1 for LovaszSchrijver.OddHole.odd_hole_deletion_contraction_valid_FRAC
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:51:29.545401+00:00
-- url     : https://prove2.me/submissions/60f03e42-027f-4fcf-b521-030e67366374

import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_StableSetCones
import Definitions.Def_LovaszSchrijver_OddHole_OddHole
import Definitions.Def_LovaszSchrijver_OddHole_DeletionContraction

namespace LovaszSchrijver.OddHole

section aux_odhdc
open Fin.NatCast Fin.CommRing

theorem aux_odhdc_pair (x : ℕ → ℝ) : ∀ n : ℕ,
    (∀ j < n, x (2 * j) + x (2 * j + 1) ≤ 1) → ∑ u ∈ Finset.range (2 * n), x u ≤ n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    push_cast
    linarith

theorem aux_odhdc_reindex {V : Type} [Fintype V] (C : Finset V) (m : ℕ) [NeZero m]
    (f : Fin m ≃ C) (s : Fin m) (b x : V → ℝ) (hb : ∀ j, j ∉ C → b j = 0) :
    ∑ j, b j * x j = ∑ u ∈ Finset.range m,
      b ((f ((u : Fin m) + s) : C) : V) * x ((f ((u : Fin m) + s) : C) : V) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ C) (fun j _ hj => by simp [hb j hj])]
  rw [← Finset.sum_coe_sort C]
  rw [← Equiv.sum_comp f]
  rw [← Equiv.sum_comp (Equiv.addRight s)]
  rw [← Fin.sum_univ_eq_sum_range
    (fun u => b ((f ((u : Fin m) + s) : C) : V) * x ((f ((u : Fin m) + s) : C) : V))]
  simp [Fin.cast_val_eq_self]

theorem aux_odhdc_main {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (C : Finset V) (hC : IsOddHole G C) (i : V) (hi : i ∈ C) :
    Valid (FRAC G) (deletion (fun j => if j ∈ C then (1 : ℝ) else 0) i)
        (((C.card : ℝ) - 1) / 2) ∧
      Valid (FRAC G) (contraction G (fun j => if j ∈ C then (1 : ℝ) else 0) i)
        (((C.card : ℝ) - 1) / 2 - 1) := by
  obtain ⟨m, hmodd, hm3, f, hf⟩ := hC
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 3 := by
    obtain ⟨j, hj⟩ := hmodd; exact ⟨j - 1, by omega⟩
  have hcard : (C.card : ℝ) = 2 * k + 3 := by
    have := Fintype.card_congr f
    simp at this
    rw [← this]; push_cast; ring
  set s : Fin (2 * k + 3) := f.symm ⟨i, hi⟩ with hs
  have hfs : ((f s : C) : V) = i := by simp [hs]
  have hadj : ∀ t : Fin (2 * k + 3), G.Adj ((f t : C) : V) ((f (t + 1) : C) : V) := by
    intro t
    rw [hf]
    left
    rw [Fin.val_add, Fin.val_one]
  have hlast : ((2 * k + 2 : ℕ) : Fin (2 * k + 3)) + s + 1 = s := by
    have h0 : ((2 * k + 3 : ℕ) : Fin (2 * k + 3)) = 0 := Fin.natCast_self _
    push_cast at h0 ⊢
    linear_combination h0
  have hstep : ∀ u : ℕ, ((u + 1 : ℕ) : Fin (2 * k + 3)) + s = ((u : ℕ) : Fin (2 * k + 3)) + s + 1 := by
    intro u; push_cast; ring
  constructor
  · intro x hx
    obtain ⟨hx0, hxe⟩ := hx
    rw [aux_odhdc_reindex C (2 * k + 3) f s _ x (by
      intro j hj; simp [deletion, Function.update_apply, hj])]
    rw [Finset.sum_range_succ']
    have hz : deletion (fun j => if j ∈ C then (1 : ℝ) else 0) i
        ((f (((0 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) = 0 := by
      simp [hfs, deletion]
    rw [hz, zero_mul, add_zero]
    have hle : ∀ u ∈ Finset.range (2 * k + 2),
        deletion (fun j => if j ∈ C then (1 : ℝ) else 0) i
          ((f (((u + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) *
          x ((f (((u + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) ≤
        x ((f (((u + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) := by
      intro u _
      have h0 := hx0 ((f (((u + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V)
      simp only [deletion, Function.update_apply]
      split_ifs <;> nlinarith
    refine (Finset.sum_le_sum hle).trans ?_
    have hp := aux_odhdc_pair (fun u => x ((f (((u + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V))
      (k + 1) (by
        intro j _
        rw [hstep (2 * j + 1)]
        exact hxe _ _ (hadj _))
    rw [show 2 * (k + 1) = 2 * k + 2 by ring] at hp
    rw [hcard]
    push_cast at hp ⊢
    linarith
  · intro x hx
    obtain ⟨hx0, hxe⟩ := hx
    set b := contraction G (fun j => if j ∈ C then (1 : ℝ) else 0) i with hb
    rw [aux_odhdc_reindex C (2 * k + 3) f s b x (by intro j hj; simp [hb, contraction, hj])]
    have hbi : ∀ t : Fin (2 * k + 3),
        ((f t : C) : V) = i ∨ G.Adj i ((f t : C) : V) → b ((f t : C) : V) = 0 := by
      intro t ht; simp [hb, contraction, ht]
    have e1 : b ((f (((2 * k + 2 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) = 0 :=
      hbi _ (Or.inr (by
        have := hadj (((2 * k + 2 : ℕ) : Fin (2 * k + 3)) + s)
        rw [hlast, hfs] at this
        exact this.symm))
    have e2 : b ((f (((0 + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) = 0 :=
      hbi _ (Or.inr (by
        rw [hstep 0]
        simp only [Nat.cast_zero, zero_add]
        rw [← hfs]
        exact hadj s))
    have e3 : b ((f (((0 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) = 0 :=
      hbi _ (Or.inl (by simp [hfs]))
    rw [Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
    rw [e1, e2, e3]
    simp only [zero_mul, add_zero]
    have hle : ∀ u ∈ Finset.range (2 * k),
        b ((f (((u + 1 + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) *
          x ((f (((u + 1 + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) ≤
        x ((f (((u + 1 + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V) := by
      intro u _
      have h0 := hx0 ((f (((u + 1 + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V)
      simp only [hb, contraction]
      split_ifs <;> nlinarith
    refine (Finset.sum_le_sum hle).trans ?_
    have hp := aux_odhdc_pair
      (fun u => x ((f (((u + 1 + 1 : ℕ) : Fin (2 * k + 3)) + s) : C) : V)) k (by
        intro j _
        rw [hstep (2 * j + 1 + 1)]
        exact hxe _ _ (hadj _))
    rw [hcard]
    push_cast at hp ⊢
    linarith

end aux_odhdc

end LovaszSchrijver.OddHole

open LovaszSchrijver.OddHole

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (C : Finset V) (hC : IsOddHole G C) (i : V) (hi : i ∈ C) :
    Valid (FRAC G) (deletion (fun j => if j ∈ C then (1 : ℝ) else 0) i)
        (((C.card : ℝ) - 1) / 2) ∧
      Valid (FRAC G) (contraction G (fun j => if j ∈ C then (1 : ℝ) else 0) i)
        (((C.card : ℝ) - 1) / 2 - 1) :=
  aux_odhdc_main G hG C hC i hi
