-- Prove2me | solution 1 for HetExponomial.ChoiceProb.combined_terms
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T20:12:50.515281+00:00
-- url     : https://prove2.me/submissions/34c1dc23-fbe3-49e1-a94e-9615c68dea8c

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model

namespace Aux_HetExponomial_ChoiceProb_combined_terms

open HetExponomial.ChoiceProb

lemma tail_eq {n : ℕ} (u lam : Fin n → ℝ) (i : Fin n) (y c : ℝ)
    (hL : 0 < ∑ j ∈ betterThan u y, lam j) :
    tailInt u lam i y c =
      Real.exp (-(∑ j ∈ betterThan u y, lam j * (u j - u i + c))) /
        ∑ j ∈ betterThan u y, lam j := by
  set L := ∑ j ∈ betterThan u y, lam j with hLdef
  set A := ∑ j ∈ betterThan u y, lam j * (u j - u i) with hA
  have hsum : ∀ z : ℝ, ∑ j ∈ betterThan u y, lam j * (u j - u i + z) = A + L * z := by
    intro z
    simp only [hA, hLdef, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  unfold tailInt
  have hpt : ∀ z : ℝ, Real.exp (-(∑ j ∈ betterThan u y, lam j * (u j - u i + z))) =
      Real.exp (-A) * Real.exp ((-L) * z) := by
    intro z
    rw [hsum, ← Real.exp_add]
    ring_nf
  simp_rw [hpt]
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith) c, neg_div_neg_eq,
    mul_div_assoc]

end Aux_HetExponomial_ChoiceProb_combined_terms

open Aux_HetExponomial_ChoiceProb_combined_terms in
open HetExponomial.ChoiceProb in
theorem solution {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (i : Fin n) (k : Fin (levels u).card) (hk : level u k = u i)
    (w w' : Fin (levels u).card) (hw : w < k) (hw' : w'.val = w.val + 1) :
    lam i * (tailInt u lam i (level u w) (u i - level u w)
              - tailInt u lam i (level u w') (u i - level u w)) =
      -(lam i * ∑ j ∈ Finset.univ.filter (fun j => u j = level u w), lam j) /
        ((∑ j ∈ betterThan u (level u w'), lam j) * (∑ j ∈ betterThan u (level u w), lam j)) *
        Real.exp (-(∑ j ∈ betterThan u (level u w), lam j * (u j - level u w))) := by
  set x := level u w with hx
  set x' := level u w' with hx'
  have hww : w < w' := by rw [Fin.lt_iff_val_lt_val]; omega
  have hxlt : x < x' := (level u).lt_iff_lt.2 hww
  have hrange : ∀ j, ∃ t, level u t = u j := by
    intro j
    have : u j ∈ (levels u : Set ℝ) := by
      simp only [levels, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨j, rfl⟩
    rw [← Finset.range_orderEmbOfFin (levels u) rfl] at this
    exact this
  have hatt : ∀ t, ∃ j, u j = level u t := by
    intro t
    have := Finset.orderEmbOfFin_mem (levels u) rfl t
    simp only [levels, Finset.mem_image, Finset.mem_univ, true_and] at this
    exact this
  have key : ∀ j, x ≤ u j ↔ (x' ≤ u j ∨ u j = x) := by
    intro j
    constructor
    · intro h
      rcases eq_or_lt_of_le h with h1 | h1
      · exact Or.inr h1.symm
      · left
        obtain ⟨t, ht⟩ := hrange j
        rw [← ht] at h1 ⊢
        have hwt : w < t := (level u).lt_iff_lt.1 h1
        have : w' ≤ t := by rw [Fin.le_iff_val_le_val]; rw [Fin.lt_iff_val_lt_val] at hwt; omega
        exact (level u).le_iff_le.2 this
    · rintro (h | h)
      · exact hxlt.le.trans h
      · exact h.symm.le
  have hpos : ∀ y, (∃ j, u j = y) → 0 < ∑ j ∈ betterThan u y, lam j := by
    rintro y ⟨j, hj⟩
    apply Finset.sum_pos (fun j _ => hlam j)
    exact ⟨j, by simp [betterThan, hj]⟩
  have hLx := hpos x (hatt w)
  have hLx' := hpos x' (hatt w')
  set E := Finset.univ.filter (fun j => u j = x) with hE
  have hf1 : (betterThan u x).filter (fun j => x' ≤ u j) = betterThan u x' := by
    ext j
    simp only [betterThan, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨(key j).2 (Or.inl h), h⟩
  have hf2 : (betterThan u x).filter (fun j => ¬ x' ≤ u j) = E := by
    ext j
    simp only [betterThan, hE, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      rcases (key j).1 h1 with h | h
      · exact absurd h h2
      · exact h
    · intro h
      refine ⟨h.symm.le, ?_⟩
      rw [h]; exact not_le.2 hxlt
  have split : ∀ g : Fin n → ℝ, ∑ j ∈ betterThan u x, g j =
      ∑ j ∈ betterThan u x', g j + ∑ j ∈ E, g j := by
    intro g
    rw [← Finset.sum_filter_add_sum_filter_not (betterThan u x) (fun j => x' ≤ u j), hf1, hf2]
  have hLsplit := split lam
  have hEzero : ∑ j ∈ E, lam j * (u j - u i + (u i - x)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [hj]; ring
  have hexp_eq : ∑ j ∈ betterThan u x', lam j * (u j - u i + (u i - x)) =
      ∑ j ∈ betterThan u x, lam j * (u j - x) := by
    rw [split (fun j => lam j * (u j - x))]
    have : ∑ j ∈ E, lam j * (u j - x) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [hj]; ring
    rw [this, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hexp_eq2 : ∑ j ∈ betterThan u x, lam j * (u j - u i + (u i - x)) =
      ∑ j ∈ betterThan u x, lam j * (u j - x) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [tail_eq u lam i x _ hLx, tail_eq u lam i x' _ hLx', hexp_eq, hexp_eq2]
  set Ex := ∑ j ∈ betterThan u x, lam j * (u j - x)
  set Lx := ∑ j ∈ betterThan u x, lam j
  set Lx' := ∑ j ∈ betterThan u x', lam j
  set SE := ∑ j ∈ E, lam j
  have hL : Lx = Lx' + SE := hLsplit
  rw [hL] at hLx ⊢
  field_simp
  ring
