-- Prove2me | solution 1 for KelsoCrawford.Returns.not_dr_violates_gs
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:21:35.724779+00:00
-- url     : https://prove2.me/submissions/a55caaba-7b93-4478-8a80-a7f9c8ff8023

import Definitions.Def_KelsoCrawford_Process_Model
import Definitions.Def_KelsoCrawford_Returns_Technology
open KelsoCrawford.Returns KelsoCrawford.Process
open scoped BigOperators

private lemma force_sets {W : Type} [Fintype W] [DecidableEq W]
    (y : Finset W → ℝ) (H : ℝ) (hH : ∀ C D, y C - y D < H)
    (S U : Finset W) (r : W → ℝ)
    (hrS : ∀ i ∈ S, r i = -H) (hrU : ∀ i, i ∉ U → r i = H)
    (C : Finset W) (hC : IsDemanded y r C) : S ⊆ C ∧ C ⊆ U := by
  constructor
  · intro i hi
    by_contra hiC
    have hh := hC (insert i C)
    unfold profit at hh
    rw [Finset.sum_insert hiC, hrS i hi] at hh
    have hb := hH C (insert i C)
    linarith
  · intro i hi
    by_contra hiU
    have hh := hC (C.erase i)
    have hsum := Finset.sum_erase_add C r hi
    rw [hrU i hiU] at hsum
    unfold profit at hh
    have hb := hH C (C.erase i)
    linarith

private lemma four_sets {W : Type} [DecidableEq W] (S C : Finset W) (a b : W)
    (hS : S ⊆ C) (hU : C ⊆ insert a (insert b S)) :
    C = S ∨ C = insert a S ∨ C = insert b S ∨ C = insert a (insert b S) := by
  by_cases ha : a ∈ C <;> by_cases hb : b ∈ C
  · right; right; right; ext i; specialize @hS i; specialize @hU i
    simp only [Finset.mem_insert] at *; aesop
  · right; left; ext i; specialize @hS i; specialize @hU i
    simp only [Finset.mem_insert] at *; aesop
  · right; right; left; ext i; specialize @hS i; specialize @hU i
    simp only [Finset.mem_insert] at *; aesop
  · left; ext i; specialize @hS i; specialize @hU i
    simp only [Finset.mem_insert] at *; aesop

private lemma gs_submodular {W : Type} [Fintype W] [DecidableEq W]
    (y : Finset W → ℝ) (hgs : GrossSubstitutesOn y Set.univ)
    (S : Finset W) (a b : W) (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b) :
    y (insert a (insert b S)) + y S ≤ y (insert a S) + y (insert b S) := by
  classical
  obtain ⟨Z, _, hZ⟩ := (Finset.univ : Finset (Finset W)).exists_max_image
    (fun C => |y C|) (by simp)
  let H := 2 * |y Z| + 1
  have hH (C D : Finset W) : y C - y D < H := by
    have hC := hZ C (by simp)
    have hD := hZ D (by simp)
    dsimp [H]; linarith [le_abs_self (y C), neg_abs_le (y D)]
  let U := insert a (insert b S)
  let va := y (insert a S) - y S
  let vb := y (insert b S) - y S
  let δ := y U + y S - y (insert a S) - y (insert b S)
  by_contra hn
  have hd : 0 < δ := by dsimp [δ,U]; linarith
  let s : W → ℝ := fun i => if i ∈ S then -H else
    if i = a then va + δ/3 else if i = b then vb + δ/3 else H
  let s' : W → ℝ := fun i => if i = a then va + 2*δ else s i
  have hba : b ≠ a := hab.symm
  have haU : a ∉ insert b S := by simp [ha, hab]
  have hss : s ≤ s' := by
    intro i
    by_cases hi : i = a
    · subst i; simp [s',s,ha]; linarith
    · simp [s',hi]
  have hsS : ∀ i ∈ S, s i = -H := by intro i hi; simp [s, hi]
  have hsU : ∀ i, i ∉ U → s i = H := by
    intro i hi
    have hi' : i ≠ a ∧ i ≠ b ∧ i ∉ S := by simpa [U] using hi
    simp [s, hi'.1, hi'.2.1, hi'.2.2]
  have hs'S : ∀ i ∈ S, s' i = -H := by
    intro i hi
    have hiA : i ≠ a := by intro h; exact ha (h ▸ hi)
    simp [s',hiA,hsS i hi]
  have hs'U : ∀ i, i ∉ U → s' i = H := by
    intro i hi
    have hiA : i ≠ a := by intro h; subst i; exact hi (by simp [U])
    simp [s',hiA,hsU i hi]
  have sa : s a = va + δ/3 := by simp [s,ha]
  have sb : s b = vb + δ/3 := by simp [s,hb,hba]
  have s'a : s' a = va + 2*δ := by simp [s']
  have s'b : s' b = vb + δ/3 := by simp [s',hba,sb]
  have old_scores (C : Finset W) (hSC : S ⊆ C) (hCU : C ⊆ U) :
      profit y C s ≤ profit y U s := by
    rcases four_sets S C a b hSC hCU with rfl | rfl | rfl | rfl <;>
      simp [profit, U, Finset.sum_insert, haU, ha, hb, sa, sb] <;>
      dsimp [va,vb,δ,U] at * <;> linarith
  obtain ⟨B,_,hB⟩ := (Finset.univ : Finset (Finset W)).exists_max_image
    (fun C => profit y C s) (by simp)
  have hB' : IsDemanded y s B := fun C => hB C (by simp)
  obtain ⟨hSB,hBU⟩ := force_sets y H hH S U s hsS hsU B hB'
  have hDemand : IsDemanded y s U := fun C => (hB' C).trans (old_scores B hSB hBU)
  obtain ⟨C,hC,hkeep⟩ := hgs s (by trivial) s' (by trivial) hss U hDemand
  have hbC : b ∈ C := hkeep (by simp [U,s',hba])
  obtain ⟨hSC,hCU⟩ := force_sets y H hH S U s' hs'S hs'U C hC
  have hz := hC S
  rcases four_sets S C a b hSC hCU with rfl | rfl | rfl | rfl
  · exact hb hbC
  · have : b ∈ S := by simpa [hba] using hbC
    exact hb this
  · simp [profit, Finset.sum_insert, hb, s'b] at hz
    dsimp [vb] at hz; linarith
  · simp [profit, Finset.sum_insert, haU, hb, s'a, s'b] at hz
    dsimp [va,vb,δ,U] at *; linarith

theorem solution {W : Type} [Fintype W] [DecidableEq W] (ybar : ℕ → ℝ)
    (h19 : ∃ w : ℕ, 1 ≤ w ∧ w + 1 ≤ Fintype.card W ∧
      ybar w - ybar (w - 1) < ybar (w + 1) - ybar w) :
    ¬ KelsoCrawford.Process.GrossSubstitutesOn (fun C : Finset W => ybar C.card) Set.univ := by
  classical
  intro hgs
  obtain ⟨w, hw, hw2, hstrict⟩ := h19
  obtain ⟨U,_,hU⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset W)) (n := w+1) (by simpa using hw2)
  have hUn : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a,ha⟩ := hUn
  have hUa : (U.erase a).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha,hU]; omega)
  obtain ⟨b,hb⟩ := hUa
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  let S := (U.erase a).erase b
  have haS : a ∉ S := by simp [S]
  have hbS : b ∉ S := by simp [S]
  have hSc : S.card = w-1 := by
    dsimp [S]; rw [Finset.card_erase_of_mem hb,Finset.card_erase_of_mem ha,hU]; omega
  have hSa : (insert a S).card = w := by rw [Finset.card_insert_of_notMem haS,hSc]; omega
  have hSb : (insert b S).card = w := by rw [Finset.card_insert_of_notMem hbS,hSc]; omega
  have hSab : (insert a (insert b S)).card = w+1 := by
    rw [Finset.card_insert_of_notMem (by simp [haS,hba.symm]),hSb]
  have hh := gs_submodular (fun C : Finset W => ybar C.card) hgs S a b haS hbS hba.symm
  rw [hSab,hSa,hSb,hSc] at hh
  linarith

#print axioms solution

