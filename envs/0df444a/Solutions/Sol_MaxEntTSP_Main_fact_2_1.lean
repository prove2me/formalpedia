-- Prove2me | solution 1 for MaxEntTSP.Main.fact_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:21:31.955004+00:00
-- url     : https://prove2.me/submissions/4f95799d-537f-4d85-8fc1-129cd981bc6c

import Mathlib
import Definitions.Def_MaxEntTSP_Main_Cuts

open MaxEntTSP.Main MetricTSP Finset

namespace Fact21Aux

lemma double_sum_eq_two_sym2 {m : ℕ} (f : Fin m → Fin m → ℝ)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) =
      2 * ∑ e ∈ (univ : Finset (Sym2 (Fin m))).filter (fun e => ¬ e.IsDiag),
        Sym2.lift ⟨f, hs⟩ e := by
  rw [← Finset.sum_product']
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : Fin m × Fin m => s(p.1, p.2))
    (t := (univ : Finset (Sym2 (Fin m)))) (fun _ _ => mem_univ _)]
  rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not univ (fun e : Sym2 (Fin m) => e.IsDiag)]
  have h1 : ∀ e ∈ (univ : Finset (Sym2 (Fin m))).filter (fun e => e.IsDiag),
      (∑ p ∈ (univ ×ˢ univ : Finset (Fin m × Fin m)) with s(p.1, p.2) = e, f p.1 p.2) = 0 := by
    intro e he
    rw [mem_filter] at he
    apply Finset.sum_eq_zero
    intro p hp
    rw [mem_filter] at hp
    have : (s(p.1, p.2)).IsDiag := hp.2 ▸ he.2
    obtain ⟨a, b⟩ := p
    rw [Sym2.mk_isDiag_iff] at this
    simp only at this; rw [this, hd]
  rw [Finset.sum_eq_zero h1, zero_add]
  apply Finset.sum_congr rfl
  intro e he
  rw [mem_filter] at he
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa [Sym2.mk_isDiag_iff] using he.2
    have hfib : ((univ ×ˢ univ : Finset (Fin m × Fin m)).filter
        (fun p => s(p.1, p.2) = s(a, b))) = {(a, b), (b, a)} := by
      ext ⟨p, q⟩
      simp only [mem_filter, mem_product, mem_univ, true_and, mem_insert, mem_singleton,
        Sym2.eq_iff, Prod.mk.injEq]
    rw [hfib, Finset.sum_pair (by simp [Prod.mk.injEq, hab])]
    simp only [Sym2.lift_mk]
    rw [hs b a]
    ring

lemma pairCost_mk {m : ℕ} (c : Fin m → Fin m → ℝ) (hs : ∀ i j, c i j = c j i)
    (i j : Fin m) : pairCost c s(i, j) = c i j := by
  simp only [pairCost, Sym2.lift_mk]
  rw [hs j i]; ring

lemma pairCost_nonneg {m : ℕ} (x : Fin m → Fin m → ℝ) (hs : ∀ i j, x i j = x j i)
    (hx0 : ∀ i j, 0 ≤ x i j) (e : Sym2 (Fin m)) : 0 ≤ pairCost x e := by
  induction e using Sym2.ind with
  | h i j => rw [pairCost_mk x hs]; exact hx0 i j

open Classical in
/-- Mass of the off-diagonal pairs inside `S` is half the internal double sum. -/
lemma inside_mass {m : ℕ} (x : Fin m → Fin m → ℝ) (hs : ∀ i j, x i j = x j i)
    (hd : ∀ i, x i i = 0) (S : Finset (Fin m)) :
    (∑ e ∈ (univ : Finset (Sym2 (Fin m))).filter (fun e => ¬ e.IsDiag ∧ edgeInside S e),
        pairCost x e) = (1 / 2) * ∑ i ∈ S, ∑ j ∈ S, x i j := by
  classical
  set f : Fin m → Fin m → ℝ := fun i j => if i ∈ S ∧ j ∈ S then x i j else 0 with hf
  have hfs : ∀ i j, f i j = f j i := by
    intro i j; simp only [hf]; rw [hs]; by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj]
  have hfd : ∀ i, f i i = 0 := by intro i; simp [hf, hd]
  have h1 : (∑ i ∈ S, ∑ j ∈ S, x i j) = ∑ i, ∑ j, f i j := by
    simp only [hf]
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => i ∈ S)]
    rw [Finset.sum_eq_zero (s := univ.filter (fun i => ¬ i ∈ S)), add_zero]
    · rw [Finset.filter_mem_eq_inter, univ_inter]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter_add_sum_filter_not univ (fun j => j ∈ S)]
      rw [Finset.sum_eq_zero (s := univ.filter (fun j => ¬ j ∈ S)), add_zero]
      · rw [Finset.filter_mem_eq_inter, univ_inter]
        apply Finset.sum_congr rfl
        intro j hj; rw [if_pos ⟨hi, hj⟩]
      · intro j hj; rw [mem_filter] at hj; rw [if_neg (fun h => hj.2 h.2)]
    · intro i hi
      rw [mem_filter] at hi
      apply Finset.sum_eq_zero; intro j _; rw [if_neg (fun h => hi.2 h.1)]
  rw [h1, double_sum_eq_two_sym2 f hfs hfd, ← mul_assoc]
  norm_num
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  induction e using Sym2.ind with
  | h i j =>
    simp only [Sym2.lift_mk, hf]
    have hin : edgeInside S s(i, j) ↔ (i ∈ S ∧ j ∈ S) := by
      constructor
      · rintro ⟨a, b, hab, ha, hb⟩
        rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨ha, hb⟩
        · exact ⟨hb, ha⟩
      · rintro ⟨hi, hj⟩; exact ⟨i, j, rfl, hi, hj⟩
    by_cases hdg : s(i, j).IsDiag
    · have hdg' := hdg
      rw [Sym2.mk_isDiag_iff] at hdg'
      subst hdg'
      simp [hd]
    · simp only [hdg, not_false_eq_true, true_and, if_true]
      by_cases h : i ∈ S ∧ j ∈ S
      · rw [if_pos (hin.mpr h), if_pos h, pairCost_mk x hs]
      · rw [if_neg (fun h' => h (hin.mp h')), if_neg h]

end Fact21Aux

open Fact21Aux in
theorem solution (m : ℕ) (hm : 3 ≤ m) (x : Fin m → Fin m → ℝ)
    (hx : IsHeldKarp x) (a b : Fin m) (hab : a ≠ b) (he0 : x a b = 1) :
    let E := lpSupport x a b
    edgeMass x E = (m : ℝ) - 1 ∧
    (∀ S : Finset (Fin m), S.Nonempty →
      edgeMass x (internalEdges E S) ≤ (S.card : ℝ) - 1) ∧
    (∀ e ∈ E, 0 ≤ pairCost x e) := by
  classical
  intro E
  obtain ⟨hxs, hxd, hx0, hx1, hdeg, hcut⟩ := hx
  have hpe0 : pairCost x s(a, b) = 1 := by rw [pairCost_mk x hxs, he0]
  have he0d : ¬ (s(a, b)).IsDiag := by rw [Sym2.mk_isDiag_iff]; exact hab
  -- internal double sum
  have hint : ∀ S : Finset (Fin m),
      (∑ i ∈ S, ∑ j ∈ S, x i j) = 2 * S.card - ∑ i ∈ S, ∑ j ∈ Sᶜ, x i j := by
    intro S
    have : ∀ i, ∑ j ∈ S, x i j = 2 - ∑ j ∈ Sᶜ, x i j := by
      intro i; rw [← hdeg i, ← Finset.sum_add_sum_compl S]; ring
    simp_rw [this, Finset.sum_sub_distrib]
    simp [mul_comm]
  -- mass of all internal off-diagonal pairs except e₀ bounds E's internal mass
  have hsub : ∀ S : Finset (Fin m), edgeMass x (internalEdges E S) ≤
      (∑ e ∈ (univ : Finset (Sym2 (Fin m))).filter (fun e => ¬ e.IsDiag ∧ edgeInside S e),
        pairCost x e) - (if edgeInside S s(a, b) then 1 else 0) := by
    intro S
    unfold edgeMass internalEdges
    by_cases hin : edgeInside S s(a, b)
    · rw [if_pos hin]
      have hmem : s(a, b) ∈ (univ : Finset (Sym2 (Fin m))).filter
          (fun e => ¬ e.IsDiag ∧ edgeInside S e) := by
        simp [he0d, hin]
      rw [← Finset.add_sum_erase _ _ hmem, hpe0, add_sub_cancel_left]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        simp only [E, lpSupport, mem_filter, mem_univ, true_and] at he
        simp only [mem_erase, mem_filter, mem_univ, true_and]
        exact ⟨he.1.2.1, he.1.1, he.2⟩
      · intro e _ _; exact pairCost_nonneg x hxs hx0 e
    · rw [if_neg hin, sub_zero]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        simp only [E, lpSupport, mem_filter, mem_univ, true_and] at he
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨he.1.1, he.2⟩
      · intro e _ _; exact pairCost_nonneg x hxs hx0 e
  refine ⟨?_, ?_, ?_⟩
  · -- total mass
    have hall : (∑ e ∈ (univ : Finset (Sym2 (Fin m))).filter
        (fun e => ¬ e.IsDiag ∧ edgeInside univ e), pairCost x e) = m := by
      rw [inside_mass x hxs hxd univ]
      simp only [hdeg, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hin : edgeInside (univ : Finset (Fin m)) s(a, b) := ⟨a, b, rfl, mem_univ _, mem_univ _⟩
    have hmem : s(a, b) ∈ (univ : Finset (Sym2 (Fin m))).filter
        (fun e => ¬ e.IsDiag ∧ edgeInside univ e) := by
      simp [he0d, hin]
    rw [← Finset.add_sum_erase _ _ hmem, hpe0] at hall
    unfold edgeMass
    have : ∑ e ∈ E, pairCost x e = ∑ e ∈ ((univ : Finset (Sym2 (Fin m))).filter
        (fun e => ¬ e.IsDiag ∧ edgeInside univ e)).erase s(a, b), pairCost x e := by
      apply Finset.sum_subset
      · intro e he
        simp only [E, lpSupport, mem_filter, mem_univ, true_and] at he
        simp only [mem_erase, mem_filter, mem_univ, true_and]
        refine ⟨he.2.1, he.1, ?_⟩
        induction e using Sym2.ind with
        | h i j => exact ⟨i, j, rfl, mem_univ _, mem_univ _⟩
      · intro e he hne
        simp only [mem_erase, mem_filter, mem_univ, true_and] at he
        simp only [E, lpSupport, mem_filter, mem_univ, true_and, not_and, not_lt] at hne
        exact le_antisymm (hne he.2.1 he.1) (pairCost_nonneg x hxs hx0 e)
    rw [this]; linarith
  · intro S hS
    have h1 := hsub S
    rw [inside_mass x hxs hxd S, hint S] at h1
    by_cases hSu : S = univ
    · subst hSu
      have hin : edgeInside (univ : Finset (Fin m)) s(a, b) :=
        ⟨a, b, rfl, mem_univ _, mem_univ _⟩
      rw [if_pos hin] at h1
      simp only [compl_univ, sum_empty, sum_const_zero, sub_zero] at h1
      linarith
    · have hc := hcut S hS hSu
      have : (0 : ℝ) ≤ if edgeInside S s(a, b) then 1 else 0 := by split_ifs <;> norm_num
      linarith
  · intro e he
    exact pairCost_nonneg x hxs hx0 e
