-- Prove2me | solution 1 for HetExponomial.ChoiceProb.negative_terms
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:55:22.233496+00:00
-- url     : https://prove2.me/submissions/84055cb6-8557-4cc1-b4c7-70e2673990c3

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model

open HetExponomial.ChoiceProb in
theorem solution {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (i : Fin n) (k : Fin (levels u).card) (hk : level u k = u i)
    (w w' : Fin (levels u).card) (hw : w < k) (hw' : w'.val = w.val + 1) :
    -(lam i * ∑ j ∈ Finset.univ.filter (fun j => u j = level u w), lam j) /
        ((∑ j ∈ betterThan u (level u w'), lam j) * (∑ j ∈ betterThan u (level u w), lam j)) *
        Real.exp (-(∑ j ∈ betterThan u (level u w), lam j * (u j - level u w))) =
      -∑ k' ∈ (strictlyWorse u i).filter (fun k' => u k' = level u w),
          lam i / Lplus u lam k' * G u lam k' := by
  set a := level u w with ha
  have hak : a < u i := hk ▸ (level u).strictMono hw
  have hww' : w < w' := by rw [Fin.lt_iff_val_lt_val]; omega
  have hgap : ∀ j, a < u j ↔ level u w' ≤ u j := by
    intro j
    constructor
    · intro h
      have hmem : u j ∈ levels u := Finset.mem_image_of_mem u (Finset.mem_univ j)
      have hr : u j ∈ Set.range (level u) := by
        unfold level
        rw [Finset.range_orderEmbOfFin]
        exact hmem
      obtain ⟨m, hm⟩ := hr
      rw [← hm] at h ⊢
      have hwm : w < m := (level u).lt_iff_lt.mp h
      have : w' ≤ m := by rw [Fin.le_iff_val_le_val]; rw [Fin.lt_iff_val_lt_val] at hwm; omega
      exact (level u).le_iff_le.mpr this
    · intro h
      exact lt_of_lt_of_le ((level u).strictMono hww') h
  have hset : (strictlyWorse u i).filter (fun k' => u k' = a) =
      Finset.univ.filter (fun j => u j = a) := by
    ext j
    simp only [strictlyWorse, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hak, h⟩
  obtain ⟨P, hP⟩ : ∃ P, P = ∑ j ∈ betterThan u (level u w'), lam j := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∑ j ∈ betterThan u a, lam j := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(∑ j ∈ betterThan u a, lam j * (u j - a))) := ⟨_, rfl⟩
  have hLplus : ∀ k', u k' = a → Lplus u lam k' = P := by
    intro k' hk'
    rw [hP]
    unfold Lplus strictlyBetter betterThan
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hk']
    exact hgap j
  have hG : ∀ k', u k' = a → G u lam k' = lam k' / Q * E := by
    intro k' hk'
    unfold G Lsum better
    rw [hk', hQ, hE]
  rw [← hP, ← hQ, ← hE, hset]
  have hR : ∑ k' ∈ Finset.univ.filter (fun j => u j = a), lam i / Lplus u lam k' * G u lam k' =
      ∑ k' ∈ Finset.univ.filter (fun j => u j = a), lam i / P * (lam k' / Q * E) := by
    apply Finset.sum_congr rfl
    intro k' hk'
    have hk'a := (Finset.mem_filter.mp hk').2
    rw [hLplus k' hk'a, hG k' hk'a]
  rw [hR]
  have : ∑ k' ∈ Finset.univ.filter (fun j => u j = a), lam i / P * (lam k' / Q * E) =
      lam i / P / Q * E * ∑ k' ∈ Finset.univ.filter (fun j => u j = a), lam k' := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [this]
  ring
