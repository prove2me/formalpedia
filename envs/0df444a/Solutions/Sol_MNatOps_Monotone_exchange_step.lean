-- Prove2me | solution 1 for MNatOps.Monotone.exchange_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:40:30.892482+00:00
-- url     : https://prove2.me/submissions/6360dffe-c77f-4c78-afd6-9ff2526f9978

import Mathlib
import Definitions.Def_MNatOps_Monotone_Model
import Theorems.Thm_MNatOps_Monotone_box_step

open MNatOps.Monotone DiscreteConvex.MConvexFunctions DiscreteConvex.EconomicEquilibrium in
theorem solution {m n : ℕ} (G : (Fin m ⊕ Fin n → ℤ) → WithBot ℝ) (hG : SSQMNatConcave G)
    (l : Fin n → WithBot ℤ) (u : Fin n → WithTop ℤ) (s s' : Fin m → ℤ) (hss : s ≤ s')
    (a : Fin n → ℤ) (ha : a ∈ optSet G l u s) (haf : G (Sum.elim s a) ≠ ⊥)
    (a' : Fin n → ℤ) (ha' : a' ∈ optSet G l u s') (ha'f : G (Sum.elim s' a') ≠ ⊥)
    (i : Fin n) (hi : a i < a' i) :
    ∃ j : Option (Fin n), (∀ k, j = some k → a' k < a k) ∧
      a' - dir i j ∈ optSet G l u s' ∧ a + dir i j ∈ optSet G l u s ∧
      (a' ∈ lowerOrthant a i.val → a' - dir i j ∈ lowerOrthant a i.val) := by
  -- the two joint points x = (s', a') and y = (s, a)
  have hx : Sum.elim s' a' ∈ UDom G := ha'f
  have hy : Sum.elim s a ∈ UDom G := haf
  have hi' : (Sum.inr i : Fin m ⊕ Fin n) ∈ SuppPos (Sum.elim s' a') (Sum.elim s a) := by
    simp [SuppPos, hi]
  obtain ⟨J, hJ, α₀, hα₀, hα⟩ := hG _ hx _ hy _ hi'
  -- J cannot be a parameter coordinate, since s ≤ s'
  obtain ⟨j, rfl, hj⟩ : ∃ j : Option (Fin n), J = j.map Sum.inr ∧
      ∀ k, j = some k → a' k < a k := by
    rcases hJ with rfl | ⟨j', rfl, hj'⟩
    · exact ⟨none, rfl, by simp⟩
    · simp only [SuppNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hj'
      cases j' with
      | inl k => exact absurd (hss k) (by simpa using hj')
      | inr k => exact ⟨some k, rfl, by simpa using hj'⟩
  -- the joint direction is the embedding of the box direction
  have hdir : dir (Sum.inr i : Fin m ⊕ Fin n) (j.map Sum.inr) =
      Sum.elim (0 : Fin m → ℤ) (dir i j) := by
    funext k
    cases j with
    | none => cases k <;> simp [dir, CharVec]
    | some j => cases k <;> simp [dir, CharVec]
  have e1 : Sum.elim s' a' - (1 : ℤ) • dir (Sum.inr i : Fin m ⊕ Fin n) (j.map Sum.inr) =
      Sum.elim s' (a' - dir i j) := by
    rw [hdir, one_smul]; funext k; cases k <;> simp
  have e2 : Sum.elim s a + (1 : ℤ) • dir (Sum.inr i : Fin m ⊕ Fin n) (j.map Sum.inr) =
      Sum.elim s (a + dir i j) := by
    rw [hdir, one_smul]; funext k; cases k <;> simp
  obtain ⟨hb1, hb2⟩ := box_step l u a a' ha.1 ha'.1 i hi j hj
  have h1 := ha'.2 _ hb1
  have h2 := ha.2 _ hb2
  have key := hα 1 (by norm_num) (by omega)
  rw [e1, e2] at key
  have heq : G (Sum.elim s' (a' - dir i j)) = G (Sum.elim s' a') ∧
      G (Sum.elim s (a + dir i j)) = G (Sum.elim s a) := by
    rcases key with h | h | h
    · exact absurd h (not_lt.mpr h1)
    · exact absurd h (not_lt.mpr h2)
    · exact h
  refine ⟨j, hj, ⟨hb1, fun b hb => ?_⟩, ⟨hb2, fun b hb => ?_⟩, ?_⟩
  · rw [heq.1]; exact ha'.2 b hb
  · rw [heq.2]; exact ha.2 b hb
  · intro hlo k hk
    have hki : k ≠ i := by intro h; subst h; omega
    have := hlo k hk
    cases j with
    | none => simp [dir, CharVec, hki]; omega
    | some j =>
      by_cases hkj : k = j
      · subst hkj; have := hj k rfl; simp [dir, CharVec, hki]; omega
      · simp [dir, CharVec, hki, hkj]; omega
