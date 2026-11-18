-- Prove2me | solution 1 for LittleCharity.GMMS.lemma_17_a
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:05:04.829315+00:00
-- url     : https://prove2.me/submissions/3d6932c8-2e07-4c02-a768-de677b615282

import Mathlib
import Definitions.Def_LittleCharity_GMMS_Setting

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : LittleCharity.MMS.IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hX : LittleCharity.EFX.IsPartialAllocation X) (hEFX : LittleCharity.MMS.IsEFX v X)
    (hpool : ∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i))
    (s : Fin n) (hs : LittleCharity.EFX.IsSource v X s) (i : Fin n) :
    ∀ j, j ≠ s → j ≠ i → (LittleCharity.GMMS.donate X s j).card = 2 →
      ∀ g ∈ LittleCharity.GMMS.donate X s j, v i {g} ≤ v i (LittleCharity.GMMS.donate X s i) := by
  intro j hjs hji hcard g hg
  unfold LittleCharity.GMMS.donate at hcard hg ⊢
  rw [Function.update_of_ne hjs] at hcard hg
  have hmono : ∀ S T : Finset (Fin m), S ⊆ T → ∀ k, v k S ≤ v k T := by
    intro S T hST k
    rw [hadd.1 k S, hadd.1 k T]
    apply Finset.sum_le_sum_of_subset_of_nonneg hST
    intro x _ _
    exact hadd.2 k _
  have hXi : v i (X i) ≤ v i (Function.update X s (X s ∪ LittleCharity.EFX.pool X) i) := by
    by_cases his : i = s
    · subst his
      rw [Function.update_self]
      exact hmono _ _ Finset.subset_union_left i
    · rw [Function.update_of_ne his]
  -- the other good of X j
  obtain ⟨a, b, hab, hXj⟩ := Finset.card_eq_two.1 hcard
  have hgab : g = a ∨ g = b := by
    rw [hXj] at hg; simpa using hg
  have hbX : ∀ x, x ∈ X j → x = a ∨ x = b := by
    intro x hx; rw [hXj] at hx; simpa using hx
  have hera : (X j).erase a = {b} := by
    rw [hXj]; ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact absurd h2 h1
      · exact h2
    · intro h; subst h; exact ⟨hab.symm, Or.inr rfl⟩
  have herb : (X j).erase b = {a} := by
    rw [hXj]; ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact h2
      · exact absurd h2 h1
    · intro h; subst h; exact ⟨hab, Or.inl rfl⟩
  have hamem : a ∈ X j := by rw [hXj]; simp
  have hbmem : b ∈ X j := by rw [hXj]; simp
  rcases hgab with rfl | rfl
  · have h1 := hEFX i j b hbmem
    rw [herb] at h1
    exact le_trans h1 hXi
  · have h1 := hEFX i j a hamem
    rw [hera] at h1
    exact le_trans h1 hXi
