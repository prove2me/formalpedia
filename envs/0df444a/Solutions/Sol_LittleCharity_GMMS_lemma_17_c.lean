-- Prove2me | solution 1 for LittleCharity.GMMS.lemma_17_c
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:05:06.206329+00:00
-- url     : https://prove2.me/submissions/7af8763d-6ddb-4fb8-89ec-ac30c53b8ea2

import Mathlib
import Definitions.Def_LittleCharity_GMMS_Setting

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : LittleCharity.MMS.IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hX : LittleCharity.EFX.IsPartialAllocation X) (hEFX : LittleCharity.MMS.IsEFX v X)
    (hpool : ∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i))
    (s : Fin n) (hs : LittleCharity.EFX.IsSource v X s) (i : Fin n) :
    ∀ j, j ≠ s → (3 ≤ (LittleCharity.GMMS.donate X s j).card ∨ j = i) →
      v i (LittleCharity.GMMS.donate X s j) ≤ (3 / 2 : ℝ) * v i (LittleCharity.GMMS.donate X s i) := by
  intro j hjs hcase
  unfold LittleCharity.GMMS.donate at hcase ⊢
  rw [Function.update_of_ne hjs] at hcase ⊢
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
  have hnn : 0 ≤ v i (X i) := hadd.2 i _
  by_cases hji : j = i
  · subst hji
    linarith
  · have h3 : 3 ≤ (X j).card := by
      rcases hcase with h | h
      · exact h
      · exact absurd h hji
    have hne : (X j).Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨g, hg, hmin⟩ := Finset.exists_min_image (X j) (fun g => v i {g}) hne
    have hsum : (X j).card • v i {g} ≤ ∑ x ∈ X j, v i {x} :=
      Finset.card_nsmul_le_sum _ _ _ (fun x hx => hmin x hx)
    rw [← hadd.1 i (X j)] at hsum
    have hEFXg := hEFX i j g hg
    have hsplit : v i ((X j).erase g) = v i (X j) - v i {g} := by
      rw [hadd.1 i ((X j).erase g), hadd.1 i (X j), ← Finset.add_sum_erase _ _ hg]
      ring
    rw [hsplit] at hEFXg
    have hcard : (3 : ℝ) ≤ ((X j).card : ℝ) := by exact_mod_cast h3
    have hg0 : 0 ≤ v i {g} := hadd.2 i _
    have hs2 : ((X j).card : ℝ) * v i {g} ≤ v i (X j) := by
      simpa [nsmul_eq_mul] using hsum
    have : 3 * v i {g} ≤ v i (X j) := by nlinarith
    linarith
