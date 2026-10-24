-- Prove2me | solution 1 for OAI.CommonBasesFPRAS.positive_count_iff_common_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-23T21:32:09.562123+00:00
-- url     : https://prove2.me/submissions/fef8f926-5f8d-447f-9606-7b76173046bb

import Definitions.Def_CommonBasesFPRAS

open OAI.CommonBasesFPRAS

theorem solution (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (hr₁ : M₁.eRank = (r : ℕ∞)) (hr₂ : M₂.eRank = (r : ℕ∞)) :
    0 < commonBaseCount M₁ M₂ ↔
      ∃ I : Finset (Fin n), I.card = r ∧
        M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n)) := by
  classical
  change 0 < Nat.card {A : Finset (Fin n) //
    M₁.IsBase (A : Set (Fin n)) ∧ M₂.IsBase (A : Set (Fin n))} ↔ _
  constructor
  · intro h
    obtain ⟨⟨I, hI₁, hI₂⟩⟩ := (Nat.card_pos_iff.mp h).1
    refine ⟨I, ?_, hI₁.indep, hI₂.indep⟩
    have hcard := hI₁.encard_eq_eRank
    simpa [hr₁] using hcard
  · rintro ⟨I, hcard, hI₁, hI₂⟩
    have hB₁ : M₁.IsBase (I : Set (Fin n)) := by
      apply hI₁.isBase_of_eRk_ge I.finite_toSet
      rw [hI₁.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard, hcard, hr₁]
    have hB₂ : M₂.IsBase (I : Set (Fin n)) := by
      apply hI₂.isBase_of_eRk_ge I.finite_toSet
      rw [hI₂.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard, hcard, hr₂]
    exact Nat.card_pos_iff.mpr ⟨⟨⟨I, hB₁, hB₂⟩⟩, inferInstance⟩

