-- Prove2me | solution 1 for HarmonicRanking.Main.Supplement.theorem_7_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T20:23:54.388536+00:00
-- url     : https://prove2.me/submissions/91935f19-6b7d-4cc5-8af7-eac47c6d6486
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HarmonicRanking_Main_Supplement_PriceLP
import Theorems.Thm_HarmonicRanking_Main_Supplement_lemma_A_1
import Theorems.Thm_HarmonicRanking_Main_Supplement_lemma_A_2
import Theorems.Thm_HarmonicRanking_Main_Supplement_theorem_B_3
import Theorems.Thm_HarmonicRanking_Main_Supplement_theorem_B_7

set_option autoImplicit false

namespace HarmonicRanking.Main.Supplement

theorem k_to_A {m : ℕ} (g : Fin m → Fin m → ℝ) (hg : IsKTable g) :
    ∃ F, InA F ∧ priceReflect F = g := by
  obtain ⟨h0, hmono, hsym⟩ := hg
  have hnn : ∀ i r, 0 ≤ g i r := by
    intro i r
    refine le_trans (h0 i) (hmono i ?_)
    exact Fin.mk_le_of_le_val (Nat.zero_le _)
  have hle : ∀ i r, g i r ≤ 1 := by
    intro i r
    have := hsym i r
    have := hnn r i
    linarith
  refine ⟨fun ℓ r => g (Fin.rev r) (Fin.rev ℓ), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro ℓ r
    exact hsym _ _
  · intro ℓ r
    exact ⟨hnn _ _, hle _ _⟩
  · intro r ℓ ℓ' h
    exact hmono _ (Fin.rev_le_rev.mpr h)
  · intro ℓ r r' h
    have h1 := hsym (Fin.rev r) (Fin.rev ℓ)
    have h2 := hsym (Fin.rev r') (Fin.rev ℓ)
    have h3 := hmono (Fin.rev ℓ) (Fin.rev_le_rev.mpr h)
    show g (Fin.rev r) (Fin.rev ℓ) ≤ g (Fin.rev r') (Fin.rev ℓ)
    linarith
  · funext i q
    simp [priceReflect]

theorem A_to_k {m : ℕ} (hm : 1 ≤ m) (F : Fin m → Fin m → ℝ) (hF : InA F) :
    IsKTable (priceReflect F) := by
  obtain ⟨hD, hb, hanti, hmono⟩ := hF
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (hb _ _).1
  · intro i q q' h
    exact hanti _ (Fin.rev_le_rev.mpr h)
  · intro i r
    have := hD (Fin.rev r) (Fin.rev i)
    simpa [priceReflect, add_comm] using this

end HarmonicRanking.Main.Supplement

open HarmonicRanking.Main.Supplement in
theorem solution (m : ℕ) (hm : 1 ≤ m) :
    gammaUW m = Vval m ∧ Vval m = lpValue m ∧
    (∃ gh : Fin m → Fin m → ℝ, IsCompTable gh ∧ wholeCellMin gh = gammaUW m) ∧
    (∃ g : Fin m → Fin m → ℝ, IsKTable g ∧ twoPathMin g = Vval m) := by
  have hA1 := lemma_A_1 m hm
  have hB7 := theorem_B_7 m hm
  have hw : ∀ gh : Fin m → Fin m → ℝ, IsCompTable gh →
      wholeCellMin gh = twoPathMin (reflect gh) := by
    intro gh h
    rw [hA1.2 gh h, lemma_A_2 m hm _ (hA1.1.mapsTo h)]
  obtain ⟨⟨F0, hF0, hR⟩, -⟩ := hB7.1
  have hK0 : IsKTable (priceReflect F0) := A_to_k hm F0 hF0
  have hK0v : twoPathMin (priceReflect F0) = lpValue m := by
    rw [← theorem_B_3 m hm F0 hF0, hR, hB7.2]
  have hV : Vval m = lpValue m := by
    apply le_antisymm
    · refine iSup₂_le fun g hg => ?_
      obtain ⟨F, hF, rfl⟩ := k_to_A g hg
      rw [← theorem_B_3 m hm F hF, ← hB7.2]
      exact hB7.1.2 ⟨F, hF, rfl⟩
    · rw [← hK0v]
      exact le_iSup₂ (f := fun (g : Fin m → Fin m → ℝ) (_ : IsKTable g) => twoPathMin g)
        (priceReflect F0) hK0
  have hG : gammaUW m = Vval m := by
    apply le_antisymm
    · refine iSup₂_le fun gh h => ?_
      rw [hw gh h]
      exact le_iSup₂ (f := fun (g : Fin m → Fin m → ℝ) (_ : IsKTable g) => twoPathMin g)
        (reflect gh) (hA1.1.mapsTo h)
    · refine iSup₂_le fun g hg => ?_
      obtain ⟨gh, h, rfl⟩ := hA1.1.surjOn hg
      rw [← hw gh h]
      exact le_iSup₂ (f := fun (gh : Fin m → Fin m → ℝ) (_ : IsCompTable gh) =>
        wholeCellMin gh) gh h
  refine ⟨hG, hV, ?_, ⟨_, hK0, by rw [hK0v, hV]⟩⟩
  obtain ⟨gh, h, hgh⟩ := hA1.1.surjOn hK0
  exact ⟨gh, h, by rw [hw gh h, hgh, hK0v, hG, hV]⟩
