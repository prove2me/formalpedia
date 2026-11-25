-- Prove2me | solution 1 for GlobalTheory.hom_value_congruent_int_mod_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:18:49.921426+00:00
-- url     : https://prove2.me/submissions/2a65a8fe-6ea8-4c0c-affa-2ff946eff185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HomValueCongruentIntModPrime
import Theorems.Thm_GlobalTheory_mem_span_prime_of_not_isUnit_of_pow_sub_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A O : Type) [CommRing A] [CommRing O] [IsLocalRing O] (g : ℕ), g.Prime → ¬ IsUnit (g : O) → (∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) → ∀ (σ : A →+* O) (x : A), (∃ i : ℤ, σ x - (i : O) ∈ Ideal.span {(g : O)}) ∧ (¬ IsUnit (σ x) → σ x ∈ Ideal.span {(g : O)}) := by
  intro A O _ _ _ g hg hgu hA σ x
  have hy : σ x ^ g - σ x ∈ Ideal.span {(g : O)} := by
    have h := Ideal.mem_map_of_mem σ (hA x)
    rw [Ideal.map_span, Set.image_singleton, map_natCast, map_sub, map_pow] at h
    exact h
  refine ⟨?_, fun hn => mem_span_prime_of_not_isUnit_of_pow_sub_mem g hg (σ x) hy hn⟩
  have : Fact g.Prime := ⟨hg⟩
  have : NeZero g := ⟨hg.ne_zero⟩
  have hgm : (g : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hgu
  have hspan : Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_iff_mem _).mpr hgm
  have hgk : ((g : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact hgm
  have : CharP (IsLocalRing.ResidueField O) g := (CharP.charP_iff_prime_eq_zero hg).mpr hgk
  have hfix : IsLocalRing.residue O (σ x) ^ g = IsLocalRing.residue O (σ x) := by
    have h := (IsLocalRing.residue_eq_zero_iff _).mpr (hspan hy)
    rwa [map_sub, map_pow, sub_eq_zero] at h
  obtain ⟨a, ha⟩ : ∃ a : ZMod g,
      IsLocalRing.residue O (σ x) = ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O) a := by
    by_contra hno
    simp only [not_exists] at hno
    classical
    have hpoly : (Polynomial.X ^ g - Polynomial.X : Polynomial (IsLocalRing.ResidueField O)) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero _ hg.one_lt
    have hnot : IsLocalRing.residue O (σ x) ∉
        Finset.univ.image (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O)) := by
      intro h
      obtain ⟨b, -, hb⟩ := Finset.mem_image.mp h
      exact hno b hb.symm
    have hsub : (insert (IsLocalRing.residue O (σ x))
        (Finset.univ.image (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O)))).val ⊆
        (Polynomial.X ^ g - Polynomial.X : Polynomial (IsLocalRing.ResidueField O)).roots := by
      intro z hz
      have hz' : z ∈ insert (IsLocalRing.residue O (σ x))
        (Finset.univ.image (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O))) := hz
      rw [Polynomial.mem_roots hpoly, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, sub_eq_zero]
      rcases Finset.mem_insert.mp hz' with h | h
      · rw [h]; exact hfix
      · obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp h
        rw [← map_pow, ZMod.pow_card]
    have hcard := Polynomial.card_le_degree_of_subset_roots hsub
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hg.one_lt, Finset.card_insert_of_notMem hnot,
      Finset.card_image_of_injective _ (RingHom.injective _), Finset.card_univ, ZMod.card] at hcard
    omega
  have ha' : IsLocalRing.residue O (σ x) = IsLocalRing.residue O ((a.val : ℕ) : O) := by
    rw [ha, map_natCast, ← map_natCast (ZMod.castHom (dvd_refl g) (IsLocalRing.ResidueField O)),
      ZMod.natCast_zmod_val]
  have hnu : ¬ IsUnit (σ x - ((a.val : ℕ) : O)) := by
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
      map_sub, ha', sub_self]
  have hne : Ideal.span {(g : O)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hgu
  have : Nontrivial (O ⧸ Ideal.span {(g : O)}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : CharP (O ⧸ Ideal.span {(g : O)}) g := (CharP.charP_iff_prime_eq_zero hg).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _)
  have hyQ : Ideal.Quotient.mk (Ideal.span {(g : O)}) (σ x) ^ g
      - Ideal.Quotient.mk (Ideal.span {(g : O)}) (σ x) = 0 := by
    rw [← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]; exact hy
  have hnQ : ((a.val : ℕ) : O ⧸ Ideal.span {(g : O)}) ^ g = ((a.val : ℕ) : O ⧸ Ideal.span {(g : O)}) := by
    rw [← map_natCast (ZMod.castHom (dvd_refl g) (O ⧸ Ideal.span {(g : O)})), ← map_pow, ZMod.pow_card]
  have hsh : (σ x - ((a.val : ℕ) : O)) ^ g - (σ x - ((a.val : ℕ) : O)) ∈ Ideal.span {(g : O)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_sub, map_natCast, sub_pow_char, hnQ]
    linear_combination hyQ
  refine ⟨(a.val : ℤ), ?_⟩
  rw [Int.cast_natCast]
  exact mem_span_prime_of_not_isUnit_of_pow_sub_mem g hg _ hsh hnu
end GlobalTheory
