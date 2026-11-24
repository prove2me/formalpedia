-- Prove2me | solution 1 for GlobalTheory.MultipleMembershipForAll.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:21:29.549838+00:00
-- url     : https://prove2.me/submissions/061c616b-6fe5-4538-8c04-a49885972a6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulMemOfForall
import Theorems.Thm_GlobalTheory_MultipleMembershipForAll_exists_mul_mem_of_forall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultipleMembershipForAll
open IsLocalRing
namespace GlobalTheory.MultipleMembershipForAll
theorem _root_.solution : ∀ (S : Type) [inst : CommRing S] [IsNoetherianRing S] (Q : Ideal S)
    [inst_2 : Ideal.IsPrime Q], ∃ (h : ℕ) (f : Fin h → S), ∃ g ∉ Q, (∀ (j : Fin h), f j ∈ Q) ∧
    (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧
    h = Submodule.spanFinrank (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
    ∀ (a : Fin h → S), ∀ u ∉ Q, u * ∑ j : Fin h, a j * f j ∈ Q ^ (2 : ℕ) →
      ∀ (j : Fin h), a j ∈ Q := by
  intro S _ _ Q _
  classical
  let R := Localization.AtPrime Q
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing Q.primeCompl R inferInstance
  obtain ⟨t, htcard, htspan⟩ :=
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R)).exists_span_finset_card_eq_spanFinrank

  have hsurj : ∀ y : R, ∃ p : S × Q.primeCompl, IsLocalization.mk' R p.1 p.2 = y := fun y => by
    obtain ⟨p, hp⟩ := IsLocalization.mk'_surjective Q.primeCompl y
    exact ⟨p, hp⟩
  choose p hxs using hsurj
  let x : R → S := fun y => (p y).1
  let e : Fin t.card → R := fun j => (t.equivFin.symm j : R)
  let f : Fin t.card → S := fun j => x (e j)
  have he : ∀ j, e j ∈ IsLocalRing.maximalIdeal R := fun j => by
    rw [← htspan]; exact Submodule.subset_span (t.equivFin.symm j).2
  have hfQ : ∀ j, f j ∈ Q := fun j => by
    have h := he j
    rw [← hxs (e j)] at h
    exact (IsLocalization.AtPrime.mk'_mem_maximal_iff R Q _ _).mp h

  have hspan : Ideal.span (Set.range fun j => algebraMap S R (f j)) = IsLocalRing.maximalIdeal R := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R Q _).mpr (hfQ j)
    · rw [← htspan]
      refine Submodule.span_le.mpr fun y hy => ?_
      have hy' : y = e (t.equivFin ⟨y, hy⟩) := by simp [e]
      rw [hy', ← hxs (e _), IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, rfl⟩)

  have hloc : ∀ y ∈ Q, ∃ g ∉ Q, g * y ∈ Ideal.span (Set.range f) := by
    intro y hy
    have hmem : algebraMap S R y ∈ (Ideal.span (Set.range f)).map (algebraMap S R) := by
      rw [Ideal.map_span, ← Set.range_comp]
      change algebraMap S R y ∈ Ideal.span (Set.range fun j => algebraMap S R (f j))
      rw [hspan]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R Q _).mpr hy
    obtain ⟨g, hg, hgy⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff Q.primeCompl R _ _).mp hmem
    exact ⟨g, hg, hgy⟩
  obtain ⟨g, hg, hgQ⟩ := exists_mul_mem_of_forall Q _ (IsNoetherian.noetherian Q) hloc
  refine ⟨t.card, f, g, hg, hfQ, hgQ, htcard, ?_⟩

  intro a u hu hsum j0
  by_contra hj0
  set E : Fin t.card → R := fun j => algebraMap S R (f j) with hE
  set m := IsLocalRing.maximalIdeal R with hm
  have hA : IsUnit (algebraMap S R (a j0)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff R Q _).mpr hj0
  have hU : IsUnit (algebraMap S R u) := (IsLocalization.AtPrime.isUnit_to_map_iff R Q _).mpr hu
  have hsq : ∑ j, algebraMap S R (a j) * E j ∈ m ^ 2 := by
    have h1 : algebraMap S R (u * ∑ j, a j * f j) ∈ m ^ 2 := by
      rw [hm, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hsum
    simp only [map_mul, map_sum] at h1
    obtain ⟨v, hv⟩ := hU.exists_left_inv
    have h2 := Ideal.mul_mem_left _ v h1
    rwa [← mul_assoc, hv, one_mul] at h2
  let N : Ideal R := Ideal.span (((Finset.univ.erase j0).image E : Finset R) : Set R)
  have hEN : ∀ j, j ≠ j0 → E j ∈ N := fun j hj =>
    Ideal.subset_span (Finset.mem_coe.mpr
      (Finset.mem_image_of_mem E (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)))
  have hrest : ∑ j ∈ Finset.univ.erase j0, algebraMap S R (a j) * E j ∈ N :=
    Ideal.sum_mem _ fun j hj => Ideal.mul_mem_left _ _ (hEN j (Finset.ne_of_mem_erase hj))
  have hj0mem : E j0 ∈ N ⊔ m * m := by
    have hsplit := Finset.add_sum_erase Finset.univ (fun j => algebraMap S R (a j) * E j)
      (Finset.mem_univ j0)
    have h2 : algebraMap S R (a j0) * E j0 ∈ N ⊔ m * m := by
      have h3 : algebraMap S R (a j0) * E j0 = ∑ j, algebraMap S R (a j) * E j -
          ∑ j ∈ Finset.univ.erase j0, algebraMap S R (a j) * E j := by
        rw [← hsplit]; ring
      rw [h3]
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (by rwa [← sq])) (Ideal.mem_sup_left hrest)
    obtain ⟨v, hv⟩ := hA.exists_left_inv
    have h4 := Ideal.mul_mem_left _ v h2
    rwa [← mul_assoc, hv, one_mul] at h4
  have hle : m ≤ N ⊔ m • m := by
    rw [Ideal.smul_eq_mul]
    calc m = Ideal.span (Set.range E) := hspan.symm
      _ ≤ N ⊔ m * m := by
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        by_cases hj : j = j0
        · subst hj; exact hj0mem
        · exact Ideal.mem_sup_left (hEN j hj)
  have hmN : m ≤ N := Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian m)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle
  have hNm : N ≤ m := by
    rw [Ideal.span_le]
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    rw [← hspan]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hcard : m.spanFinrank ≤ t.card - 1 := by
    calc m.spanFinrank = N.spanFinrank := by rw [le_antisymm hmN hNm]
      _ ≤ (((Finset.univ.erase j0).image E : Finset R) : Set R).ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)
      _ = ((Finset.univ.erase j0).image E).card := Set.ncard_coe_finset _
      _ ≤ (Finset.univ.erase j0).card := Finset.card_image_le
      _ = t.card - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hpos : 0 < t.card := j0.pos
  omega
end GlobalTheory.MultipleMembershipForAll
