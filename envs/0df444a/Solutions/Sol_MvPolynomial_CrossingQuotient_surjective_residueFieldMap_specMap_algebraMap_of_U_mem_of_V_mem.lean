-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.surjective_residueFieldMap_specMap_algebraMap_of_U_mem_of_V_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8012ade3-8423-5bd0-842b-2db955872281

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_CrossingQuotient_surjective_residueFieldMap_specMap_algebraMap_of_U_mem_of_V_mem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

theorem solution
    {O : Type} [CommRing O] (a : O) (q : ↥(CrossingQuotient.crossingScheme a))
    (hU : CrossingQuotient.U a ∈ q.asIdeal) (hV : CrossingQuotient.V a ∈ q.asIdeal) :
    Function.Surjective
      ((Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O a)))).residueFieldMap q).hom := by
  classical
  let f : CommRingCat.of O ⟶ CommRingCat.of (CrossingQuotient O a) := CommRingCat.ofHom (algebraMap O (CrossingQuotient O a))

  have hspan : Ideal.map (CrossingQuotient.mk a) (Ideal.span (X '' (Set.univ : Set (Fin 2)))) ≤ q.asIdeal := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, -, rfl⟩, rfl⟩
    fin_cases i
    · exact hU
    · exact hV
  have key : ∀ g : CrossingQuotient O a, ∃ c : O, g - f.hom c ∈ q.asIdeal := by
    intro g
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mkₐ_surjective O _ g
    refine ⟨P.coeff 0, ?_⟩
    have hmem : P - C (P.coeff 0) ∈ Ideal.span (X '' (Set.univ : Set (Fin 2))) := by
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl, sub_self] at hm
        exact hm rfl
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
      exact ⟨i, Set.mem_univ _, by simpa using hi⟩
    have := hspan (Ideal.mem_map_of_mem (CrossingQuotient.mk a) hmem)
    rw [map_sub, CrossingQuotient.mk_C_eq_algebraMap] at this
    exact this

  have hres : ∀ z : (Spec (CommRingCat.of (CrossingQuotient O a))).presheaf.stalk q,
      ∃ w : (Spec (CommRingCat.of O)).presheaf.stalk (PrimeSpectrum.comap f.hom q),
        ((Spec.map f).stalkMap q).hom w - z ∈ IsLocalRing.maximalIdeal _ := by
    intro z

    obtain ⟨⟨g, s⟩, hz⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl
      ((Spec.stalkIso (CommRingCat.of (CrossingQuotient O a)) q).hom.hom z)
    have hz0 : IsLocalization.mk' _ g s = (Spec.stalkIso (CommRingCat.of (CrossingQuotient O a)) q).hom.hom z := hz

    obtain ⟨c, hc⟩ := key g
    obtain ⟨c₀, hc₀⟩ := key (s : CrossingQuotient O a)
    have hs₀ : c₀ ∈ (Ideal.comap f.hom q.asIdeal).primeCompl := by
      intro (h : f.hom c₀ ∈ q.asIdeal)
      exact s.2 (by simpa using q.asIdeal.add_mem hc₀ h)
    obtain ⟨y₁, hy₁⟩ : ∃ y₁ : q.asIdeal.primeCompl, (y₁ : CrossingQuotient O a) = f.hom c₀ :=
      ⟨⟨f.hom c₀, by simpa using hs₀⟩, rfl⟩
    let w' : Localization.AtPrime (Ideal.comap f.hom q.asIdeal) := IsLocalization.mk' _ c ⟨c₀, hs₀⟩
    refine ⟨(Spec.stalkIso (CommRingCat.of O) (PrimeSpectrum.comap f.hom q)).inv.hom w', ?_⟩

    have Hc := Scheme.localRingHom_comp_stalkIso f q
    have hRinv : (Spec.stalkIso (CommRingCat.of O) (PrimeSpectrum.comap f.hom q)).hom.hom
        ((Spec.stalkIso (CommRingCat.of O) (PrimeSpectrum.comap f.hom q)).inv.hom w') = w' := by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, RingHom.id_apply]
    have hSinv : ∀ t, (Spec.stalkIso (CommRingCat.of (CrossingQuotient O a)) q).hom.hom
        ((Spec.stalkIso (CommRingCat.of (CrossingQuotient O a)) q).inv.hom t) = t := fun t => by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, RingHom.id_apply]
    have happ := congrArg (fun φ : (Spec (CommRingCat.of O)).presheaf.stalk (PrimeSpectrum.comap f.hom q) ⟶
        (Spec (CommRingCat.of (CrossingQuotient O a))).presheaf.stalk q =>
          φ.hom ((Spec.stalkIso (CommRingCat.of O) (PrimeSpectrum.comap f.hom q)).inv.hom w')) Hc
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at happ
    rw [hRinv] at happ

    have hT : (Spec.stalkIso (CommRingCat.of (CrossingQuotient O a)) q).hom.hom
        (((Spec.map f).stalkMap q).hom ((Spec.stalkIso (CommRingCat.of O) (PrimeSpectrum.comap f.hom q)).inv.hom w')) =
        Localization.localRingHom (Ideal.comap f.hom q.asIdeal) q.asIdeal f.hom rfl w' :=
      (congrArg ((Spec.stalkIso (CommRingCat.of (CrossingQuotient O a)) q).hom.hom) happ.symm).trans (hSinv _)

    have hL : Localization.localRingHom (Ideal.comap f.hom q.asIdeal) q.asIdeal f.hom rfl w' =
        IsLocalization.mk' (CommRingCat.of (Localization.AtPrime q.asIdeal)) (f.hom c) y₁ := by
      show Localization.localRingHom (Ideal.comap f.hom q.asIdeal) q.asIdeal f.hom rfl
        (IsLocalization.mk' (Localization.AtPrime (Ideal.comap f.hom q.asIdeal)) c ⟨c₀, hs₀⟩) = _
      rw [Localization.localRingHom_mk']
      have hy : (⟨f.hom c₀, by simpa using hs₀⟩ : q.asIdeal.primeCompl) = y₁ := Subtype.ext hy₁.symm
      rw [← hy]

    have hnum : f.hom c * (s : CrossingQuotient O a) - g * (y₁ : CrossingQuotient O a) ∈ q.asIdeal := by
      have e1 : f.hom c * (s : CrossingQuotient O a) - g * (y₁ : CrossingQuotient O a) =
          -(g - f.hom c) * s + g * ((s : CrossingQuotient O a) - f.hom c₀) := by rw [hy₁]; ring
      rw [e1]
      exact q.asIdeal.add_mem (q.asIdeal.mul_mem_right _ (q.asIdeal.neg_mem hc)) (q.asIdeal.mul_mem_left _ hc₀)
    have e := IsLocalization.mk'_sub (CommRingCat.of (Localization.AtPrime q.asIdeal)) (f.hom c) g y₁ s
    have m := (IsLocalization.AtPrime.mk'_mem_maximal_iff (CommRingCat.of (Localization.AtPrime q.asIdeal)) q.asIdeal
      (f.hom c * (s : CrossingQuotient O a) - g * (y₁ : CrossingQuotient O a)) (y₁ * s)).mpr hnum
    rw [e] at m

    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at m ⊢
    intro hu
    apply m
    have hu' := hu.map (Spec.stalkIso (CommRingCat.of (CrossingQuotient O a)) q).hom.hom
    rw [(Spec.stalkIso (CommRingCat.of (CrossingQuotient O a)) q).hom.hom.map_sub, hT, hL, ← hz0] at hu'
    exact hu'

  intro y
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨w, hw⟩ := hres z
  refine ⟨IsLocalRing.residue _ w, ?_⟩
  show IsLocalRing.ResidueField.map ((Spec.map f).stalkMap q).hom (IsLocalRing.residue _ w) = IsLocalRing.residue _ z
  rw [IsLocalRing.ResidueField.map_residue, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hw

end S_MvPolynomial_CrossingQuotient_surjective_residueFieldMap_specMap_algebraMap_of_U_mem_of_V_mem
end P2MW
export P2MW.S_MvPolynomial_CrossingQuotient_surjective_residueFieldMap_specMap_algebraMap_of_U_mem_of_V_mem (solution)
