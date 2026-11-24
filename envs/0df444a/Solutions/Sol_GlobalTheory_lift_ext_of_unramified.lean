-- Prove2me | solution 1 for GlobalTheory.lift_ext_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:15:00.511897+00:00
-- url     : https://prove2.me/submissions/8efdb3c2-4ed2-4613-953d-5553297ea537

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S)
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution [FormallyUnramified f] [LocallyOfFiniteType f]
    {B C : CommRingCat.{u}} (π : B ⟶ C) (hπ : Function.Surjective π)
    (hj : RingHom.ker π.hom ≤ Ideal.jacobson ⊥) {x₁ x₂ : Spec B ⟶ X}
    (h₀ : Spec.map π ≫ x₁ = Spec.map π ≫ x₂) (h : x₁ ≫ f = x₂ ≫ f) : x₁ = x₂ := by
  let g : Spec B ⟶ pullback f f := pullback.lift x₁ x₂ h
  have hg : Spec.map π ≫ g = (Spec.map π ≫ x₁) ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · simp only [g, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · simp only [g, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, h₀]
  have hrange : Set.range g.base ⊆ Set.range (pullback.diagonal f).base := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨m, hm, hym⟩ := Ideal.exists_le_maximal y.asIdeal y.isPrime.ne_top
    have hkm : RingHom.ker π.hom ≤ m := hj.trans (sInf_le ⟨bot_le, hm⟩)
    haveI := hm.isPrime
    let z : PrimeSpectrum C := ⟨m.map π.hom, Ideal.map_isPrime_of_surjective hπ hkm⟩
    have hz : PrimeSpectrum.comap π.hom z = ⟨m, hm.isPrime⟩ := by
      ext1
      show Ideal.comap π.hom (m.map π.hom) = m
      rw [Ideal.comap_map_of_surjective' _ hπ, sup_eq_left.mpr hkm]
    have hgp : g.base ⟨m, hm.isPrime⟩ ∈ (pullback.diagonal f).opensRange := by
      rw [← hz]
      show (Spec.map π ≫ g).base z ∈ _
      rw [hg]
      exact ⟨_, rfl⟩
    have hsp : y ⤳ ⟨m, hm.isPrime⟩ := (PrimeSpectrum.le_iff_specializes y ⟨m, hm.isPrime⟩).mp hym
    exact (hsp.map g.base.hom.continuous).mem_open (pullback.diagonal f).opensRange.isOpen hgp
  obtain ⟨l, hl⟩ : ∃ l, l ≫ pullback.diagonal f = g :=
    ⟨IsOpenImmersion.lift (pullback.diagonal f) g hrange, IsOpenImmersion.lift_fac _ _ _⟩
  have e₁ : x₁ = l := by
    rw [← pullback.lift_fst x₁ x₂ h]; change g ≫ _ = _; rw [← hl]; simp
  have e₂ : x₂ = l := by
    rw [← pullback.lift_snd x₁ x₂ h]; change g ≫ _ = _; rw [← hl]; simp
  rw [e₁, e₂]
end _root_.GlobalTheory
end GlobalTheory
