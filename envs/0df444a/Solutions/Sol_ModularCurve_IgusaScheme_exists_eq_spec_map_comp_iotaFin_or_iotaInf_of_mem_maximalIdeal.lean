-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_eq_spec_map_comp_iotaFin_or_iotaInf_of_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e146d546-4efc-588d-9d94-a5a0c1df10cf

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_eq_spec_map_comp_iotaFin_or_iotaInf_of_mem_maximalIdeal

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_eq_spec_map_comp_iotaFin_or_iotaInf_of_mem_maximalIdeal.ModularCurve IsLocalRing ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_eq_spec_map_comp_iotaFin_or_iotaInf_of_mem_maximalIdeal.ModularCurve.IgusaScheme"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme.jInvChartInf IgusaScheme IgusaScheme.ιFin IgusaScheme.ιInf"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "chartAlgFin chartAlgInf chartAlgMid jInvChartInf inclInf isLocalization_away_inclInf XInf fFin fInf ιFin ιInf mem_range_ιFin_or_mem_range_ιInf"
namespace CoverPole
p2m_open "ModularCurve.IgusaScheme ModularCurve"

universe u

theorem pushout_inl_eq_inr_iff {U X Y : Scheme.{u}} (f : U ⟶ X) (g : U ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] (x : X) (y : Y) :
    (pushout.inl f g).base x = (pushout.inr f g).base y ↔
      ∃ w : U, f.base w = x ∧ g.base w = y := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span f g)
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x) (xj := y)).mp h
    rcases k with (_ | _ | _)
    · have hfi : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
      have hfj : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
      subst hfi hfj
      exact ⟨w, by simp at h₁; exact h₁, by simp at h₂; exact h₂⟩
    · change WidePushoutShape.Hom (some WalkingPair.left) (some WalkingPair.right) at fj
      rcases fj with ⟨⟩
    · change WidePushoutShape.Hom (some WalkingPair.right) (some WalkingPair.left) at fi
      rcases fi with ⟨⟩
  · rintro ⟨w, rfl, rfl⟩
    change (f ≫ pushout.inl f g).base w = (g ≫ pushout.inr f g).base w
    rw [pushout.condition]

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

theorem range_fInf_base : Set.range (fInf N ℓ).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf N ℓ) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgInf N ℓ))) :
      Set (PrimeSpectrum (chartAlgInf N ℓ))) := by
  letI := (inclInf N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf N ℓ
  rw [← PrimeSpectrum.localization_away_comap_range (chartAlgMid N ℓ) (jInvChartInf N ℓ),
    Spec.map_base]
  rfl

theorem ιInf_base_mem_range_ιFin_iff (xi : XInf N ℓ) :
    (ιInf N ℓ).base xi ∈ Set.range (ιFin N ℓ).base ↔ jInvChartInf N ℓ ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fInf_base, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (pushout_inl_eq_inr_iff (fFin N ℓ) (fInf N ℓ) x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(fFin N ℓ).base w, (pushout_inl_eq_inr_iff (fFin N ℓ) (fInf N ℓ) _ _).mpr ⟨w, rfl, rfl⟩⟩

theorem coverPole {A : Type} [CommRing A] [IsLocalRing A]
    (f : Spec (CommRingCat.of A) ⟶ ModularCurve.IgusaScheme N ℓ) :
    (∃ α : ↥(chartAlgFin N ℓ) →+* A,
        f = Spec.map (CommRingCat.ofHom α) ≫ ModularCurve.IgusaScheme.ιFin N ℓ) ∨
      (∃ α : ↥(chartAlgInf N ℓ) →+* A,
        f = Spec.map (CommRingCat.ofHom α) ≫ ModularCurve.IgusaScheme.ιInf N ℓ ∧
          α (ModularCurve.IgusaScheme.jInvChartInf N ℓ) ∈ IsLocalRing.maximalIdeal A) := by
  have key : ∀ {X : Scheme} (ι : X ⟶ ModularCurve.IgusaScheme N ℓ) [IsOpenImmersion ι],
      f.base (closedPoint A) ∈ Set.range ι.base → Set.range f.base ⊆ Set.range ι.base := by
    intro X ι _ hc
    rintro _ ⟨q, rfl⟩
    have hsp : f.base q ⤳ f.base (closedPoint A) :=
      (IsLocalRing.specializes_closedPoint q).map f.base.hom.continuous
    exact hsp.mem_open ι.isOpenEmbedding.isOpen_range hc
  by_cases h : f.base (closedPoint A) ∈ Set.range (ιFin N ℓ).base
  · left
    refine ⟨(Spec.preimage (IsOpenImmersion.lift (ιFin N ℓ) f (key _ h))).hom, ?_⟩
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  · right
    have h' : f.base (closedPoint A) ∈ Set.range (ιInf N ℓ).base :=
      (mem_range_ιFin_or_mem_range_ιInf N ℓ _).resolve_left h
    set g := IsOpenImmersion.lift (ιInf N ℓ) f (key _ h') with hg
    have hfac : g ≫ ιInf N ℓ = f := IsOpenImmersion.lift_fac _ _ _
    refine ⟨(Spec.preimage g).hom, ?_, ?_⟩
    · rw [CommRingCat.ofHom_hom, Spec.map_preimage, hfac]
    ·
      have hpt : f.base (closedPoint A) = (ιInf N ℓ).base (g.base (closedPoint A)) := by
        rw [← hfac]; rfl
      have hj : jInvChartInf N ℓ ∈ (g.base (closedPoint A)).asIdeal := by
        by_contra hne
        exact h (hpt ▸ (ιInf_base_mem_range_ιFin_iff N ℓ _).mpr hne)
      have hgs : g = Spec.map (Spec.preimage g) := (Spec.map_preimage g).symm
      rw [hgs, Spec.map_base] at hj
      exact hj

end ModularCurve.IgusaScheme.CoverPole

end

open CategoryTheory AlgebraicGeometry _root_.ModularCurve _root_.P2MW.S_ModularCurve_IgusaScheme_exists_eq_spec_map_comp_iotaFin_or_iotaInf_of_mem_maximalIdeal.ModularCurve _root_.ModularCurve.IgusaScheme _root_.P2MW.S_ModularCurve_IgusaScheme_exists_eq_spec_map_comp_iotaFin_or_iotaInf_of_mem_maximalIdeal.ModularCurve.IgusaScheme in

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    {A : Type} [CommRing A] [IsLocalRing A]
    (f : Spec (CommRingCat.of A) ⟶ ModularCurve.IgusaScheme N ℓ) :
    (∃ α : ↥(chartAlgFin N ℓ) →+* A,
        f = Spec.map (CommRingCat.ofHom α) ≫ ModularCurve.IgusaScheme.ιFin N ℓ) ∨
      (∃ α : ↥(chartAlgInf N ℓ) →+* A,
        f = Spec.map (CommRingCat.ofHom α) ≫ ModularCurve.IgusaScheme.ιInf N ℓ ∧
          α (ModularCurve.IgusaScheme.jInvChartInf N ℓ) ∈ IsLocalRing.maximalIdeal A) :=
  ModularCurve.IgusaScheme.CoverPole.coverPole N ℓ f

end S_ModularCurve_IgusaScheme_exists_eq_spec_map_comp_iotaFin_or_iotaInf_of_mem_maximalIdeal
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_eq_spec_map_comp_iotaFin_or_iotaInf_of_mem_maximalIdeal (solution)
