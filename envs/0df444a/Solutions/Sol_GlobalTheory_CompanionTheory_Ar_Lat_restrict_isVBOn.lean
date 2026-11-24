-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Lat.restrict_isVBOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:17.549322+00:00
-- url     : https://prove2.me/submissions/270f51a5-65df-4004-bb4f-fdb8a08e1952

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_lat_restrict_comap_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
namespace GlobalTheory.CompanionTheory.Ar
namespace Lat
theorem _root_.solution : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E),
    L.IsVBOn T r V → (L.comap V.subtype).IsVBOn T r ⊤ ∧
      ∀ p ∈ T, ((L.comap V.subtype).map V.subtype) p = L p := by
  intro X Ω _ ξ E _ _ L T r V h
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨U, hpU, b, hb, hq⟩ := h p hp
    have hbV : ∀ i, b i ∈ V := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
    let b' : Fin r → V := fun i => ⟨b i, hbV i⟩
    have hval : (fun i => (b' i : E)) = b := rfl
    refine ⟨U, hpU, b', ?_, ?_⟩
    · apply Submodule.map_injective_of_injective (f := V.subtype) Subtype.val_injective
      have h1 : (Set.range b) = V.subtype '' Set.range b' := by
        rw [← Set.range_comp]; rfl
      rw [Submodule.map_span, ← h1, hb, Submodule.map_top, Submodule.range_subtype]
    · intro q hqT hqU
      obtain ⟨hli, hsp⟩ := hq q hqT hqU
      refine ⟨?_, ?_⟩
      · exact LinearIndependent.of_comp V.subtype hli
      · show (L q).comap (V.subtype.restrictScalars (regAt ξ q)) = _
        rw [hsp, ← hval]
        exact lat_restrict_comap_span V b'
  · intro p hp
    obtain ⟨U, hpU, b, hb, hq⟩ := h p hp
    obtain ⟨_, hsp⟩ := hq p hp hpU
    have hle : ∀ e ∈ L p, e ∈ V := by
      intro e he
      rw [hsp] at he
      have : Submodule.span (regAt ξ p) (Set.range b) ≤ V.restrictScalars (regAt ξ p) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hb ▸ Submodule.subset_span ⟨i, rfl⟩
      exact this he
    show ((L p).comap (V.subtype.restrictScalars (regAt ξ p))).map (V.subtype.restrictScalars (regAt ξ p)) = L p
    ext e
    simp only [Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro he
      exact ⟨⟨e, hle e he⟩, he, rfl⟩
end Lat
end GlobalTheory.CompanionTheory.Ar
