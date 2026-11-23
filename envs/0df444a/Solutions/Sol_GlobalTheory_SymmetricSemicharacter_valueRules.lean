-- Prove2me | solution 1 for GlobalTheory.SymmetricSemicharacter.valueRules
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:01.988479+00:00
-- url     : https://prove2.me/submissions/c583e879-28c4-415d-a914-00fd4400f4ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.SymmetricSemicharacter
open CubeValues
namespace GlobalTheory.SymmetricSemicharacter
theorem _root_.solution : ValueRules := by
  intro X x
  have h1 : ∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U := fun U =>
    ⟨fun h => h (x := (default : PrimeSpectrum ℂ)) trivial, fun h p _ => by
      have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      subst this
      exact h⟩
  refine ⟨h1, fun U h => ?_, fun U V h f hV => ?_, fun Y φ U f => ?_, fun U f => ?_,
    fun p hp U a h => ?_⟩
  · exact ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom,
      fun f => by simp only [valAt', dif_pos h, valAt]; rfl⟩
  · have hU : ⊤ ≤ x ⁻¹ᵁ U := fun p hp => h (hV hp)
    simp only [valAt', dif_pos hV, dif_pos hU, valAt]
    congr 1
    exact congr($(Scheme.Hom.map_appLE x hV (homOfLE h).op).hom f)
  · by_cases h : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U
    · have h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := h
      simp only [valAt', dif_pos h, dif_pos h', valAt]
      congr 1
    · have h' : ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := h
      simp only [valAt', dif_neg h, dif_neg h']
  · by_cases h : ⊤ ≤ x ⁻¹ᵁ U
    · have e : (Sp ℂ).basicOpen ((x.appLE U ⊤ h).hom f) = x ⁻¹ᵁ X.basicOpen f := by
        rw [Scheme.basicOpen_appLE, top_inf_eq]
      simp only [valAt', dif_pos h, valAt]
      rw [← e]
      generalize (x.appLE U ⊤ h).hom f = s
      obtain ⟨a, rfl⟩ : ∃ a : ℂ, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a = s :=
        ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom s, by simp⟩
      have ea : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) = a := by simp
      rw [ea]
      constructor
      · rintro k rfl
        rw [map_zero, Scheme.basicOpen_zero] at k
        exact k (x := (default : PrimeSpectrum ℂ)) trivial
      · intro k
        exact (Scheme.basicOpen_of_isUnit _ ((isUnit_iff_ne_zero.2 k).map _)).ge
    · simp only [valAt', dif_neg h, ne_eq, not_true, iff_false]
      exact fun k => h fun p hp => X.basicOpen_le f (k hp)
  · simp only [valAt', dif_pos h, valAt, constFn]
    have := congr($(Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h).hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
    simp only [hp, CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    have e : ∀ k, Scheme.Hom.appLE (𝟙 (Sp ℂ)) ⊤ ⊤ k = 𝟙 _ := fun k => by
      rw [← Scheme.Hom.id_app]
      exact (Scheme.Hom.app_eq_appLE (𝟙 (Sp ℂ)) (U := ⊤)).symm
    rw [e]
    simp
end GlobalTheory.SymmetricSemicharacter
