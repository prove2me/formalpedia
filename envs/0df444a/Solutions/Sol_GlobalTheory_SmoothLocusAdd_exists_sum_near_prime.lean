-- Prove2me | solution 1 for GlobalTheory.SmoothLocusAdd.exists_sum_near_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:33:32.689344+00:00
-- url     : https://prove2.me/submissions/e7033ac5-81a2-442d-bbeb-76dfad3f289c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfLocallyRel
import Theorems.Thm_GlobalTheory_SmoothLocusAdd_exists_sum_of_isUnit
import Theorems.Thm_GlobalTheory_AddLaw_addXYZ_equiv_add
import Theorems.Thm_GlobalTheory_AddLaw_addXYZ_ne_zero_or_diagXYZ_ne_zero
import Theorems.Thm_GlobalTheory_AddLaw_diagXYZ_equiv_add
import Theorems.Thm_GlobalTheory_AddLaw_map_diagXYZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  AlgebraicGeometry
noncomputable section
open GlobalTheory GlobalTheory.SmoothLocusAdd
open GlobalTheory.WeierstrassCurve
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
open WeierstrassCurve.Projective
namespace GlobalTheory.SmoothLocusAdd
theorem _root_.solution {C : Type} [CommRing C] [_root_.IsReduced C] (ρ : R →+* C)
    {P Q : Fin 3 → C} (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (nP : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ P))
    (nQ : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ Q)) (z : Spec (.of C)) :
    ∃ (V : Scheme.{0}) (j : V ⟶ Spec (.of C)) (_ : IsOpenImmersion j) (f : V ⟶ scheme W),
      z ∈ Set.range j ∧ f ≫ toSpec W = j ≫ Spec.map (CommRingCat.ofHom ρ) ∧
        ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ V),
          IsSumAt W (x ≫ j ≫ ptHom W ρ P hP) (x ≫ j ≫ ptHom W ρ Q hQ) (x ≫ f) := by
  have key : ∃ (S : Fin 3 → C) (i : Fin 3), S i ∉ z.asIdeal ∧
      ∀ (k : Type) [Field k] (φ : C →+* k), φ ∘ S ≠ 0 →
        φ ∘ S ≈ (W.map (φ.comp ρ)).toProjective.add (φ ∘ P) (φ ∘ Q) := by
    have eA : ∀ (k : Type) [Field k] (φ : C →+* k),
        (W.map (φ.comp ρ)).toProjective.addXYZ (φ ∘ P) (φ ∘ Q) =
          φ ∘ (W.map ρ).toProjective.addXYZ P Q := fun k _ φ =>
      map_addXYZ (W' := (W.map ρ).toProjective) φ P Q
    have eD : ∀ (k : Type) [Field k] (φ : C →+* k),
        AddLaw.diagXYZ (W.map (φ.comp ρ)).toProjective (φ ∘ P) (φ ∘ Q) =
          φ ∘ AddLaw.diagXYZ (W.map ρ).toProjective P Q := fun k _ φ =>
      AddLaw.map_diagXYZ (W := (W.map ρ).toProjective) φ P Q
    have := z.isPrime
    let κ := algebraMap C z.asIdeal.ResidueField
    rcases AddLaw.addXYZ_ne_zero_or_diagXYZ_ne_zero (nP _ κ) (nQ _ κ) with h | h
    · rw [eA] at h
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      refine ⟨_, i, fun hm => hi (Ideal.algebraMap_residueField_eq_zero.mpr hm), fun k _ φ h => ?_⟩
      rw [← eA] at h ⊢
      exact AddLaw.addXYZ_equiv_add (nP k φ) (nQ k φ) h
    · rw [eD] at h
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      refine ⟨_, i, fun hm => hi (Ideal.algebraMap_residueField_eq_zero.mpr hm), fun k _ φ h => ?_⟩
      rw [← eD] at h ⊢
      exact AddLaw.diagXYZ_equiv_add (nP k φ) (nQ k φ) h
  obtain ⟨S, i, hi, hS⟩ := key
  let C' := Localization.Away (S i)
  let g : C →+* C' := algebraMap C C'
  have : _root_.IsReduced C' := inferInstanceAs (_root_.IsReduced (Localization (.powers (S i))))
  obtain ⟨h, hsum⟩ := exists_sum_of_isUnit W (g.comp ρ) (S := g ∘ S) (hP.map_comp g)
    (hQ.map_comp g) (fun k _ φ => nP k (φ.comp g)) (fun k _ φ => nQ k (φ.comp g))
    (fun k _ φ => hS k (φ.comp g)) i (IsLocalization.Away.algebraMap_isUnit (S i))
  refine ⟨Spec (.of C'), Spec.map (CommRingCat.ofHom g),
    IsOpenImmersion.of_isLocalization (S i), ptHom W _ _ h, ?_, ?_, fun k _ x => ?_⟩
  · exact (PrimeSpectrum.localization_away_comap_range C' (S i)).ge hi
  · rw [ptHom_toSpec, ← Spec.map_comp, CommRingCat.ofHom_comp]
  · rw [SpecMap_ptHom, SpecMap_ptHom]
    exact hsum k x
end GlobalTheory.SmoothLocusAdd
