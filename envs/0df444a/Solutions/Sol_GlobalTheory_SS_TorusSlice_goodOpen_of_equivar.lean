-- Prove2me | solution 1 for GlobalTheory.SS.TorusSlice.goodOpen_of_equivar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:23.292975+00:00
-- url     : https://prove2.me/submissions/b1ab4b3e-1b87-4441-a247-90763e4ee707

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnits
import Theorems.Thm_GlobalTheory_SS_TorusSlice_isPullback_whiskerLeft
import Theorems.Thm_GlobalTheory_SS_TorusSlice_ch_eq
import Theorems.Thm_GlobalTheory_SS_TorusSlice_ch_mul
import Theorems.Thm_GlobalTheory_SS_TorusSlice_ch_comp
import Theorems.Thm_GlobalTheory_SS_TorusSlice_appLE_comp_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.TorusSlice
variable {S : Scheme.{0}}
variable {X : Type} [AddCommGroup X]
namespace GlobalTheory.SS.TorusSlice
theorem _root_.solution {G P : Over S} [GrpObj G] (i : splitTorus S X ⟶ G) (a : P ⟶ G) [IsOpenImmersion a.left]
    [IsAffine P.left] (τ : P ⟶ splitTorus S X) (hτ : Equivar i a τ)
    (hs : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (p : Z ⟶ P), ∃ p' : Z ⟶ P, p' ≫ a = (t ≫ i) * (p ≫ a)) :
    GoodOpen i (a.left ''ᵁ ⊤) := by
  have hV : ∀ x, x ∈ a.left ''ᵁ ⊤ ↔ x ∈ Set.range a.left := fun x => by
    rw [Scheme.Hom.image_top_eq_opensRange]; rfl
  have hm : Mono a := Over.mono_of_mono_left a
  refine ⟨(isAffineOpen_top _).image_of_isOpenImmersion _, fun z hz => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := (hV _).1 hz
    obtain ⟨w, rfl, -⟩ := Scheme.exists_preimage_of_isPullback
      ((isPullback_whiskerLeft (splitTorus S X) a).map (Over.forget S)) z y hy.symm
    obtain ⟨p', hp'⟩ := hs _ (fst (splitTorus S X) P) (snd _ _)
    refine (hV _).2 ⟨p'.left w, ?_⟩
    have : p' ≫ a = (splitTorus S X ◁ a) ≫ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G) := by
      simp [hp', MonObj.comp_mul]
    exact congrArg (fun f : splitTorus S X ⊗ P ⟶ G => f.left w) this
  · have h0 : ⊤ ≤ a.left ⁻¹ᵁ (a.left ''ᵁ ⊤) := (a.left.preimage_image_eq ⊤).ge
    have hψ : ∀ x, (a.left.appLE _ ⊤ h0).hom ((a.left.appIso ⊤).inv.hom x) = x := fun x => by
      rw [← Scheme.Hom.appIso_hom']
      exact congrArg (fun φ => φ.hom x) (a.left.appIso ⊤).inv_hom_id
    have lift : ∀ {Z : Over S} (g : Z ⟶ G), ⊤ ≤ g.left ⁻¹ᵁ (a.left ''ᵁ ⊤) → ∃ p : Z ⟶ P, g = p ≫ a := by
      intro Z g h
      have hr : Set.range g.left ⊆ Set.range a.left := by
        rintro _ ⟨z, rfl⟩
        exact (hV _).1 (h (Set.mem_univ z))
      refine ⟨Over.homMk (IsOpenImmersion.lift a.left g.left hr) ?_, ?_⟩
      · rw [← Over.w a, IsOpenImmersion.lift_fac_assoc, Over.w]
      · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ hr).symm
    refine ⟨(Units.map (a.left.appIso ⊤).inv.hom.toMonoidHom).comp (splitTorusPointsEquiv S X P τ),
      fun χ Z t g h₁ h₂ => ?_⟩
    obtain ⟨p, hp⟩ := lift g h₂
    obtain ⟨p', hp'⟩ := lift _ h₁
    rw [appLE_comp_top p' a _ hp' _ h₁ h0, appLE_comp_top p a _ hp _ h₂ h0]
    have e : (a.left.appLE _ ⊤ h0).hom (((Units.map (a.left.appIso ⊤).inv.hom.toMonoidHom).comp
        (splitTorusPointsEquiv S X P τ)) (Multiplicative.ofAdd χ)).val = ch τ χ := by
      rw [ch_eq]; exact hψ _
    rw [e, ← ch_comp, ← ch_comp, hτ Z t p p' (by rw [← hp', hp]), ch_mul]
    rfl
end GlobalTheory.SS.TorusSlice
