-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.isMonHom_iff_of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:50:32.412747+00:00
-- url     : https://prove2.me/submissions/05e2129a-649c-48a9-bf4a-7f0513802f4d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
import Theorems.Thm_GlobalTheory_FieldBaseChange_pullback_map_left_fst
import Theorems.Thm_GlobalTheory_FieldBaseChange_isMonHom_of_pullback
import Theorems.Thm_GlobalTheory_FunDescent_hom_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.FieldBaseChange
variable {U S : Scheme.{0}} (j : U ⟶ S)
variable {j}
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution [Flat j] [Surjective j] {G H : Over S} [GrpObj G] [GrpObj H]
    {G' H' : Over U} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hG : IsGrpPullback G' G j φ) (hH : IsGrpPullback H' H j ψ) (f' : G' ⟶ H') (f : G ⟶ H)
    (hf : φ ≫ f.left = f'.left ≫ ψ) : IsMonHom f' ↔ IsMonHom f := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G j) hG
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hH (isGrpPullback_pullback H j)
  have e : (Over.pullback j).map f = a.hom ≫ f' ≫ b.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [pullback_map_left_fst, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ← hf,
        ← Category.assoc, ha']
    · exact (Over.w _).trans (Over.w _).symm
  constructor
  · intro h
    exact isMonHom_of_pullback j f (by rw [e]; infer_instance)
  · intro h
    have e' : f' = a.inv ≫ (Over.pullback j).map f ≫ b.inv := by simp [e]
    rw [e']
    infer_instance
end GlobalTheory.FieldBaseChange
