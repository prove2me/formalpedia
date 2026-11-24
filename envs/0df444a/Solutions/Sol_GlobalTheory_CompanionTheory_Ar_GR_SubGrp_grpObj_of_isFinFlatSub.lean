-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.GR.SubGrp.grpObj_of_isFinFlatSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:51:10.33019+00:00
-- url     : https://prove2.me/submissions/5a4f52c2-98e9-48b8-9e0d-80fbed47798c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFlatSubgroupScheme
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_GR_SubGrp_exists_grpObj_of_mono
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_GR_SubGrp_affine_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_GR_SubGrp_affine_one
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_GR_SubGrp_affine_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_GR_SubGrp_mono_of_isFinFlatSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.GR GlobalTheory.CompanionTheory.Ar.GR.SubGrp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
variable {R : Type} [CommRing R]
variable {A : Over (Spec (CommRingCat.of R))} [GrpObj A] {B : Type} [CommRing B] [Algebra R B]
  {h : sp (R₀ := R) B ⟶ A}
namespace GlobalTheory.CompanionTheory.Ar.GR.SubGrp
theorem _root_.solution (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (B : Type)
    [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A) (H : IsFinFlatSub A B h) :
    ∃ _ : GrpObj (sp (R₀ := R) B), IsMonHom h ∧ Mono h := by
  have hmono := mono_of_isFinFlatSub H
  haveI : IsAffine (sp (R₀ := R) B).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
    inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (sp (R₀ := R) B ⊗ sp (R₀ := R) B).left :=
    inferInstanceAs (IsAffine (pullback (sp (R₀ := R) B).hom (sp (R₀ := R) B).hom))
  obtain ⟨m, hm⟩ := affine_mul H (fst _ _) (snd _ _)
  obtain ⟨e, he⟩ := affine_one H (T := 𝟙_ _)
  obtain ⟨i, hi⟩ := affine_inv H (𝟙 _)
  rw [Category.id_comp] at hi
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono h m e i hm he hi
  exact ⟨G, hG, hmono⟩
end GlobalTheory.CompanionTheory.Ar.GR.SubGrp
