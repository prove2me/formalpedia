-- Prove2me | solution 1 for GlobalTheory.SemiRigid.abelian_tensor_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:53:07.303825+00:00
-- url     : https://prove2.me/submissions/4faf9d1a-e2dc-4983-89f7-8b1cf82589b1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqCompSectionOfSurjectiveAppTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SurjectiveAppOfIsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GroupRingHomConstOfLaurent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Theorems.Thm_GlobalTheory_SemiRigid_globalFns
import Theorems.Thm_GlobalTheory_eq_comp_section_of_local_rigidity
import Theorems.Thm_GlobalTheory_local_rigidity
import Theorems.Thm_GlobalTheory_surjective_app_of_isAbelianScheme
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_isAb_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SemiRigid
open SplitTorus
variable {K : Type} [Field K]
namespace GlobalTheory.SemiRigid
theorem _root_.solution {B H : Over (Spec (.of K))} [GrpObj B] [GrpObj H]
    (hB : IsAbelianScheme B) [IsSeparated H.hom] (W : Over (Spec (.of K))) [ConnectedSpace W.left]
    (w : 𝟙_ _ ⟶ W) (g : B ⊗ W ⟶ H) (h₁ : lift 1 (𝟙 W) ≫ g = 1)
    (h₂ : lift (𝟙 B) (toUnit _ ≫ w) ≫ g = 1) : g = 1 := by
  have := hB.smooth
  have := hB.proper
  let ε : W ⟶ B ⊗ W := lift 1 (𝟙 W)
  let j : B ⟶ B ⊗ W := lift (𝟙 B) (toUnit _ ≫ w)
  have hεp : ε.left ≫ (snd B W).left = 𝟙 W.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have hsm : Smooth (snd B W).left := by
    change Smooth (pullback.snd B.hom W.hom); infer_instance
  have huc : UniversallyClosed (snd B W).left := by
    change UniversallyClosed (pullback.snd B.hom W.hom); infer_instance
  have hsurj : ∀ V : W.left.Opens, Function.Surjective ((snd B W).left.app V).hom := fun V ↦
    surjective_app_of_isAbelianScheme globalFns _ (Out.TLinPf.isAb_pullback W.hom B hB) V
  have hw : w.left ≫ W.hom = 𝟙 _ := Over.w w
  have hpb : IsPullback j.left B.hom (snd B W).left w.left := by
    have hr : IsPullback (fst B W).left (snd B W).left B.hom W.hom := .of_hasPullback B.hom W.hom
    refine IsPullback.of_right ?_ ?_ hr
    · have : j.left ≫ (fst B W).left = 𝟙 B.left := by
        rw [← Over.comp_left, lift_fst, Over.id_left]
      rw [this, hw]
      exact IsPullback.of_id_fst
    · rw [← Over.comp_left, lift_snd, Over.comp_left]
      rfl
  have key : g.left = (snd B W).left ≫ ε.left ≫ g.left := by
    refine eq_comp_section_of_local_rigidity (snd B W).left ε.left g.left W.hom H.hom hεp
      ((Over.w g).trans (Over.w (snd B W)).symm) (snd B W).left.isOpenMap
      (local_rigidity _ _ _ _ _ _ hεp huc hsurj) (fun s ↦ ?_) ?_
    · have : W.hom ⁻¹' {s} = Set.univ := Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
      rw [this]
      exact isPreconnected_univ
    intro s
    refine ⟨w.left s, (η[H] : 𝟙_ _ ⟶ H).left s, Subsingleton.elim _ _, ?_⟩
    intro x hx
    obtain ⟨z, rfl, rfl⟩ := Scheme.exists_preimage_of_isPullback hpb x s hx
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h₂, Hom.one_def, Over.comp_left,
      Scheme.Hom.comp_apply]
    rfl
  have key' : g = snd B W ≫ ε ≫ g := Over.OverMorphism.ext key
  rw [key', h₁, MonObj.comp_one]
end GlobalTheory.SemiRigid
