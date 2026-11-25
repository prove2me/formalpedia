-- Prove2me | solution 1 for GlobalTheory.AddEig.surj_fst_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:04:37.968035+00:00
-- url     : https://prove2.me/submissions/5000daeb-9306-4c9c-b19f-6df84ec976d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalOfIsTwistPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSumTmulLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdditionTensorEigenDiagonalThetaOrderTwo
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.appLE_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_appLE
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.AddEig
namespace GlobalTheory.AddEig
theorem _root_.solution {S : Scheme.{0}} (hG : GlobalFnsSt) {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    (T : Over S) : Function.Surjective (fst T (A ⊗ A)).left.appTop.hom := by
  let m : T ⊗ (A ⊗ A) ⟶ A ⊗ (A ⊗ T) := lift (snd _ _ ≫ fst _ _) (lift (snd _ _ ≫ snd _ _) (fst _ _))
  let n : A ⊗ (A ⊗ T) ⟶ T ⊗ (A ⊗ A) := lift (snd _ _ ≫ snd _ _) (lift (fst _ _) (snd _ _ ≫ fst _ _))
  have e₀ : m ≫ snd _ _ ≫ snd _ _ = fst T (A ⊗ A) := by simp [m]
  have e₁ : m ≫ n = 𝟙 _ := by ext <;> simp [m, n]
  rw [← e₀, Over.comp_left, Over.comp_left]
  refine surj_comp (fun a => ⟨n.left.appTop.hom a, ?_⟩) (surj_comp (surj_snd hG hA _) (surj_snd hG hA T))
  have e : m.left ≫ n.left = 𝟙 _ := by rw [← Over.comp_left, e₁]; rfl
  have := congrArg (fun q => (Scheme.Hom.appTop q).hom a) e
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.id_appTop,
    CommRingCat.hom_id, RingHom.id_apply] using this
end GlobalTheory.AddEig
