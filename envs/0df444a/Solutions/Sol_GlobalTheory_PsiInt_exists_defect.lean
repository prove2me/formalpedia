-- Prove2me | solution 1 for GlobalTheory.PsiInt.exists_defect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:01:23.458656+00:00
-- url     : https://prove2.me/submissions/5e253cc9-2fa0-4727-8ac9-17279af5d1f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecRelationDefect
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfSvalWhiskerRightEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_JKAppTopInjective
import Theorems.Thm_GlobalTheory_PsiInt_gs_scal
import Theorems.Thm_GlobalTheory_PsiInt_cT_zero
import Theorems.Thm_GlobalTheory_exists_sec_relation_defect
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.PsiInt
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.PsiInt
theorem _root_.solution
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (f : ∀ α, SecBT D (𝟙_ _) 1 α) (χ : D.X) (hg : (ga χ).IsGen) (p q : R) :
    ∃ d : SecBT D (𝟙_ _) 1 χ, ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J),
      Good D.P.L z J → sval d (lift (toUnit T) y).left z J =
        gs (𝟙 _) z ⊤ (scal T.hom q) * sval (f χ) (lift (toUnit T) y).left z J -
        gs (𝟙 _) z ⊤ (scal T.hom p) * ((val (ga χ) (toUnit T).left z J * rigV D z J).val *
          sval (f 0) (lift (toUnit T) (y * cT D T χ)).left z J) := by
  let Y : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let τ : Y ⟶ Y := lift (toUnit Y) (snd _ _ * cT D Y χ)
  have hF : FormEq (famφT D (𝟙_ _) χ) (DegPre.famε 1)
      (Sum.elim (fun k => τ.left ≫ famφT D (𝟙_ _) 0 k)
        (fun k => (toUnit Y).left ≫ Sum.elim (fun _ : PUnit => (D.c χ).left) (fun _ : PUnit => eSec D.P.A) k))
      (Sum.elim (DegPre.famε 1) (Sum.elim (fun _ => -1) (fun _ => 1))) := by
    intro U _ h
    have e₁ : τ.left ≫ famφT D (𝟙_ _) 0 1 = famφT D (𝟙_ _) χ 1 := by
      change (τ ≫ (snd _ _ * cT D Y 0)).left = (snd _ _ * cT D Y χ).left
      rw [cT_zero, _root_.mul_one, lift_snd]
    have e₂ : τ.left ≫ famφT D (𝟙_ _) 0 2 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ cT D Y 0).left = (1 : Y ⟶ D.P.A).left
      rw [cT_zero, MonObj.comp_one]
    have e₃ : τ.left ≫ famφT D (𝟙_ _) 0 3 = famφT D (𝟙_ _) χ 3 := by
      change (τ ≫ (1 : Y ⟶ D.P.A)).left = (1 : Y ⟶ D.P.A).left
      rw [MonObj.comp_one]
    have e₄ : (toUnit Y).left ≫ (D.c χ).left = famφT D (𝟙_ _) χ 2 := rfl
    have e₅ : (toUnit Y).left ≫ eSec D.P.A = famφT D (𝟙_ _) χ 3 := rfl
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_four,
      e₁, e₂, e₃, e₄, e₅]
    simp [DegPre.famε, _root_.mul_assoc]
  obtain ⟨d, hd⟩ := exists_sec_relation_defect Y.left D.P.A.left Y.left D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ τ.left
    (f 0) (f χ) (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (ga χ) D.rig) (toUnit Y).left)
    (scal Y.hom p) (scal Y.hom q)
    (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hg D.rig_gen) _) hF
  refine ⟨d, fun T y z J hJ => ?_⟩
  have e₁ : (lift (toUnit T) y).left ≫ Y.hom = T.hom := Over.w _
  have e₂ : (lift (toUnit T) y).left ≫ τ.left = (lift (toUnit T) (y * cT D T χ)).left := by
    rw [← Over.comp_left]
    congr 1
    simp only [τ, comp_lift, MonObj.comp_mul, lift_snd, cT, ← Category.assoc]
    congr 2
    · exact toUnit_unique _ _
    · congr 1
      exact toUnit_unique _ _
  have e₃ : (lift (toUnit T) y).left ≫ (toUnit Y).left = (toUnit T).left := by
    rw [← Over.comp_left]
    exact congrArg _ (toUnit_unique _ _)
  rw [hd _ _ z J hJ, gs_scal, gs_scal Y.hom _ z p, e₁, e₂, val_pull hJ, e₃, val_mul hJ, mul_comm (sval (f 0) _ z J)]
  congr 5
end GlobalTheory.PsiInt
