-- Prove2me | solution 1 for GlobalTheory.UU.famFE_one_of_psiRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:13:37.585004+00:00
-- url     : https://prove2.me/submissions/0f2b01cb-2399-4e6d-ac7f-23f3119249ab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FamFEOneOfPsiRel
import Theorems.Thm_GlobalTheory_UU_val_famMult_one
import Theorems.Thm_GlobalTheory_UU_uVal_one
import Theorems.Thm_GlobalTheory_UU_sval_of_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff


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
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ s : Raw D F 1) (c : F), PsiRel D (TF (R := R) F) s₀ → (∀ α j, (s α).f j = DegPre.constBF D F c _ * (s₀ α).f j) → DegPre.FamFE D F 1 s := by
  intro hG R _ _ D F _ _ s₀ s c hψ hs mu α u hu hc
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  have e₃ := (gen_fe hG 1 mu α).2 u hu hc _ (𝟙 _) y J hJ
  rw [uVal_one D F _ _ _ hJ, _root_.one_mul, Category.id_comp, Over.id_left] at e₃
  have e₄ := val_famMult_one D F (fst (TF (R := R) F) D.P.A) hJ mu α
  let κ : DegPre.BF D F ⟶ TK R := Over.homMk ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) F) D.P.A)))
  have e₁ := hψ (α + 1 • mu) _ (fst _ _) κ (snd _ _) y J hJ
  have e₂ := hψ α _ (fst _ _) κ (snd _ _ * cT D _ mu) y J hJ
  have q : snd (TF (R := R) F) D.P.A * cT D _ mu * cT D _ α = snd (TF (R := R) F) D.P.A * cT D _ (α + 1 • mu) := by
    rw [one_nsmul, add_comm, _root_.mul_assoc]
    exact congrArg _ (cPoint_add D _ mu α).symm
  rw [q] at e₂
  rw [lift_fst_snd, Over.id_left] at e₁
  have e₅ : val (D.psi (α + 1 • mu)) κ.left y J =
      val (DegPre.famMult D F 1 mu α) (fst (TF (R := R) F) D.P.A).left y J * val (D.psi α) κ.left y J := by
    rw [one_nsmul, add_comm]; exact e₄.symm
  have t : (DegPre.trF D F mu).left ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R) F) D.P.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trF D F mu ≫ fst (TF (R := R) F) D.P.A = _)
  have e₁' : sval (s₀ (α + 1 • mu)) (𝟙 _) y J = _ := e₁
  have e₂' : sval (s₀ α) (DegPre.trF D F mu).left y J = _ := e₂
  rw [sval_of_const D F s₀ s c hs _ _ y hJ, sval_of_const D F s₀ s c hs _ _ y hJ, Category.id_comp, Category.id_comp, t,
    e₁', e₂', e₃, e₅]
  simp only [Units.val_mul]
  ring
end GlobalTheory.UU
