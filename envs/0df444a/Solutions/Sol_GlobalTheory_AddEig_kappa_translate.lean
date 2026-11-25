-- Prove2me | solution 1 for GlobalTheory.AddEig.kappa_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:49:08.500485+00:00
-- url     : https://prove2.me/submissions/2b931153-c2a2-4d82-930c-c557fb85fa00

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
import Theorems.Thm_GlobalTheory_AddEig_gen_ratio
import Theorems.Thm_GlobalTheory_AddEig_surj_fst_sq
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
import Theorems.Thm_GlobalTheory_ThetaLin_gs_scal_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
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
theorem _root_.solution (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) {F : Type} [CommRing F]
    (p : Spec (CommRingCat.of F) ⟶ S)
    (κ : LB.Gen (LB.LinComb P.L (K := Fin 4)
      ![(snd (Over.mk p) (P.A ⊗ P.A) ≫ fst P.A P.A).left, (snd (Over.mk p) (P.A ⊗ P.A) ≫ snd P.A P.A).left,
        (snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A)).left,
        (snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹)).left] ![2, 2, -1, -1])) (hκ : κ.IsGen)
    (c : Over.mk p ⟶ P.A) (hc : c ^ 2 = 1)
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (Over.mk p) P.A).left, (translPt P.A c).left] ![2, -2]))
    (hα : α.IsGen) :
    ∃ r : F, ∀ (T : Over S) (ρ : T ⟶ Over.mk p) (x y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      (val α (lift ρ x).left z J * val α (lift ρ y).left z J *
        val κ (lift ρ (lift ((ρ ≫ c) * x) ((ρ ≫ c) * y))).left z J).val =
      gs (𝟙 _) z ⊤ (scal (R := F) ρ.left r) * (val κ (lift ρ (lift x y)).left z J).val := by
  have := P.isAb.comm
  let a : Over.mk p ⊗ (P.A ⊗ P.A) ⟶ P.A := snd _ _ ≫ fst _ _
  let b : Over.mk p ⊗ (P.A ⊗ P.A) ⟶ P.A := snd _ _ ≫ snd _ _
  let d : Over.mk p ⊗ (P.A ⊗ P.A) ⟶ P.A := fst _ _ ≫ c
  have hd : d * d = 1 := by
    rw [← MonObj.comp_mul, ← pow_two, hc, MonObj.comp_one]
  have tp : translPt P.A c = (fst _ P.A ≫ c) * snd _ P.A := rfl
  obtain ⟨r, hr⟩ := gen_ratio (F := F) P.isLB (fun U _ h => by
      have e₁ : lift (fst _ _) a ≫ translPt P.A c = d * a := by
        rw [tp, MonObj.comp_mul, lift_fst_assoc, lift_snd]
      have e₂ : lift (fst _ _) b ≫ translPt P.A c = d * b := by
        rw [tp, MonObj.comp_mul, lift_fst_assoc, lift_snd]
      have e₃ : lift (fst _ _) (lift (d * a) (d * b)) ≫ snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A) =
          snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A) := by
        rw [lift_snd_assoc, MonObj.comp_mul, lift_fst, lift_snd, MonObj.comp_mul, _root_.mul_mul_mul_comm, hd,
          _root_.one_mul]
      have e₄ : lift (fst _ _) (lift (d * a) (d * b)) ≫ snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹) =
          snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹) := by
        rw [lift_snd_assoc, MonObj.comp_mul, lift_fst, GrpObj.comp_inv, lift_snd, MonObj.comp_mul, GrpObj.comp_inv,
          _root_.mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_four,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ← Over.comp_left, e₁, e₂, e₃, e₄, lift_snd,
        lift_snd_assoc, lift_fst]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      abel)
    (fst (Over.mk p) (P.A ⊗ P.A)).left (surj_fst_sq hG P.isAb _)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ hα (lift (fst _ _) a).left) (DVR.pullGen_isGen _ _ _ _ hα (lift (fst _ _) b).left))
      (DVR.pullGen_isGen _ _ _ _ hκ (lift (fst _ _) (lift (d * a) (d * b))).left)) hκ
  refine ⟨r, fun T ρ x y z J hJ => ?_⟩
  have := hr _ (lift ρ (lift x y)).left z J hJ
  rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, ThetaLin.gs_scal_comp] at this
  simp only [← Over.comp_left] at this
  have f₁ : lift ρ (lift x y) ≫ lift (fst _ _) a = lift ρ x := by simp [a]
  have f₂ : lift ρ (lift x y) ≫ lift (fst _ _) b = lift ρ y := by simp [b]
  have f₃ : lift ρ (lift x y) ≫ lift (fst _ _) (lift (d * a) (d * b)) =
      lift ρ (lift ((ρ ≫ c) * x) ((ρ ≫ c) * y)) := by simp [a, b, d, MonObj.comp_mul]
  rw [f₁, f₂, f₃, lift_fst] at this
  exact this
end GlobalTheory.AddEig
