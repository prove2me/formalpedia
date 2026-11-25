-- Prove2me | solution 1 for GlobalTheory.ThetaLin.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:53:20.998045+00:00
-- url     : https://prove2.me/submissions/9f3b993d-00f4-4e25-bf16-037296325477

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_FinrankComplexReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalOfIsTwistPull
import Theorems.Thm_GlobalTheory_ThetaLin_exists_linearEquiv
import Theorems.Thm_GlobalTheory_ThetaLin_sval_of_isTwistPull
import Theorems.Thm_GlobalTheory_ThetaLin_isTwistPull_of_sval
import Theorems.Thm_GlobalTheory_ThetaLin_lift_translT
import Theorems.Thm_GlobalTheory_ThetaLin_translT_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val


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
noncomputable section
open GlobalTheory GlobalTheory.ThetaLin
namespace GlobalTheory.ThetaLin
theorem _root_.solution : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (k : ℕ) (θ : ThetaGrp P.A P.L (k : ℤ) (Over.mk p)), ∃ Φ : EA P p k ≃ₗ[F] EA P p k, (∀ v, IsActOf P.A P.L (k : ℤ) θ v.sec (Φ v).sec) ∧ (∀ v v', IsActOf P.A P.L (k : ℤ) θ v v' → v' = (Φ (SecMod.mk _ v)).sec) ∧ ∀ (v : EA P p k) (T : Over S) (ρ : T ⟶ Over.mk p) (x : T ⟶ P.A) (z : T.left) (J), Good P.L z J → sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((k : ℕ) : ℤ)) (Φ v).sec (lift ρ x).left z J = (val (L := P.L) (φ := ![(snd (Over.mk p) P.A).left, (translPt P.A θ.pt).left]) (ε := ![(k : ℤ), -(k : ℤ)]) θ.φ (lift ρ x).left z J).val * sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((k : ℕ) : ℤ)) v.sec (lift ρ ((ρ ≫ θ.pt) * x)).left z J := by
  intro S P F _ p k θ
  obtain ⟨Φ, hΦ⟩ := exists_linearEquiv (F := F) P.isLB (fst (Over.mk p) P.A).left (snd (Over.mk p) P.A).left
    (translPt P.A θ.pt).left (translT P.A θ.pt).left (translT P.A θ.pt⁻¹).left
    (by rw [← Over.comp_left, translT, lift_snd])
    (by rw [← Over.comp_left, translT_comp _ _ _ (mul_inv_cancel _), Over.id_left])
    (by rw [← Over.comp_left, translT_comp _ _ _ (inv_mul_cancel _), Over.id_left])
    (((Over.comp_left _ _ _ _ _).symm.trans (by rw [translT, lift_fst]))) (k : ℤ) θ.φ θ.isGen
  refine ⟨Φ, fun v => isTwistPull_of_sval P.A P.isLB θ.isGen fun y J hJ => hΦ v _ _ y J hJ, fun v v' h => ?_,
    fun v T ρ x z J hJ => ?_⟩
  · exact DVR.SecOps.sec_ext (sec_ext_val P.isLB fun y J hJ =>
      (sval_of_isTwistPull P.A h (𝟙 _) y hJ).trans (hΦ (SecMod.mk _ v) _ _ y J hJ).symm)
  · refine (hΦ v _ _ z J hJ).trans ?_
    rw [← Over.comp_left, lift_translT]
    rfl
end GlobalTheory.ThetaLin
