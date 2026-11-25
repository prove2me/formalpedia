-- Prove2me | solution 1 for GlobalTheory.UU.BiLift.exists_defect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:42:11.344428+00:00
-- url     : https://prove2.me/submissions/987c9c74-0405-49d1-addf-e5366162a21e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsPullLam
import Theorems.Thm_GlobalTheory_UU_BiLift_prod_lam
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BiLift
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
namespace GlobalTheory.UU.BiLift
theorem _root_.solution {Y : Over S} (a b x : Y ⟶ G) {φ₁ φ₂ φ₃ : Fin 4 → (Y.left ⟶ G.left)}
    (h₁ : FormEq φ₁ Oε (lam (a * b) x) Oε) (h₂ : FormEq φ₂ Oε (lam a x) Oε) (h₃ : FormEq φ₃ Oε (lam b x) Oε)
    (s₁ : LB.Gen (LB.LinComb L.L φ₁ Oε)) (s₂ : LB.Gen (LB.LinComb L.L φ₂ Oε)) (s₃ : LB.Gen (LB.LinComb L.L φ₃ Oε))
    (g₁ : s₁.IsGen) (g₂ : s₂.IsGen) (g₃ : s₃.IsGen) :
    ∃ f : Γ(Y.left, ⊤)ˣ, ∀ (Z : Over S) (r : Z ⟶ Y) (z : Z.left) (J), Good L.L z J →
      val s₁ r.left z J = gm r.left z ⊤ f * (cubV c z J (r ≫ a) (r ≫ b) (r ≫ x) * val s₂ r.left z J * val s₃ r.left z J) := by
  obtain ⟨f, hf⟩ := TorusCoord.exists_ratio L.isLB (fun U _ h => by
      refine Eq.trans ?_ (DVR.prod_sum₂ (K := thK ⊕ Fin 4) (K' := Fin 4) (U := U) _
        (DVR.prod_sum₂ (K := thK) (K' := Fin 4) (U := U) _ (prod_cub a b x h) ((h₂ U h).trans (prod_lam a x h)))
        ((h₃ U h).trans (prod_lam b x h))).symm
      rw [h₁ U h, prod_lam]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) s₁ g₁
    (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b x)).left) s₂) s₃)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _) g₂) g₃)
  refine ⟨f, fun Z r z J hJ => (hf _ r.left z J hJ).trans (congrArg _ ?_)⟩
  exact (val_mul hJ _ _ _).trans (congrArg (· * _) ((val_mul hJ _ _ _).trans (congrArg (· * _) (val_cub c r hJ _ _ _))))
end GlobalTheory.UU.BiLift
