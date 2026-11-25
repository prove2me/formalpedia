-- Prove2me | solution 1 for GlobalTheory.EndCalc.cmp_add_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:05:57.477803+00:00
-- url     : https://prove2.me/submissions/1d19bf43-b23e-4761-88ab-db5ecbead1fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniformizationEndomorphismOfLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UniformizationEndomorphismCalculus
import Theorems.Thm_GlobalTheory_EndCalc_Rep_mul
import Theorems.Thm_GlobalTheory_EndCalc_Rep_cub
import Theorems.Thm_GlobalTheory_EndCalc_Rep_cmp
import Theorems.Thm_GlobalTheory_EndCalc_Rep_unique
import Theorems.Thm_GlobalTheory_EndCalc_cmp_one
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul
import Theorems.Thm_GlobalTheory_Cartier_SecMaps_unique
import Theorems.Thm_GlobalTheory_TorusUnit_IsCharNear_unique
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_some
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffineLift
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_zero
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_symm_zeroOver
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_zeroOver
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_some
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_zero
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_symm_zeroOver



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.EndCalc
variable {R : Type} [CommRing R] [IsDomain R]
variable {D : DegPre R} {a a' a'' : D.P.A ⟶ D.P.A} {p p' p'' χ χ' χ'' : D.X} {T : Over (Spec (CommRingCat.of R))}
  {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι}
namespace GlobalTheory.EndCalc
theorem _root_.solution (hG : GlobalFnsSt) [IsMonHom a] {u : CmpGen D a p χ} (hu : Normd u)
    (hJ : Good D.P.L z J) (x y : T ⟶ D.P.A) :
    val u (x * y).left z J * th D z J (cP D T χ) (x ≫ a) (y ≫ a) =
      th D z J (cP D T p) x y * (val u x.left z J * val u y.left z J) := by
  have sj : Function.Surjective (D.P.A ⊗ D.P.A).hom.appTop.hom := by
    rw [← Over.w (snd D.P.A D.P.A)]
    exact surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2
  have h := ((Rep.cmp hu (fst _ _ * snd _ _)).mul (Rep.cub (cP D _ χ) (fst _ _ ≫ a) (snd _ _ ≫ a))).unique
    ((Rep.cub (cP D _ p) (fst _ _) (snd _ _)).mul ((Rep.cmp hu (fst _ _)).mul (Rep.cmp hu (snd _ _))))
    sj (lift 1 1) (by
      rw [MonObj.mul_comp, _root_.mul_assoc (cP D _ χ), _root_.mul_assoc (cP D _ p)]; abel)
    (fun y I hI => by
      have C : IsCub (th D (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
      rw [MonObj.comp_mul, lift_fst_assoc, lift_fst, lift_snd, _root_.mul_one, cmp_one hu hI, MonObj.one_comp,
        C.face₂, C.face₂]
      simp) (lift x y) hJ
  simpa only [MonObj.comp_mul, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, comp_cP] using h
end GlobalTheory.EndCalc
