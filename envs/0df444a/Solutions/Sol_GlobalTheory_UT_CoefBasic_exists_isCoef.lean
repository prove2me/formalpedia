-- Prove2me | solution 1 for GlobalTheory.UT.CoefBasic.exists_isCoef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:51:04.866864+00:00
-- url     : https://prove2.me/submissions/1d08d601-e7ca-4511-ade4-9ba5442ce8ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFrameRatio
import Theorems.Thm_GlobalTheory_UT_CoefBasic_pt_eq
import Theorems.Thm_GlobalTheory_UT_CoefBasic_cst_eq
import Theorems.Thm_GlobalTheory_UT_CoefBasic_cstH_surj
import Theorems.Thm_GlobalTheory_UT_CoefBasic_exists_pt
import Theorems.Thm_P2M_GlobalTheory_UT_CoefBasic_exists_good__0c0484e460d1
import Theorems.Thm_GlobalTheory_UT_CoefBasic_val_tr
import Theorems.Thm_GlobalTheory_UT_CoefBasic_sval_tr
import Theorems.Thm_GlobalTheory_UT_CoefBasic_prod_line
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_fam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pt_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.CoefBasic
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UT.CoefBasic
theorem _root_.solution {k : ℕ} (g : GtPtF D F) {w : Frm D F k g.b} (hw : w.IsGen) (χ : D.X) (s) :
    ∃ x, IsCoef k g w χ s x := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' D.P.isLB z
  obtain ⟨x, hx⟩ := cstH_surj z (sval s (lift (𝟙 (TF (R := R) F)) g.b).left z J' * (val (g.s χ) (𝟙 _) z J').val *
    (val w (𝟙 _) z J').val * ((rigV D (TF (R := R) F).hom z J' ^ k)⁻¹).val)
  refine ⟨x, fun z' J hJ => ?_⟩
  obtain rfl := pt_eq z z'
  have a₁ := sval_tr s (lift (𝟙 (TF (R := R) F)) g.b).left hJ hJ'
  have a₂ := val_tr (g.isGen χ) (𝟙 _) hJ hJ'
  have a₃ := val_tr hw (𝟙 _) hJ hJ'
  have a₄ : rigV D (TF (R := R) F).hom z J = trU D.P.L z J J' (1 : TF (R := R) F ⟶ D.P.A).left *
      rigV D (TF (R := R) F).hom z J' := by
    refine (val_tr (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig_gen
      (TF (R := R) F).hom hJ hJ').trans ?_
    rw [Fintype.prod_unique, zpow_one]; rfl
  rw [prod_fam D F (lift (𝟙 (TF (R := R) F)) g.b) χ k (trU D.P.L z J J'), lift_snd] at a₁
  simp only [Category.id_comp] at a₂ a₃
  rw [prod_gt g.b χ (trU D.P.L z J J')] at a₂
  rw [prod_line k g.b (trU D.P.L z J J')] at a₃
  rw [cst_eq, hx, a₁, a₂, a₃, a₄, ← Units.val_pow_eq_pow_val, mul_comm (Units.val _) (sval _ _ _ _)]
  simp only [_root_.mul_assoc, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  module
end GlobalTheory.UT.CoefBasic
