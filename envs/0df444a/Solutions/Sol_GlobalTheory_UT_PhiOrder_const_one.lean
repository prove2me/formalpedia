-- Prove2me | solution 1 for GlobalTheory.UT.PhiOrder.const_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:35:10.134158+00:00
-- url     : https://prove2.me/submissions/d349dbff-847d-41a7-a09a-7e386173a3d4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SymmetricFramePhiPowOrderEqId
import Theorems.Thm_GlobalTheory_UT_PhiOrder_const_eq_one
import Theorems.Thm_GlobalTheory_UT_PhiOrder_exists_kap
import Theorems.Thm_GlobalTheory_UT_PhiOrder_tau_diag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_nsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_chain_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gt_nsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.PhiOrder
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable {D}
variable {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UT.PhiOrder
theorem _root_.solution (hB : D.TauBimult) (hE : D.PsiEven) {k : ℕ} (hk : Odd k) (p : QkPt D F k) (w : Frm D F k p.g.b)
    (hw : TXFrame k p w) (z : (TF (R := R) F).left) (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : Good D.P.L z J) :
    (∏ i ∈ Finset.range k, H1.hv (th D z J) k ((p.g.b ^ k) ^ i) p.g.b (p.g.b ^ (k - 1 - i)) *
        (val (p.g.s (i • p.y)) (Over.Hom.left (𝟙 (TF (R := R) F))) z J * val w (Over.Hom.left (𝟙 (TF (R := R) F))) z J)) *
      (val (GeneratorPullback.powGen D.P.L _ _ (D.psi p.y) k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J *
        val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J)⁻¹ = 1 := by
  obtain ⟨m, hm⟩ := hk
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
  obtain ⟨κ, hκ, vκ⟩ := exists_kap (D := D) m k hm
  have h₁ := hw.2.2 κ hκ z J hJ
  rw [vκ _ p.g.b z J hJ] at h₁
  have c0 : cP D (TF (R := R) F) 0 = 1 := by simpa using cPoint_nsmul D (TF (R := R) F) 0 p.y
  have s0 : val (p.g.s 0) (Over.Hom.left (𝟙 (TF (R := R) F))) z J = 1 := by
    have := gt_mul (𝟙 (TF (R := R) F)) hJ p.g 0 0
    rw [c0, C.face, add_zero] at this
    exact (mul_left_cancel this).symm
  have hS : ∀ i : ℕ, val (p.g.s (i • p.y)) (Over.Hom.left (𝟙 (TF (R := R) F))) z J *
      cubN (th D z J) i 1 (p.g.b ^ k) p.g.b = val (p.g.s p.y) (Over.Hom.left (𝟙 (TF (R := R) F))) z J ^ i := fun i => by
    have := gt_nsmul (𝟙 (TF (R := R) F)) hJ p.g 0 p.y i
    rwa [zero_add, c0, s0, _root_.one_mul, cPoint_y, Category.id_comp] at this
  have hτ := chain_val (𝟙 (TF (R := R) F)) hJ p p.y
  rw [Category.id_comp, cPoint_y] at hτ
  have hd := tau_diag hB hE (𝟙 (TF (R := R) F)) hJ p.y
  rw [cPoint_y] at hd
  have r₁ : rigV D (TF (R := R) F).hom z J =
      val D.rigK ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J := by
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    refine congrArg (fun q => rigV D q z J) ?_
    rw [Over.id_left, Category.id_comp]; rfl
  have r₂ : val (D.psi p.y) (jFK (R := R) F) z J =
      val (D.psi p.y) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J :=
    congrArg (fun q => val (D.psi p.y) q z J) (Category.id_comp _).symm
  have key := const_eq_one C p.g.b m k hm _ _ _ _ _ _ _ hS hτ hd (h₁.trans (congrArg₂ (· * ·) r₂ r₁))
  refine Eq.trans ?_ key
  exact congrArg₂ (· * ·) rfl (congrArg (·⁻¹) (congrArg₂ (· * ·) (map_pow _ _ _) (map_pow _ _ _)))
end GlobalTheory.UT.PhiOrder
