-- Prove2me | solution 1 for GlobalTheory.UT.PhiOrder.tau_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:03:48.054831+00:00
-- url     : https://prove2.me/submissions/3c6a0451-e27d-4bd2-98f5-0a4c6ecd0a68

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_nsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tau_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
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
theorem _root_.solution (hB : D.TauBimult) (hE : D.PsiEven) {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F)
    {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (y : D.X) :
    val (D.tau y y) (σ.left ≫ jFK (R := R) F) z J =
      th D z J (cP D T y) (cP D T y)⁻¹ (cP D T y) * (val D.sym (cP D T y).left z J)⁻¹ *
        val (D.psi y) (σ.left ≫ jFK (R := R) F) z J ^ 2 * val D.rigK (σ.left ≫ jFK (R := R) F) z J ^ 2 := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have e : ∀ a b : D.X, val (D.tau a b) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi (a + b)) (σ.left ≫ jFK (R := R) F) z J * (val (D.psi a) (σ.left ≫ jFK (R := R) F) z J)⁻¹ *
        (val (D.psi b) (σ.left ≫ jFK (R := R) F) z J)⁻¹ * (val D.rigK (σ.left ≫ jFK (R := R) F) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have c0 : cP D T 0 = 1 := by simpa using cPoint_nsmul D T 0 y
  have cn : cP D T (-y) = (cP D T y)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← cPoint_add, neg_add_cancel, c0]
  have t₀ := tau_mul σ hJ hB 0 0 y
  rw [c0, C.face, add_zero, e, zero_add] at t₀
  have t₁ := tau_mul σ hJ hB y (-y) y
  rw [add_neg_cancel, cn, e 0 y, e (-y) y, zero_add, neg_add_cancel] at t₁
  have t₂ := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    (val_corr hJ (hE y) (σ.left ≫ jFK (R := R) F))
  have a₁ : (σ.left ≫ jFK (R := R) F) ≫ D.xK y = (cP D T y).left := by
    rw [← comp_cP D σ, Category.assoc]
    exact congrArg (σ.left ≫ ·) (Category.assoc _ _ _).symm
  rw [a₁] at t₂
  apply Additive.ofMul.injective
  have b₀ := congrArg Additive.ofMul t₀
  have b₁ := congrArg Additive.ofMul t₁
  have b₂ := congrArg Additive.ofMul t₂
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at b₀ b₁ b₂ ⊢
  linear_combination (norm := module) -b₁ - 2 • b₀ + b₂
end GlobalTheory.UT.PhiOrder
