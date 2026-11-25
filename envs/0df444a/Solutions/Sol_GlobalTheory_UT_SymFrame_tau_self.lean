-- Prove2me | solution 1 for GlobalTheory.UT.SymFrame.tau_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:52:00.532152+00:00
-- url     : https://prove2.me/submissions/10e6c814-7f58-4ece-b8a3-daaf75138343

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Theorems.Thm_GlobalTheory_UT_SymFrame_cPoint_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tau_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cPoint_zero
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
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.SymFrame
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Y : Over (Spec (CommRingCat.of R))}
variable {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UT.SymFrame
theorem _root_.solution (hE : D.PsiEven) (hB : D.TauBimult) (y : D.X) {z : (TF (R := R) F).left} {J} (hJ : Good D.P.L z J) :
    val (D.tau y y) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) z J =
      cubV D.cub z J (cP D (TF (R := R) F) y) (cP D _ y)⁻¹ (cP D _ y) * (val D.sym (cP D (TF (R := R) F) y).left z J)⁻¹ *
        (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi y) (jFK (R := R) F) z J) *
          rigV D (TF (R := R) F).hom z J) ^ 2 := by
  let ρ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
  have vτ : ∀ a b : D.X, val (D.tau a b) ρ.left z J =
      val (D.psi (a + b)) ρ.left z J * (val (D.psi a) ρ.left z J)⁻¹ * (val (D.psi b) ρ.left z J)⁻¹ *
        (rigV D (TF (R := R) F).hom z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) ((val_inv _ _).trans
        (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans rfl))))
  have tm : ∀ a a' b : D.X, val (D.tau (a + a') b) ρ.left z J * th D z J (cP D _ a) (cP D _ a') (cP D _ b) =
      val (D.tau a b) ρ.left z J * val (D.tau a' b) ρ.left z J := fun a a' b => by
    have := tau_mul (𝟙 (TF (R := R) F)) hJ hB a a' b
    rw [Over.id_left, Category.id_comp] at this
    exact this
  have t₀ : val (D.tau 0 y) ρ.left z J = 1 := by
    have t := tm 0 0 y
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
    exact mul_eq_left.1 t.symm
  have t₁ := tm y (-y) y
  rw [add_neg_cancel, t₀, cPoint_neg, vτ (-y), neg_add_cancel] at t₁
  rw [vτ, zero_add] at t₀
  have ev := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hE y) ρ.left)
  rw [val_pull hJ, show ρ.left ≫ D.xK y = (cP D (TF (R := R) F) y).left from
    congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (comp_cP D ρ y)] at ev
  rw [Over.id_left, Category.id_comp]
  show val (D.tau y y) ρ.left z J = th D z J _ _ _ * _ * (val (D.psi y) ρ.left z J * _) ^ 2
  apply Additive.ofMul.injective
  have a₀ := congrArg Additive.ofMul t₀
  have a₁ := congrArg Additive.ofMul t₁
  have a₂ := congrArg Additive.ofMul ev
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at a₀ a₁ a₂ ⊢
  linear_combination (norm := module) - a₁ + a₀ + a₂
end GlobalTheory.UT.SymFrame
