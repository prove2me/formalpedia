-- Prove2me | solution 1 for GlobalTheory.UT.CoefPhi.coef_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:45:37.803547+00:00
-- url     : https://prove2.me/submissions/f3de52d1-7309-40ea-8281-32173c7b9f1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFrameRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubNMul
import Theorems.Thm_GlobalTheory_UT_CoefPhi_cubN_mul
import Theorems.Thm_GlobalTheory_UT_CoefPhi_exists_frame
import Theorems.Thm_GlobalTheory_UT_CoefBasic_coef_eq
import Theorems.Thm_GlobalTheory_UT_CoefBasic_isCoef_coef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gt_nsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_phiRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_pr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isAdd_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isZero_iff


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
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.CoefPhi
open GlobalTheory.UT.CoefBasic
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UT.CoefPhi
theorem _root_.solution : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), w.IsGen → ∀ (g₀ g₁ : GtPtF D.toPre F), g₀.IsAdd p.g g₁ → ∀ ω₀ : Frm D.toPre F k g₀.b, ω₀.IsGen → ∃ ω₁ : Frm D.toPre F k g₁.b, ω₁.IsGen ∧ (g₀.IsZero → FrmOne ω₀ → ∀ z J, Good D.toPre.P.L z J → val ω₁ (𝟙 _) z J = val w (𝟙 _) z J) ∧ ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ (q : QkPt D.toPre F N), q.y = n • p.y → q.g = p.g → ∀ (wN : Frm D.toPre F N q.g.b) (w₀ : Frm D.toPre F N g₀.b) (w₁ : Frm D.toPre F N g₁.b), (wN.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val wN (𝟙 _) z J = val w (𝟙 _) z J ^ n) → (w₀.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val w₀ (𝟙 _) z J = val ω₀ (𝟙 _) z J ^ n) → (w₁.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val w₁ (𝟙 _) z J = val ω₁ (𝟙 _) z J ^ n) → ∀ s s' : Fam D.toPre F N, PhiRel D.toPre F N q wN s s' → ∀ α, coef s' g₀ w₀ (α + q.y) = coef s g₁ w₁ α := by
  intro hL R _ _ _ I _ D F _ _ _ k _ p w hw g₀ g₁ hadd ω₀ h₀
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
  obtain ⟨ω₁, h₁, v₁⟩ := exists_frame p w hw g₀ ω₀ h₀ g₁.b hb
  refine ⟨ω₁, h₁, fun hz ho z J hJ => ?_, ?_⟩
  · have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
    obtain ⟨z₁, z₂⟩ := (isZero_iff _).1 hz
    have c : cubN (th D.toPre z J) k 1 p.g.b g₀.b = 1 := by rw [z₁, C.N_one]
    rw [v₁ z J hJ, ho.2 z J hJ, z₂ _ z J hJ, c, _root_.one_mul, _root_.mul_one, _root_.mul_one]
  · rintro n _ _ rfl ⟨qy, qg, qe⟩ hy hg wN w₀ w₁ ⟨hN, vN⟩ ⟨-, v₀⟩ ⟨hw₁, vw₁⟩ s s' hΦ α
    dsimp only at hy hg
    subst hy hg
    have H := (phiRel_iff hL.1.globalFns _ wN hN s s').1 hΦ
    refine coef_eq fun z J hJ => ?_
    have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
    have e₁ := H α _ rfl _ (lift (𝟙 (TF (R := R) F)) g₀.b) z J hJ
    have t : lift (𝟙 (TF (R := R) F)) g₀.b ≫ DegPre.trPt D.toPre F p.g.b = lift (𝟙 (TF (R := R) F)) g₁.b := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, tr_fst, lift_fst, lift_fst]
      · rw [lift_snd, hb, Category.assoc]
        refine (congrArg (_ ≫ ·) (tr_pr D.toPre F p.g.b)).trans ?_
        rw [MonObj.comp_mul, lift_fst_assoc, Category.id_comp, lift_snd]
    dsimp only at e₁ vN
    rw [t, uVal, lift_fst_assoc, lift_fst, lift_snd, Category.id_comp, Over.id_left, val_mul hJ, vN z J hJ,
      cubN_mul C] at e₁
    have e₂ := gt_nsmul (𝟙 (TF (R := R) F)) hJ g₀ α p.y n
    rw [Category.id_comp, Over.id_left, cPoint_y] at e₂
    have e₃ := hs α z J hJ
    rw [isCoef_coef g₁ hw₁ α s z J hJ]
    dsimp only
    rw [e₁, v₀ z J hJ, vw₁ z J hJ, v₁ z J hJ]
    simp only [_root_.mul_assoc, ← Units.val_mul]
    congr 2
    apply Additive.ofMul.injective
    have a₂ := congrArg Additive.ofMul e₂
    have a₃ := congrArg Additive.ofMul e₃
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at a₂ a₃ ⊢
    linear_combination (norm := module) a₃ - a₂
end GlobalTheory.UT.CoefPhi
