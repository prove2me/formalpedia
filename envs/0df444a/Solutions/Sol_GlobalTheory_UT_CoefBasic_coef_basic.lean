-- Prove2me | solution 1 for GlobalTheory.UT.CoefBasic.coef_basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:48:53.736037+00:00
-- url     : https://prove2.me/submissions/384e2beb-5b98-4d92-b1ff-234047fe0408

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
import Theorems.Thm_GlobalTheory_UT_CoefBasic_exists_pt
import Theorems.Thm_GlobalTheory_UT_CoefBasic_exists_gen_pt
import Theorems.Thm_GlobalTheory_UT_CoefBasic_prod_line
import Theorems.Thm_GlobalTheory_UT_CoefBasic_isCoef_unique
import Theorems.Thm_GlobalTheory_UT_CoefBasic_coef_eq
import Theorems.Thm_GlobalTheory_UT_CoefBasic_exists_isCoef
import Theorems.Thm_GlobalTheory_UT_CoefBasic_isCoef_coef
import Theorems.Thm_GlobalTheory_UT_CoefBasic_sval_lin
import Theorems.Thm_GlobalTheory_UT_CoefBasic_exists_frame_ratio
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__944b82dcaa95
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isAdd_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pt_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F), (∃ w : Frm D F k g.b, w.IsGen) ∧ (g.b = 1 → ∃ w : Frm D F k g.b, FrmOne w) ∧ ∀ w : Frm D F k g.b, w.IsGen → (∀ χ s, ∃! x, IsCoef k g w χ s x) ∧ (∀ (s s' : Fam D F k) (c : F) χ, coef (c • s + s') g w χ = c * coef s g w χ + coef s' g w χ) ∧ (∀ w' : Frm D F k g.b, w'.IsGen → ∃ c : F, c ≠ 0 ∧ (∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val) ∧ ∀ (s : Fam D F k) χ, coef s g w' χ = c * coef s g w χ) ∧ ∀ (t : Multiplicative D.X →* Fˣ) (g₀ g' : GtPtF D F) (w' : Frm D F k g'.b), IsTor t g₀ → g.IsAdd g₀ g' → (∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J) → ∀ (s : Fam D F k) χ, coef s g' w' χ = (t (Multiplicative.ofAdd χ)).val * coef s g w χ := by
  intro R _ _ D F _ _ k g
  obtain ⟨z₀⟩ := exists_pt (R := R) (F := F)
  refine ⟨exists_gen_pt D.P.isLB z₀ (fun y => pt_eq y z₀) _ _, fun hb => ?_, fun w hw => ⟨fun χ s => ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨w, hw, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F g.b) (ε' := DegPre.lineε k)
      (fun U _ h => by rw [prod_line, hb, mul_inv_cancel]; exact Fintype.prod_empty _)
      (LB.oneGen D.P.L (Y := (TF (R := R) F).left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨w, hw, fun z J hJ => (hv _ _ z J hJ).trans (val_one _)⟩
  · obtain ⟨x, hx⟩ := exists_isCoef g hw χ s
    exact ⟨x, hx, fun y hy => isCoef_unique hy hx⟩
  · intro s s' c χ
    refine coef_eq fun z J hJ => ?_
    have a := isCoef_coef g hw χ s z J hJ
    have a' := isCoef_coef g hw χ s' z J hJ
    rw [sval_lin g.b s s' c χ hJ]
    simp only [cst_eq, map_add, map_mul] at a a' ⊢
    linear_combination cstH z c * a + a'
  · intro w' hw'
    obtain ⟨c, hc, hv⟩ := exists_frame_ratio hw hw'
    refine ⟨c, hc, hv, fun s χ => coef_eq fun z J hJ => ?_⟩
    have a := isCoef_coef g hw χ s z J hJ
    rw [hv z J hJ]
    simp only [cst_eq, map_mul] at a ⊢
    linear_combination cstH z c * a
  · intro t g₀ g' w' ht hadd hv s χ
    obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
    refine coef_eq fun z J hJ => ?_
    have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
    have a := isCoef_coef g hw χ s z J hJ
    have e := hs χ z J hJ
    rw [ht.1, _root_.mul_one] at hb
    have e₀ : th D z J (cP D _ χ) g.b g₀.b = 1 := by rw [ht.1, C.face₃]
    rw [e₀, _root_.mul_one] at e
    have e₁ : lift (𝟙 (TF (R := R) F)) g'.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]
    rw [hv z J hJ, e, e₁, Units.val_mul, ht.2 χ z J hJ]
    simp only [cst_eq, map_mul] at a ⊢
    linear_combination cstH z (t (Multiplicative.ofAdd χ)).val * a
end GlobalTheory.UT.CoefBasic
