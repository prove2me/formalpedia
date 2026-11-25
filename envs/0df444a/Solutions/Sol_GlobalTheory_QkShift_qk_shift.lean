-- Prove2me | solution 1 for GlobalTheory.QkShift.qk_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:37:54.978408+00:00
-- url     : https://prove2.me/submissions/20a2e685-f920-4cc9-8787-5ead6cf7685b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsShiftGen
import Theorems.Thm_GlobalTheory_QkShift_cub_shift
import Theorems.Thm_GlobalTheory_QkShift_trPt_comp
import Theorems.Thm_GlobalTheory_QkShift_exists_shift_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_nsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gt_nsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_phiRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_trF_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_pr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_val_famMult
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.QkShift
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.QkShift
theorem _root_.solution : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p q : QkPt D F n) (z : D.X) (h : GtPtF D F), q.y = p.y + n • z → GtPtF.IsIota z h → GtPtF.IsAdd p.g h q.g → ∀ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n)), w.IsGen → ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q.g.b) (DegPre.lineε n)), w₂.IsGen ∧ ∀ s s' : Fam D F n, PhiRel D F n p w s s' → PhiRel D F n q w₂ s s' := by
  intro hG R _ _ D _ F _ _ n _ p q z h hy hι hadd w hw
  have hh : h.b = cP D _ z := hι.1
  have hb : q.g.b = p.g.b * cP D _ z := hadd.1.trans (congrArg (p.g.b * ·) hh)
  obtain ⟨w₂, h₂, v₂⟩ := exists_shift_gen n p.g z q.g.b hb w hw
  refine ⟨w₂, h₂, fun s t H => ?_⟩
  rw [phiRel_iff hG p w hw] at H
  rw [phiRel_iff hG q w₂ h₂]
  intro α β hβ T ρ y J hJ
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  have e₁ := H (α + n • z) β (by rw [← hβ, hy]; abel) T ρ y J hJ
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := F) hG n z α
  have e₄ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').1 (s.fe z α u' hu' hc') _
    (ρ ≫ DegPre.trPt D F p.g.b).left y J hJ
  rw [hv' u' hu' hc' _ (ρ ≫ DegPre.trPt D F p.g.b) y J hJ, trF_eq, ← Over.comp_left, Category.assoc, trPt_comp, ← hb,
    Category.assoc, tr_fst] at e₄
  rw [e₁, e₄, _root_.mul_assoc, ← Units.val_mul]
  congr 2
  have t₁ := gt_nsmul (ρ ≫ fst (TF (R := R) F) D.P.A) hJ p.g α z n
  have t₂ := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl
    (val_cub D.cub (ρ ≫ fst (TF (R := R) F) D.P.A) hJ _ _ _))).symm.trans
    ((val_corr hJ (hadd.2 α) (ρ ≫ fst (TF (R := R) F) D.P.A).left).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl ((val_corr hJ (hι.2 α) _).trans (val_pull hJ _ _ _)))))
  have c₁ : (ρ ≫ fst (TF (R := R) F) D.P.A) ≫ DegPre.cF D F α = cP D T α := comp_cP D _ α
  have c₂ : (ρ ≫ fst (TF (R := R) F) D.P.A) ≫ cP D _ z = cP D T z := comp_cP D _ z
  rw [hh, c₁, c₂] at t₂
  have key := cub_shift C n _ _ _ (ρ ≫ DegPre.prB D F) _ _ _ _ _
    (val (GeneratorPullback.powGen D.P.L _ _ (D.psi z) n) ((ρ ≫ fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) y J *
      val (GeneratorPullback.powGen D.P.L _ _ D.rigK n) ((ρ ≫ fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) y J)
    (val w (ρ ≫ fst (TF (R := R) F) D.P.A).left y J) t₁ t₂
  have d₁ : (ρ ≫ DegPre.trPt D F p.g.b) ≫ fst _ _ ≫ cP D _ z = cP D T z := by
    rw [← Category.assoc]; exact comp_cP D _ z
  have d₂ : (ρ ≫ DegPre.trPt D F p.g.b) ≫ DegPre.prB D F =
      (ρ ≫ DegPre.prB D F) * ((ρ ≫ fst (TF (R := R) F) D.P.A) ≫ p.g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, Category.assoc]
  have d₃ : ρ ≫ fst _ _ ≫ q.g.b = ((ρ ≫ fst (TF (R := R) F) D.P.A) ≫ p.g.b) * cP D T z := by
    rw [← Category.assoc, hb, MonObj.comp_mul, c₂]
  rw [val_famMult _ hJ, val_mul hJ, val_mul hJ, v₂ _ _ y J hJ, uVal, uVal, uVal, d₁, d₂, d₃, cPoint_add, cPoint_nsmul,
    ← Category.assoc ρ]
  exact key
end GlobalTheory.QkShift
