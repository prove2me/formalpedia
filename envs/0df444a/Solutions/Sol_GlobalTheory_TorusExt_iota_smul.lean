-- Prove2me | solution 1 for GlobalTheory.TorusExt.iota_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:21:53.080362+00:00
-- url     : https://prove2.me/submissions/05e91b26-2704-4e37-844f-be721b841735

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_GtActIffEqGtSmul
import Theorems.Thm_GlobalTheory_TorusExt_iota_b
import Theorems.Thm_GlobalTheory_TorusExt_iota_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tau_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
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
open GlobalTheory GlobalTheory.TorusExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
attribute [local instance] gtGroup
variable {O : Type} [CommRing O] [StarRing O] [Module O D.X]
variable (hG : GlobalFnsSt) (oa : D.OAct O)
namespace GlobalTheory.TorusExt
theorem _root_.solution (hB : D.TauBimult) (a : O) (x : D.X) : iota hB F (a • x) = gtSmul hG oa a (iota hB F x) := by
  have hbal := oa.tau_bal (star a)
  rw [star_star] at hbal
  refine gt_ext_val (by rw [gtSmul_b, iota_b, iota_b, cPoint_smul oa]) fun χ y J hJ => ?_
  let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by rw [Category.id_comp]; rfl)
  have e := (val_mul hJ _ _ _).symm.trans
    (val_corr hJ (hbal _ (rosGen_isRos hG oa a).1 (rosGen_isRos hG oa a).2 χ x) κ.left)
  have e' : val (LB.pullGen D.P.L _ _ (rosGen hG oa a) (D.pt2 χ x)) κ.left y J =
      val₂ (rosGen hG oa a) y J (cP D _ χ) (cP D _ x) := by
    rw [val_pull hJ, val₂, ← comp_cP D κ, ← comp_cP D κ x, ← comp_lift]; rfl
  rw [gtSmul_val hG oa _ _ χ hJ, iota_val hB _ _ hJ, iota_val hB _ _ hJ, iota_b, ← e']
  exact ((congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans
    (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))).symm
end GlobalTheory.TorusExt
