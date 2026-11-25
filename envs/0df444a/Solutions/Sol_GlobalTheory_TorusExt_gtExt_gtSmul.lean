-- Prove2me | solution 1 for GlobalTheory.TorusExt.gtExt_gtSmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:09:46.857423+00:00
-- url     : https://prove2.me/submissions/a8f66bf6-341f-4362-8cc5-3b575ae2b507

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_GtActIffEqGtSmul
import Theorems.Thm_GlobalTheory_TorusExt_gtExt_b
import Theorems.Thm_GlobalTheory_TorusExt_gtExt_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr


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
variable {F' : Type} [Field F'] [Algebra (FractionRing R) F']
variable (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
namespace GlobalTheory.TorusExt
theorem _root_.solution {O : Type} [CommRing O] [StarRing O] [Module O D.X] (hG : GlobalFnsSt) (oa : D.OAct O) (a : O)
    (g : GtPtF D F) : gtExt D f hf (gtSmul hG oa a g) = gtSmul hG oa a (gtExt D f hf g) :=
  gt_ext_val (by rw [gtExt_b, gtSmul_b, gtSmul_b, gtExt_b, Category.assoc]) fun χ y J hJ => by
    rw [gtExt_val f hf _ χ hJ, gtSmul_val hG oa _ _ χ hJ, gtExt_val f hf _ _ hJ, gtExt_b, ← comp_cP D (extMap f hf)]
    exact (val_corr hJ ((gtAct_gtSmul hG oa a g).2 _ (rosGen_isRos hG oa a).1 (rosGen_isRos hG oa a).2 χ) _).symm.trans
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull_pair _ _ hJ _ _)))
end GlobalTheory.TorusExt
