-- Prove2me | solution 1 for GlobalTheory.TorusExt.gtExt_iota
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:17:18.43307+00:00
-- url     : https://prove2.me/submissions/88edd4cf-789b-44e7-ae83-430df5ef4162

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_GtActIffEqGtSmul
import Theorems.Thm_GlobalTheory_TorusExt_extMap_jFK
import Theorems.Thm_GlobalTheory_TorusExt_gtExt_b
import Theorems.Thm_GlobalTheory_TorusExt_gtExt_val
import Theorems.Thm_GlobalTheory_TorusExt_iota_b
import Theorems.Thm_GlobalTheory_TorusExt_iota_val
import Theorems.Thm_GlobalTheory_TorusExt_isIota_iota
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
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
variable {F' : Type} [Field F'] [Algebra (FractionRing R) F']
variable (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
namespace GlobalTheory.TorusExt
theorem _root_.solution (hB : D.TauBimult) (x : D.X) : gtExt D f hf (iota hB F x) = iota hB F' x :=
  gt_ext_val (by rw [gtExt_b, iota_b, iota_b, comp_cP]) fun χ y J hJ => by
    rw [gtExt_val f hf _ χ hJ, iota_val hB _ _ hJ, tauVal, ← extMap_jFK f hf]
    exact (val_corr hJ ((isIota_iota hB x).2 χ) _).trans (val_pull hJ _ _ _)
end GlobalTheory.TorusExt
