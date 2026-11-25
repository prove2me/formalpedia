-- Prove2me | solution 1 for GlobalTheory.TorusExt.gtAct_iff_eq_gtSmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:49:02.683089+00:00
-- url     : https://prove2.me/submissions/7ab594b2-5da1-4246-baa0-9c13c33b606f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_GtActIffEqGtSmul
import Theorems.Thm_GlobalTheory_TorusExt_gtAct_unique

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
theorem _root_.solution (a : O) (g g' : GtPtF D F) : GtAct oa a g g' ↔ g' = gtSmul hG oa a g :=
  ⟨fun h => gtAct_unique hG h (gtAct_gtSmul hG oa a g), fun h => h ▸ gtAct_gtSmul hG oa a g⟩
end GlobalTheory.TorusExt
