-- Prove2me | solution 1 for GlobalTheory.TorusExt.gtAct_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:35:28.334986+00:00
-- url     : https://prove2.me/submissions/8f8051f5-93b8-4a5c-8c1c-33f5da960fdf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_GtActIffEqGtSmul

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
namespace GlobalTheory.TorusExt
theorem _root_.solution (hG : GlobalFnsSt) {oa : D.OAct O} {a : O} {g h h' : GtPtF D F} (e : GtAct oa a g h)
    (e' : GtAct oa a g h') : h = h' := by
  obtain ⟨b, v⟩ := (gtAct_iff_val hG _ _ _ _).1 e
  obtain ⟨b', v'⟩ := (gtAct_iff_val hG _ _ _ _).1 e'
  exact gt_ext_val (b.trans b'.symm) fun χ y J hJ => (v χ y J hJ).trans (v' χ y J hJ).symm
end GlobalTheory.TorusExt
