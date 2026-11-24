-- Prove2me | solution 1 for GlobalTheory.AnArc.dualForm_im_of_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:19:00.081887+00:00
-- url     : https://prove2.me/submissions/e62014d2-7b77-4638-b553-d26d2e3b597b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_dualForm_re_im
import Theorems.Thm_GlobalTheory_AnArc_coord_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (w : ℂ) {r r' : A.X →+ ℂ} (hr : ∀ x, (r x).im = 0) (hr' : ∀ x, (r' x).im = 0) :
    (A.dualForm w r r').im = 0 := by
  rw [(A.dualForm_re_im w r r' _ rfl).2]
  simp [coord_apply, hr, hr', dotProduct, mulVec]
end GlobalTheory.AnArc
