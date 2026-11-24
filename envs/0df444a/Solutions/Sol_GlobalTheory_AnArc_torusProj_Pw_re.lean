-- Prove2me | solution 1 for GlobalTheory.AnArc.torusProj_Pw_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:03:36.884894+00:00
-- url     : https://prove2.me/submissions/0404943d-21ba-4741-95ff-23a1e6fc2fd9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_torusProj_apply
import Theorems.Thm_GlobalTheory_AnArc_div_two_I
import Theorems.Thm_GlobalTheory_AnArc_H_im_symm

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
theorem _root_.solution (w : ℂ) (v : A.La) (x : A.X) : (A.torusProj (A.Pw w v) x).re =
    v.n x + (A.H v.l (A.ct x)).im + (A.T v.y x).re + w.re * A.be v.y x + (A.H (A.ct v.y) (A.ct x)).im / 2 := by
  rw [torusProj_apply, Pw_fst_apply, Pw_snd, H_add_left, div_two_I, div_two_I]
  simp [A.H_im_symm (A.ct x) v.l]; ring
end GlobalTheory.AnArc
