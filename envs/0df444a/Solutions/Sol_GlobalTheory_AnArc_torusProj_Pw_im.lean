-- Prove2me | solution 1 for GlobalTheory.AnArc.torusProj_Pw_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:18:53.16354+00:00
-- url     : https://prove2.me/submissions/adc93a9f-e25e-4686-ba4b-d67a46e3c017

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_torusProj_apply
import Theorems.Thm_GlobalTheory_AnArc_div_two_I
import Theorems.Thm_GlobalTheory_AnArc_H_re_symm
import Theorems.Thm_GlobalTheory_AnArc_Bw_eq

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
theorem _root_.solution (w : ℂ) (v : A.La) (x : A.X) : (A.torusProj (A.Pw w v) x).im = A.Bw w v.y x := by
  rw [torusProj_apply, Pw_fst_apply, Pw_snd, H_add_left, Bw_eq, div_two_I, div_two_I]
  simp [A.H_re_symm (A.ct x) v.l]; ring
end GlobalTheory.AnArc
