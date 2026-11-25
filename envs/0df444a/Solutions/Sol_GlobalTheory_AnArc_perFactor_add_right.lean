-- Prove2me | solution 1 for GlobalTheory.AnArc.perFactor_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:39.208618+00:00
-- url     : https://prove2.me/submissions/ccbed38e-5acc-4137-8d02-edc2f997173c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_perFactor_eq_exp

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
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (w : ℂ) (la : A.La) (v v' : A.V) :
    A.perFactor w la (v + v') = A.perFactor w la v * Complex.exp (A.lin la v') := by
  rw [perFactor_eq_exp, perFactor_eq_exp, ← Complex.exp_add, L, L, map_add]; congr 1; ring
end GlobalTheory.AnArc
