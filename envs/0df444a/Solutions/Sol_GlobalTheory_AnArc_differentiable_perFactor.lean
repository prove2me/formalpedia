-- Prove2me | solution 1 for GlobalTheory.AnArc.differentiable_perFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:25:34.460147+00:00
-- url     : https://prove2.me/submissions/bcd9da2d-bbcb-4895-b56e-57b535f4be40

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
theorem _root_.solution (w : ℂ) (la : A.La) : Differentiable ℂ (A.perFactor w la) := by
  have : A.perFactor w la = fun v => Complex.exp ((A.lin la).toContinuousLinearMap v + A.logConst w la) :=
    funext fun v => A.perFactor_eq_exp w la v
  rw [this]
  fun_prop
end GlobalTheory.AnArc
