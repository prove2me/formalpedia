-- Prove2me | solution 1 for GlobalTheory.AnArc.perFactor_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:13:28.244257+00:00
-- url     : https://prove2.me/submissions/fb4daca2-a626-436e-afc6-25fab5eebdbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_chi_ne_zero

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
theorem _root_.solution (w : ℂ) (la : A.La) (v : A.V) : A.perFactor w la v = Complex.exp (A.L w la v) := by
  rw [perFactor, ah, L, logConst, lin_apply, H_add_left]
  simp only [Complex.exp_add, Complex.exp_sub, mul_add, Complex.exp_log (A.chi_ne_zero _),
    Complex.exp_log (A.psi _).ne_zero, e_def]
  ring
end GlobalTheory.AnArc
