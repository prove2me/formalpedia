-- Prove2me | solution 1 for GlobalTheory.AnArc.Sum_add_Pw_div_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:03:37.41333+00:00
-- url     : https://prove2.me/submissions/3ad5e6b1-06d1-4811-af6a-6a2f7e57ee15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_exp_lin
import Theorems.Thm_GlobalTheory_AnArc_Sum_add_Pw_div

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
variable (k : ℕ) [NeZero k]
namespace GlobalTheory.AnArc
theorem _root_.solution (w : ℂ) (la : A.La) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.Sum k α th w (v + (k : ℂ)⁻¹ • A.Pw w la) * eTwoPi (v.1 la.y) =
      Complex.exp (Real.pi * A.H v.2 la.l) * eTwoPi (w * A.be la.y α / k) *
        A.Sum k (α + la.y) (A.shift k la α th) w v := by
  have := e_ne_zero (v.1 la.y)
  rw [Sum_add_Pw_div, exp_lin]
  field_simp
end GlobalTheory.AnArc
