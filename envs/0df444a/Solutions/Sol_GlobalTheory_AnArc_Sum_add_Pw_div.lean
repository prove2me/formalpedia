-- Prove2me | solution 1 for GlobalTheory.AnArc.Sum_add_Pw_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:46:32.126571+00:00
-- url     : https://prove2.me/submissions/4eebaee2-c9ea-49a9-85d8-250193ce6ba6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_term_add_Pw_div

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
    A.Sum k α th w (v + (k : ℂ)⁻¹ • A.Pw w la) = Complex.exp (A.lin la v) * eTwoPi (w * A.be la.y α / k) *
      A.Sum k (α + la.y) (A.shift k la α th) w v := by
  simp only [Sum, term_add_Pw_div, tsum_mul_left]
end GlobalTheory.AnArc
