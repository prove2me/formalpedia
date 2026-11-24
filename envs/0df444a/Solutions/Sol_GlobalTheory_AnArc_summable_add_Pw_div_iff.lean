-- Prove2me | solution 1 for GlobalTheory.AnArc.summable_add_Pw_div_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:43:46.835899+00:00
-- url     : https://prove2.me/submissions/8e8baaf1-0d42-49cf-b8f1-48b3882fbecf

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
    (Summable fun μ => A.term k α th μ (v + (k : ℂ)⁻¹ • A.Pw w la) * eTwoPi (w * A.exponent k α μ)) ↔
      Summable fun μ => A.term k (α + la.y) (A.shift k la α th) μ v * eTwoPi (w * A.exponent k (α + la.y) μ) := by
  simp only [term_add_Pw_div]
  exact summable_mul_left_iff (mul_ne_zero (Complex.exp_ne_zero _) (e_ne_zero _))
end GlobalTheory.AnArc
