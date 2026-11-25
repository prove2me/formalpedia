-- Prove2me | solution 1 for GlobalTheory.AnArc.Sum_eq_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:25:09.727788+00:00
-- url     : https://prove2.me/submissions/f7cb823e-4f03-4de6-a80f-32f1fcde1d53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_exponent_add
import Theorems.Thm_GlobalTheory_AnArc_term_add_index

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
theorem _root_.solution (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (y : A.X) (w : ℂ) (v : A.V) :
    A.Sum j α th w v = (A.psi y : ℂ) ^ j * eTwoPi (A.T y α) * eTwoPi (w * A.exponent j α y) *
      A.Sum j (α + j • y) (fun z => th (z + A.ct y)) w v := by
  rw [Sum, Sum, ← tsum_mul_left, ← (Equiv.addRight y).tsum_eq]
  refine tsum_congr fun μ => ?_
  rw [Equiv.coe_addRight, term_add_index, exponent_add]
  push_cast
  rw [mul_add, e_add]; ring
end GlobalTheory.AnArc
