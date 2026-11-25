-- Prove2me | solution 1 for GlobalTheory.AnArc.Sum_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:46:29.31935+00:00
-- url     : https://prove2.me/submissions/a7fa9fa9-45e9-4e12-96e3-0f6be8f601db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_term_neg
import Theorems.Thm_GlobalTheory_AnArc_exponent_neg

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
theorem _root_.solution (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (w : ℂ) (v : A.V) :
    A.Sum j α th w (-v) = A.Sum j (-α) (fun z => th (-z)) w v := by
  rw [Sum, Sum, ← (Equiv.neg A.X).tsum_eq fun μ => A.term j (-α) _ μ v * _]
  exact tsum_congr fun μ => by rw [Equiv.neg_apply, term_neg, exponent_neg]
end GlobalTheory.AnArc
