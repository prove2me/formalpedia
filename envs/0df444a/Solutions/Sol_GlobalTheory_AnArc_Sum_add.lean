-- Prove2me | solution 1 for GlobalTheory.AnArc.Sum_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:34:35.91563+00:00
-- url     : https://prove2.me/submissions/f7b3e701-8de9-4c74-96f3-46146de1136d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_term_add

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
theorem _root_.solution {j : ℕ} {α : A.X} {th th' : (Fin A.gB → ℂ) → ℂ} {w : ℂ} {v : A.V}
    (h : Summable fun μ => A.term j α th μ v * eTwoPi (w * A.exponent j α μ))
    (h' : Summable fun μ => A.term j α th' μ v * eTwoPi (w * A.exponent j α μ)) :
    A.Sum j α (th + th') w v = A.Sum j α th w v + A.Sum j α th' w v := by
  simp only [Sum, term_add, add_mul, h.tsum_add h']
end GlobalTheory.AnArc
