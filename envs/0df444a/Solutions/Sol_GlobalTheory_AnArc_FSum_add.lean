-- Prove2me | solution 1 for GlobalTheory.AnArc.FSum_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:57:37.738595+00:00
-- url     : https://prove2.me/submissions/062726d7-12a1-4f32-b872-5e7ba816a688

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_term_add
import Theorems.Thm_GlobalTheory_AnArc_coeff_FSum


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
theorem _root_.solution (j : ℕ) [NeZero j] (α : A.X) (th th' : (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSum j α (th + th') v = A.FSum j α th v + A.FSum j α th' v := by
  ext n
  simp only [coeff_FSum, HahnSeries.coeff_add, term_add, Finset.sum_add_distrib]
end GlobalTheory.AnArc
