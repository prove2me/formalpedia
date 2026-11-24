-- Prove2me | solution 1 for GlobalTheory.summable_exp_neg_sum_abs_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:58.809579+00:00
-- url     : https://prove2.me/submissions/c49db963-c7fb-4fe1-b38b-ee9283c9018c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_SummableExpNegAbsSum_summable_exp_neg_sum_abs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
namespace GlobalTheory
theorem _root_.solution {ι : Type} [Fintype ι] :
    Summable fun m : ι → ℤ => Real.exp (-∑ i, |(m i : ℝ)|) := by
  first
  | exact @_root_.GlobalTheory.SummableExpNegAbsSum.summable_exp_neg_sum_abs
  | exact _root_.GlobalTheory.SummableExpNegAbsSum.summable_exp_neg_sum_abs
  | (apply _root_.GlobalTheory.SummableExpNegAbsSum.summable_exp_neg_sum_abs <;> assumption)
  | (intros; apply _root_.GlobalTheory.SummableExpNegAbsSum.summable_exp_neg_sum_abs <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SummableExpNegAbsSum.summable_exp_neg_sum_abs <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SummableExpNegAbsSum.summable_exp_neg_sum_abs ..)
end GlobalTheory
