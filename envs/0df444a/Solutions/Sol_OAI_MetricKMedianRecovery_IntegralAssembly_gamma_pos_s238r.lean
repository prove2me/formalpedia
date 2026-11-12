-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.IntegralAssembly.gamma_pos_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:29:52.437382+00:00
-- url     : https://prove2.me/submissions/4a6c928a-9b22-49c7-9b68-fb8c29816c6f

import Mathlib
import Definitions.Def_Q238L009

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_StrictnessGapPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring

lemma strictnessGap_pos {T : ℝ} (hT : 0 < T) : 0 < strictnessGap T := by
  unfold strictnessGap
  positivity

end MetricKMedianRecovery.Surplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_IndexedCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseSurplusProducer
open LocalSearch Anchoring Surplus
variable {V : Type*} [MetricSpace V] [DecidableEq V]

lemma countConstant_ge_ten : (10:ℝ) ≤ countConstant (1/100) := by
  unfold countConstant
  have hh : 0 ≤ (600/(1/100:ℝ))*(2:ℝ)^(rounds (1/100)-1) := by positivity
  linarith only [hh]

end MetricKMedianRecovery.PhaseSurplusProducer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LowCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
open LocalSearch Anchoring Completion Sampling Surplus FiniteSampling

lemma gamma_pos_s238r_oai : 0 < gamma := by
  have hT : 0 < 200*countConstant (1/100) := by
    have hC := PhaseSurplusProducer.countConstant_ge_ten
    linarith
  exact lt_min (by norm_num) (div_pos (strictnessGap_pos hT) (by norm_num))

end MetricKMedianRecovery.IntegralAssembly

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.IntegralAssembly.gamma_pos_s238r_oai := @OAI.MetricKMedianRecovery.IntegralAssembly.gamma_pos_s238r_oai
