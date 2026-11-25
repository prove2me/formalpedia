-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_8_iii_goalV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T07:46:46.316383+00:00
-- url     : https://prove2.me/submissions/72c370ae-d234-48e2-afa0-f16ebe13cb4b

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_8CertificationV2
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_P_exp_clock_sup_drawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_Kyprianou_Ch04_independentExpClockEndpointSupJointLaw
set_option autoImplicit false

open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal

theorem solution : certificate_ex4_8_iii_v2 := by
  intro Ω _ P F L hBV Psi hPsi q hq e he hlaw hi
  letI : IsProbabilityMeasure P := L.isProbability
  letI : IsProbabilityMeasure (expMeasure q) := isProbabilityMeasure_expMeasure hq
  obtain ⟨hD, hS, hJ⟩ := independentExpClockEndpointSupJointLaw P F L q hq e he hlaw hi
  have hm := levy_exponential_real_clock_extrema_drawdown_measurable L
  have hp := (avram_ws01e_bt_new_original_P_exp_clock_sup_drawdown_indepFun L q hq).symm
  have hh := hp.comp measurable_neg measurable_id
  change IndepFun _ _ P
  apply indepFun_of_identDistrib_pair hh
  refine ⟨?_, (hD.prodMk hS).aemeasurable, ?_⟩
  · exact (hm.snd.neg.prodMk hm.fst.fst).aemeasurable
  · simpa only [Function.comp_apply, id_eq, neg_sub] using hJ.symm
