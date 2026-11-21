-- Prove2me | solution 1 for MasulloRH.archTerm_eq_neg_realTraceIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T22:27:16.729173+00:00
-- url     : https://prove2.me/submissions/cb04acc6-5e0b-4631-8c84-1fd8fa2afe90

import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_ConnesRZ_weil_defs
import Theorems.Thm_MasulloRH_archTerm_log_test_eq_neg_real_place
open Set MeasureTheory MasulloRH

theorem solution (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    ConnesRZ.archTerm (fun u => φ (Real.exp u)) = -∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t :=
  MasulloRH.archTerm_log_test_eq_neg_real_place φ hφ
