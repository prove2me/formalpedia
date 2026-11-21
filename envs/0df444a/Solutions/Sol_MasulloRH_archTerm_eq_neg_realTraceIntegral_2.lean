-- Prove2me | solution 2 for MasulloRH.archTerm_eq_neg_realTraceIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-20T22:27:56.778821+00:00
-- url     : https://prove2.me/submissions/d16ad997-e90a-45b9-8e54-ba2857c3d01f

import Theorems.Thm_MasulloRH_archTerm_log_test_eq_neg_real_place

open MeasureTheory Set MasulloRH

theorem solution (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    ConnesRZ.archTerm (fun u => φ (Real.exp u)) =
      -∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t :=
  MasulloRH.archTerm_log_test_eq_neg_real_place φ hφ
