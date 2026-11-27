-- Prove2me | solution 1 for MasulloRH.quarter_shift_theta_derivative_table_fourth_quarter
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T23:58:31.833379+00:00
-- url     : https://prove2.me/submissions/03baeedb-0748-4df7-98e6-9b4f9fd44c35

import Definitions.Def_MasulloRH_ThetaDerivativeCertificates
import Mathlib.Tactic.IntervalCases

open MasulloRH.ThetaDerivativeCertificate
set_option maxRecDepth 160000
set_option maxHeartbeats 10000000

private theorem row0 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(6))) = true := by decide +kernel
private theorem row1 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(9))) = true := by decide +kernel
private theorem row2 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(12))) = true := by decide +kernel
private theorem row3 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(15))) = true := by decide +kernel
private theorem row4 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(18))) = true := by decide +kernel
private theorem row5 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(21))) = true := by decide +kernel

theorem solution (j : ℤ) (hl : 6 ≤ j) (hr : j < 24) : thetaCheck j = true := by
  by_cases h0 : j < 9
  · have h := List.all_eq_true.mp row0 (j-(6)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(6)).toNat:ℤ)+(6)=j by omega] using h
  by_cases h1 : j < 12
  · have h := List.all_eq_true.mp row1 (j-(9)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(9)).toNat:ℤ)+(9)=j by omega] using h
  by_cases h2 : j < 15
  · have h := List.all_eq_true.mp row2 (j-(12)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(12)).toNat:ℤ)+(12)=j by omega] using h
  by_cases h3 : j < 18
  · have h := List.all_eq_true.mp row3 (j-(15)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(15)).toNat:ℤ)+(15)=j by omega] using h
  by_cases h4 : j < 21
  · have h := List.all_eq_true.mp row4 (j-(18)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(18)).toNat:ℤ)+(18)=j by omega] using h
  have h := List.all_eq_true.mp row5 (j-(21)).toNat (List.mem_range.mpr (by omega))
  simpa only [show ((j-(21)).toNat:ℤ)+(21)=j by omega] using h
