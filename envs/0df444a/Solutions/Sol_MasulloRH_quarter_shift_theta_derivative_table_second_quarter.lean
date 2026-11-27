-- Prove2me | solution 1 for MasulloRH.quarter_shift_theta_derivative_table_second_quarter
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T23:58:28.980262+00:00
-- url     : https://prove2.me/submissions/3215c355-4d4c-45b8-906f-496e530c1ae8

import Definitions.Def_MasulloRH_ThetaDerivativeCertificates
import Mathlib.Tactic.IntervalCases

open MasulloRH.ThetaDerivativeCertificate
set_option maxRecDepth 160000
set_option maxHeartbeats 10000000

private theorem row0 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(-30))) = true := by decide +kernel
private theorem row1 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(-27))) = true := by decide +kernel
private theorem row2 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(-24))) = true := by decide +kernel
private theorem row3 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(-21))) = true := by decide +kernel
private theorem row4 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(-18))) = true := by decide +kernel
private theorem row5 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(-15))) = true := by decide +kernel

theorem solution (j : ℤ) (hl : -30 ≤ j) (hr : j < -12) : thetaCheck j = true := by
  by_cases h0 : j < -27
  · have h := List.all_eq_true.mp row0 (j-(-30)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-30)).toNat:ℤ)+(-30)=j by omega] using h
  by_cases h1 : j < -24
  · have h := List.all_eq_true.mp row1 (j-(-27)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-27)).toNat:ℤ)+(-27)=j by omega] using h
  by_cases h2 : j < -21
  · have h := List.all_eq_true.mp row2 (j-(-24)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-24)).toNat:ℤ)+(-24)=j by omega] using h
  by_cases h3 : j < -18
  · have h := List.all_eq_true.mp row3 (j-(-21)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-21)).toNat:ℤ)+(-21)=j by omega] using h
  by_cases h4 : j < -15
  · have h := List.all_eq_true.mp row4 (j-(-18)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-18)).toNat:ℤ)+(-18)=j by omega] using h
  have h := List.all_eq_true.mp row5 (j-(-15)).toNat (List.mem_range.mpr (by omega))
  simpa only [show ((j-(-15)).toNat:ℤ)+(-15)=j by omega] using h
