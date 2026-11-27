-- Prove2me | solution 1 for MasulloRH.quarter_shift_theta_derivative_table_first_quarter
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T23:58:28.132162+00:00
-- url     : https://prove2.me/submissions/20187507-1151-4f94-acdd-c474281f1863

import Definitions.Def_MasulloRH_ThetaDerivativeCertificates
import Mathlib.Tactic.IntervalCases

open MasulloRH.ThetaDerivativeCertificate
set_option maxRecDepth 160000
set_option maxHeartbeats 10000000

private theorem row0 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(-48))) = true := by decide +kernel
private theorem row1 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(-45))) = true := by decide +kernel
private theorem row2 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(-42))) = true := by decide +kernel
private theorem row3 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(-39))) = true := by decide +kernel
private theorem row4 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(-36))) = true := by decide +kernel
private theorem row5 : (List.range 3).all (fun n => thetaCheck ((n:ℤ)+(-33))) = true := by decide +kernel

theorem solution (j : ℤ) (hl : -48 ≤ j) (hr : j < -30) : thetaCheck j = true := by
  by_cases h0 : j < -45
  · have h := List.all_eq_true.mp row0 (j-(-48)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-48)).toNat:ℤ)+(-48)=j by omega] using h
  by_cases h1 : j < -42
  · have h := List.all_eq_true.mp row1 (j-(-45)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-45)).toNat:ℤ)+(-45)=j by omega] using h
  by_cases h2 : j < -39
  · have h := List.all_eq_true.mp row2 (j-(-42)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-42)).toNat:ℤ)+(-42)=j by omega] using h
  by_cases h3 : j < -36
  · have h := List.all_eq_true.mp row3 (j-(-39)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-39)).toNat:ℤ)+(-39)=j by omega] using h
  by_cases h4 : j < -33
  · have h := List.all_eq_true.mp row4 (j-(-36)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-36)).toNat:ℤ)+(-36)=j by omega] using h
  have h := List.all_eq_true.mp row5 (j-(-33)).toNat (List.mem_range.mpr (by omega))
  simpa only [show ((j-(-33)).toNat:ℤ)+(-33)=j by omega] using h
