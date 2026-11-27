-- Prove2me | solution 1 for MasulloRH.quarter_shift_gaussian_derivative_and_weight_tables
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T23:58:32.811686+00:00
-- url     : https://prove2.me/submissions/a9dc8c0b-a5b2-4a30-b88e-ae385a681ac4

import Definitions.Def_MasulloRH_ThetaDerivativeCertificates
import Mathlib.Tactic.IntervalCases

open MasulloRH.ThetaDerivativeCertificate
set_option maxRecDepth 160000
set_option maxHeartbeats 10000000

private theorem row0 : (List.range 16).all (fun n => pulseCheck ((n:ℤ)+(-112))) = true := by decide +kernel
private theorem row1 : (List.range 16).all (fun n => pulseCheck ((n:ℤ)+(-96))) = true := by decide +kernel
private theorem row2 : (List.range 16).all (fun n => pulseCheck ((n:ℤ)+(-80))) = true := by decide +kernel
private theorem row3 : (List.range 16).all (fun n => pulseCheck ((n:ℤ)+(-64))) = true := by decide +kernel
private theorem row4 : (List.range 16).all (fun n => pulseCheck ((n:ℤ)+(-48))) = true := by decide +kernel
private theorem row5 : (List.range 16).all (fun n => pulseCheck ((n:ℤ)+(-32))) = true := by decide +kernel
private theorem row6 : (List.range 16).all (fun n => pulseCheck ((n:ℤ)+(-16))) = true := by decide +kernel
private theorem row7 : (List.range 16).all (fun n => pulseCheck ((n:ℤ)+(0))) = true := by decide +kernel
private theorem row8 : (List.range 16).all (fun n => pulseCheck ((n:ℤ)+(16))) = true := by decide +kernel
private theorem row9 : (List.range 16).all (fun n => pulseCheck ((n:ℤ)+(32))) = true := by decide +kernel
private theorem row10 : (List.range 16).all (fun n => pulseCheck ((n:ℤ)+(48))) = true := by decide +kernel
private theorem row11 : (List.range 16).all (fun n => pulseCheck ((n:ℤ)+(64))) = true := by decide +kernel
private theorem row12 : (List.range 16).all (fun n => pulseCheck ((n:ℤ)+(80))) = true := by decide +kernel
private theorem row13 : (List.range 16).all (fun n => pulseCheck ((n:ℤ)+(96))) = true := by decide +kernel

theorem solution (j : ℤ) (hl : -112 ≤ j) (hr : j < 112) : pulseCheck j = true := by
  by_cases h0 : j < -96
  · have h := List.all_eq_true.mp row0 (j-(-112)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-112)).toNat:ℤ)+(-112)=j by omega] using h
  by_cases h1 : j < -80
  · have h := List.all_eq_true.mp row1 (j-(-96)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-96)).toNat:ℤ)+(-96)=j by omega] using h
  by_cases h2 : j < -64
  · have h := List.all_eq_true.mp row2 (j-(-80)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-80)).toNat:ℤ)+(-80)=j by omega] using h
  by_cases h3 : j < -48
  · have h := List.all_eq_true.mp row3 (j-(-64)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-64)).toNat:ℤ)+(-64)=j by omega] using h
  by_cases h4 : j < -32
  · have h := List.all_eq_true.mp row4 (j-(-48)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-48)).toNat:ℤ)+(-48)=j by omega] using h
  by_cases h5 : j < -16
  · have h := List.all_eq_true.mp row5 (j-(-32)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-32)).toNat:ℤ)+(-32)=j by omega] using h
  by_cases h6 : j < 0
  · have h := List.all_eq_true.mp row6 (j-(-16)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(-16)).toNat:ℤ)+(-16)=j by omega] using h
  by_cases h7 : j < 16
  · have h := List.all_eq_true.mp row7 (j-(0)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(0)).toNat:ℤ)+(0)=j by omega] using h
  by_cases h8 : j < 32
  · have h := List.all_eq_true.mp row8 (j-(16)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(16)).toNat:ℤ)+(16)=j by omega] using h
  by_cases h9 : j < 48
  · have h := List.all_eq_true.mp row9 (j-(32)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(32)).toNat:ℤ)+(32)=j by omega] using h
  by_cases h10 : j < 64
  · have h := List.all_eq_true.mp row10 (j-(48)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(48)).toNat:ℤ)+(48)=j by omega] using h
  by_cases h11 : j < 80
  · have h := List.all_eq_true.mp row11 (j-(64)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(64)).toNat:ℤ)+(64)=j by omega] using h
  by_cases h12 : j < 96
  · have h := List.all_eq_true.mp row12 (j-(80)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(80)).toNat:ℤ)+(80)=j by omega] using h
  have h := List.all_eq_true.mp row13 (j-(96)).toNat (List.mem_range.mpr (by omega))
  simpa only [show ((j-(96)).toNat:ℤ)+(96)=j by omega] using h
