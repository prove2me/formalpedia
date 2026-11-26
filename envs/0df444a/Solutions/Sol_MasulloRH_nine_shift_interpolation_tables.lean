-- Prove2me | solution 1 for MasulloRH.nine_shift_interpolation_tables
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T21:38:00.69632+00:00
-- url     : https://prove2.me/submissions/30d2fb13-f248-4b4f-9e80-0d1861faa2db

import Definitions.Def_MasulloRH_NineShiftWindows
import Mathlib.Tactic.IntervalCases

open MasulloRH.NineShift
set_option maxRecDepth 160000
set_option maxHeartbeats 8000000

private theorem t0 : (List.range 8).all (fun n => let j : ℤ := (n:ℤ) + (-48); thetaCheck j (thetaRow j)) = true := by decide +kernel
private theorem t8 : (List.range 8).all (fun n => let j : ℤ := (n:ℤ) + (-40); thetaCheck j (thetaRow j)) = true := by decide +kernel
private theorem t16 : (List.range 8).all (fun n => let j : ℤ := (n:ℤ) + (-32); thetaCheck j (thetaRow j)) = true := by decide +kernel
private theorem t24 : (List.range 8).all (fun n => let j : ℤ := (n:ℤ) + (-24); thetaCheck j (thetaRow j)) = true := by decide +kernel
private theorem t32 : (List.range 8).all (fun n => let j : ℤ := (n:ℤ) + (-16); thetaCheck j (thetaRow j)) = true := by decide +kernel
private theorem t40 : (List.range 8).all (fun n => let j : ℤ := (n:ℤ) + (-8); thetaCheck j (thetaRow j)) = true := by decide +kernel
private theorem t48 : (List.range 8).all (fun n => let j : ℤ := (n:ℤ) + (0); thetaCheck j (thetaRow j)) = true := by decide +kernel
private theorem t56 : (List.range 8).all (fun n => let j : ℤ := (n:ℤ) + (8); thetaCheck j (thetaRow j)) = true := by decide +kernel
private theorem t64 : (List.range 8).all (fun n => let j : ℤ := (n:ℤ) + (16); thetaCheck j (thetaRow j)) = true := by decide +kernel
private theorem p0 : (List.range 16).all (fun n => let j : ℤ := (n:ℤ) + (-96); pulseCheck j (pulseRow j) && weightCheck j) = true := by decide +kernel
private theorem p16 : (List.range 16).all (fun n => let j : ℤ := (n:ℤ) + (-80); pulseCheck j (pulseRow j) && weightCheck j) = true := by decide +kernel
private theorem p32 : (List.range 16).all (fun n => let j : ℤ := (n:ℤ) + (-64); pulseCheck j (pulseRow j) && weightCheck j) = true := by decide +kernel
private theorem p48 : (List.range 16).all (fun n => let j : ℤ := (n:ℤ) + (-48); pulseCheck j (pulseRow j) && weightCheck j) = true := by decide +kernel
private theorem p64 : (List.range 16).all (fun n => let j : ℤ := (n:ℤ) + (-32); pulseCheck j (pulseRow j) && weightCheck j) = true := by decide +kernel
private theorem p80 : (List.range 16).all (fun n => let j : ℤ := (n:ℤ) + (-16); pulseCheck j (pulseRow j) && weightCheck j) = true := by decide +kernel
private theorem p96 : (List.range 16).all (fun n => let j : ℤ := (n:ℤ) + (0); pulseCheck j (pulseRow j) && weightCheck j) = true := by decide +kernel
private theorem p112 : (List.range 16).all (fun n => let j : ℤ := (n:ℤ) + (16); pulseCheck j (pulseRow j) && weightCheck j) = true := by decide +kernel
private theorem p128 : (List.range 16).all (fun n => let j : ℤ := (n:ℤ) + (32); pulseCheck j (pulseRow j) && weightCheck j) = true := by decide +kernel
private theorem p144 : (List.range 16).all (fun n => let j : ℤ := (n:ℤ) + (48); pulseCheck j (pulseRow j) && weightCheck j) = true := by decide +kernel
private theorem p160 : (List.range 16).all (fun n => let j : ℤ := (n:ℤ) + (64); pulseCheck j (pulseRow j) && weightCheck j) = true := by decide +kernel
private theorem p176 : (List.range 16).all (fun n => let j : ℤ := (n:ℤ) + (80); pulseCheck j (pulseRow j) && weightCheck j) = true := by decide +kernel

theorem solution :
    (∀ j : ℤ, -48 ≤ j → j < 24 → thetaCheck j (thetaRow j) = true) ∧
    (∀ j : ℤ, -96 ≤ j → j < 96 → (pulseCheck j (pulseRow j) && weightCheck j) = true) ∧
    (∑ n ∈ Finset.range 192, cellCost ((n:ℤ)-96)) ≤ (59/1000000:ℚ) := by
  refine ⟨?_,?_,?_⟩
  · intro j hL hR
    by_cases u : j < -40
    · have h := List.all_eq_true.mp t0 (j-(-48)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(-48)).toNat:ℤ)+(-48)=j by omega] using h
    by_cases u : j < -32
    · have h := List.all_eq_true.mp t8 (j-(-40)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(-40)).toNat:ℤ)+(-40)=j by omega] using h
    by_cases u : j < -24
    · have h := List.all_eq_true.mp t16 (j-(-32)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(-32)).toNat:ℤ)+(-32)=j by omega] using h
    by_cases u : j < -16
    · have h := List.all_eq_true.mp t24 (j-(-24)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(-24)).toNat:ℤ)+(-24)=j by omega] using h
    by_cases u : j < -8
    · have h := List.all_eq_true.mp t32 (j-(-16)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(-16)).toNat:ℤ)+(-16)=j by omega] using h
    by_cases u : j < 0
    · have h := List.all_eq_true.mp t40 (j-(-8)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(-8)).toNat:ℤ)+(-8)=j by omega] using h
    by_cases u : j < 8
    · have h := List.all_eq_true.mp t48 (j-(0)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(0)).toNat:ℤ)+(0)=j by omega] using h
    by_cases u : j < 16
    · have h := List.all_eq_true.mp t56 (j-(8)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(8)).toNat:ℤ)+(8)=j by omega] using h
    have h := List.all_eq_true.mp t64 (j-(16)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(16)).toNat:ℤ)+(16)=j by omega] using h
  · intro j hL hR
    by_cases u : j < -80
    · have h := List.all_eq_true.mp p0 (j-(-96)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(-96)).toNat:ℤ)+(-96)=j by omega] using h
    by_cases u : j < -64
    · have h := List.all_eq_true.mp p16 (j-(-80)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(-80)).toNat:ℤ)+(-80)=j by omega] using h
    by_cases u : j < -48
    · have h := List.all_eq_true.mp p32 (j-(-64)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(-64)).toNat:ℤ)+(-64)=j by omega] using h
    by_cases u : j < -32
    · have h := List.all_eq_true.mp p48 (j-(-48)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(-48)).toNat:ℤ)+(-48)=j by omega] using h
    by_cases u : j < -16
    · have h := List.all_eq_true.mp p64 (j-(-32)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(-32)).toNat:ℤ)+(-32)=j by omega] using h
    by_cases u : j < 0
    · have h := List.all_eq_true.mp p80 (j-(-16)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(-16)).toNat:ℤ)+(-16)=j by omega] using h
    by_cases u : j < 16
    · have h := List.all_eq_true.mp p96 (j-(0)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(0)).toNat:ℤ)+(0)=j by omega] using h
    by_cases u : j < 32
    · have h := List.all_eq_true.mp p112 (j-(16)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(16)).toNat:ℤ)+(16)=j by omega] using h
    by_cases u : j < 48
    · have h := List.all_eq_true.mp p128 (j-(32)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(32)).toNat:ℤ)+(32)=j by omega] using h
    by_cases u : j < 64
    · have h := List.all_eq_true.mp p144 (j-(48)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(48)).toNat:ℤ)+(48)=j by omega] using h
    by_cases u : j < 80
    · have h := List.all_eq_true.mp p160 (j-(64)).toNat (List.mem_range.mpr (by omega))
      simpa only [show ((j-(64)).toNat:ℤ)+(64)=j by omega] using h
    have h := List.all_eq_true.mp p176 (j-(80)).toNat (List.mem_range.mpr (by omega))
    simpa only [show ((j-(80)).toNat:ℤ)+(80)=j by omega] using h
  · decide +kernel
