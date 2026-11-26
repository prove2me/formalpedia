-- Prove2me | solution 1 for Kyprianou.Ch05.renewalCrossingIndexCharacterization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:00:40.884478+00:00
-- url     : https://prove2.me/submissions/7d230af1-5a9e-42da-a586-b38db5b7236e

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- First crossing index equals n+1 precisely at a strict crossing of a nondecreasing epoch sequence. -/
theorem solution
    {Omega : Type} (Z : Nat → Omega → Real) (w : Omega)
    (hmono : Monotone (fun n : Nat => renewalEpoch Z n w))
    (x : Real) (hx : 0 < x) (n : Nat) :
    (nextRenewalIndex Z x w = n+1 ∧ x < renewalEpoch Z (n+1) w) ↔
      (renewalEpoch Z n w ≤ x ∧ x < renewalEpoch Z (n+1) w) := by
  let T := fun n => renewalEpoch Z n w
  let E := {n : Nat | 0 < n ∧ x < T n}
  have h0 : T 0 = 0 := by simp [T,renewalEpoch]
  change (sInf E = n+1 ∧ x < T (n+1)) ↔ _
  constructor
  · rintro ⟨he,hp⟩
    refine ⟨?_,hp⟩
    by_contra! hn
    have hn0 : 0 < n := by
      by_contra! h
      have : n=0 := by omega
      change x < T n at hn
      rw [this,h0] at hn
      linarith
    have hle := Nat.sInf_le (show n ∈ E from ⟨hn0,hn⟩)
    omega
  · rintro ⟨hn,hp⟩
    have hm : n+1 ∈ E := ⟨by omega,hp⟩
    have hle := Nat.sInf_le hm
    have hmem := Nat.sInf_mem ⟨n+1,hm⟩
    have hlt : n < sInf E := by
      by_contra! h
      exact (not_lt_of_ge ((hmono h).trans hn)) hmem.2
    exact ⟨by omega,hp⟩
