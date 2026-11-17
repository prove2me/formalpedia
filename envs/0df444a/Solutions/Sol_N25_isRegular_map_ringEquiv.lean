-- Prove2me | solution 1 for N25.isRegular_map_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:36:00.223201+00:00
-- url     : https://prove2.me/submissions/dbd1eb2d-6830-4cba-95a4-54d6de7b0764

import Mathlib

/-! Regularity in monic root extensions and two-element regular-sequence swaps. -/
noncomputable section

namespace N25

open Polynomial

/-- Ring equivalences preserve regular elements. -/
theorem _root_.solution
    {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S)
    {r : R} (hr : IsRegular r) : IsRegular (e r) := by
  constructor
  · intro x y hxy
    apply e.symm.injective
    apply hr.left
    have h := congrArg e.symm hxy
    simpa only [map_mul, e.symm_apply_apply] using h
  · intro x y hxy
    apply e.symm.injective
    apply hr.right
    have h := congrArg e.symm hxy
    simpa only [map_mul, e.symm_apply_apply] using h

end N25
