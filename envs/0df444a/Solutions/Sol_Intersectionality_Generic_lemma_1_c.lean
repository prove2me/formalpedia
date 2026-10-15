-- Prove2me | solution 1 for Intersectionality.Generic.lemma_1_c
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T13:52:54.061686+00:00
-- url     : https://prove2.me/submissions/57f9237d-9dbd-42e9-a937-c72b7970fe84

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting
open Intersectionality.Generic

theorem solution(X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (Q : Set (↥X → ↥X))
    (hQ : IsPolicyFamily Q) : (id : ↥X → ↥X) ∈ Q := by
  obtain ⟨x0⟩ := ‹Nonempty ↥X›
  obtain ⟨q, hq, hqx⟩ := hQ.rich x0 x0
  have hid : q = id := by
    funext y
    obtain ⟨q', hq', hq'x⟩ := hQ.rich x0 y
    have h := congrFun (hQ.comm q hq q' hq') x0
    simp only [Function.comp, hqx, hq'x] at h
    simpa using h
  exact hid ▸ hq
