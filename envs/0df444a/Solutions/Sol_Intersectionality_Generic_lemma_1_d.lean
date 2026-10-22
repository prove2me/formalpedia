-- Prove2me | solution 1 for Intersectionality.Generic.lemma_1_d
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:43:08.135288+00:00
-- url     : https://prove2.me/submissions/f0f0cc87-cc73-4413-9cd0-18373e5147bb

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting

set_option autoImplicit false
open Intersectionality.Generic

theorem solution (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (Q : Set (↥X → ↥X))
    (hQ : IsPolicyFamily Q) : ∀ q ∈ Q, ∀ q' ∈ Q, q ∘ q' ∈ Q := by
  intro q hq q' hq'
  obtain ⟨x0⟩ := ‹Nonempty ↥X›
  obtain ⟨r, hr, hrx⟩ := hQ.rich x0 (q (q' x0))
  have : r = q ∘ q' := by
    funext z
    obtain ⟨s, hs, hsz⟩ := hQ.rich x0 z
    have h1 : r (s x0) = s (r x0) := congrFun (hQ.comm r hr s hs) x0
    have h2 : s (q (q' x0)) = q (s (q' x0)) := congrFun (hQ.comm s hs q hq) (q' x0)
    have h3 : s (q' x0) = q' (s x0) := congrFun (hQ.comm s hs q' hq') x0
    simp only [Function.comp]
    rw [← hsz, h1, hrx, h2, h3]
  rw [← this]; exact hr
