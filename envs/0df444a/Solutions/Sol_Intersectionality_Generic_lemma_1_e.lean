-- Prove2me | solution 1 for Intersectionality.Generic.lemma_1_e
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:42:32.628505+00:00
-- url     : https://prove2.me/submissions/4f09373c-6f10-49e5-92dc-484a01147831

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting

set_option autoImplicit false
open Intersectionality.Generic

theorem solution (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (Q : Set (↥X → ↥X))
    (hQ : IsPolicyFamily Q) :
    ∀ q ∈ Q, ∃ q' ∈ Q, q ∘ q' = id ∧ q' ∘ q = id := by
  intro q hq
  obtain ⟨x0⟩ := ‹Nonempty ↥X›
  obtain ⟨r, hr, hrx⟩ := hQ.rich (q x0) x0
  have hcomm : ∀ s ∈ Q, q (s x0) = s (q x0) := fun s hs =>
    congrFun (hQ.comm q hq s hs) x0
  have hrq : r ∘ q = id := by
    funext z
    obtain ⟨s, hs, hsz⟩ := hQ.rich x0 z
    have h1 : r (s (q x0)) = s (r (q x0)) := congrFun (hQ.comm r hr s hs) (q x0)
    simp only [Function.comp, id]
    rw [← hsz, hcomm s hs, h1, hrx]
  refine ⟨r, hr, ?_, hrq⟩
  have : q ∘ r = r ∘ q := hQ.comm q hq r hr
  rw [this, hrq]
