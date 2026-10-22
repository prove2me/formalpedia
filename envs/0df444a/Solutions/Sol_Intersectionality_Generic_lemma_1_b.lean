-- Prove2me | solution 1 for Intersectionality.Generic.lemma_1_b
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:57:11.61806+00:00
-- url     : https://prove2.me/submissions/32ab1c01-0ff7-4dd8-b529-03c3749ce386

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting

set_option autoImplicit false

theorem solution (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (Q : Set (↥X → ↥X))
    (hQ : Intersectionality.Generic.IsPolicyFamily Q) :
    ∀ x y : ↥X, ∀ q ∈ Q, ∀ q' ∈ Q, q x = y → q' x = y → q = q' := by
  intro x y q hq q' hq' h1 h2
  funext w
  obtain ⟨r, hr, hrx⟩ := hQ.rich x w
  have e1 : q w = r (q x) := by
    rw [← hrx]; exact congrFun (hQ.comm q hq r hr) x
  have e2 : q' w = r (q' x) := by
    rw [← hrx]; exact congrFun (hQ.comm q' hq' r hr) x
  rw [e1, e2, h1, h2]
