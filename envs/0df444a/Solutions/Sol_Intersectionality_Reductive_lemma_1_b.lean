-- Prove2me | solution 1 for Intersectionality.Reductive.lemma_1_b
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:06:13.090869+00:00
-- url     : https://prove2.me/submissions/349b6ce4-32c4-423a-91c9-ee0c56dd0a30

import Mathlib
import Definitions.Def_Intersectionality_Reductive_Setting

set_option autoImplicit false

theorem solution (X : Set ℝ) (Q : Set (↥X → ↥X)) (hQ : Intersectionality.Generic.IsPolicyFamily Q) :
    ∀ x y : ↥X, ∀ q ∈ Q, ∀ q' ∈ Q, q x = y → q' x = y → q = q' := by
  intro x y q hq q' hq' h1 h2
  funext w
  obtain ⟨r, hr, hrx⟩ := hQ.rich x w
  have e1 : q w = r (q x) := by
    rw [← hrx]; exact congrFun (hQ.comm q hq r hr) x
  have e2 : q' w = r (q' x) := by
    rw [← hrx]; exact congrFun (hQ.comm q' hq' r hr) x
  rw [e1, e2, h1, h2]
