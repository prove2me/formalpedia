-- Prove2me | solution 1 for MasulloAudit.inertia_groupoid_printed_composition_leaves_fibre_product
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:17:30.17508+00:00
-- url     : https://prove2.me/submissions/aeee548c-a0b1-4441-a44b-c1633564d1dd

import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Common

set_option autoImplicit false

theorem solution :
    ∃ (s t : Bool × Bool → Bool) (c : Bool × Bool → Bool × Bool → Bool × Bool)
      (e : Bool → Bool × Bool) (i : Bool × Bool → Bool × Bool),
      (∀ x y, s x = t y → t (c x y) = t x ∧ s (c x y) = s y) ∧
      (∀ x y z, s x = t y → s y = t z → c x (c y z) = c (c x y) z) ∧
      (∀ a, s (e a) = a ∧ t (e a) = a) ∧
      (∀ x, c x (e (s x)) = x ∧ c (e (t x)) x = x) ∧
      (∀ x, s (i x) = t x ∧ t (i x) = s x) ∧
      (∀ x, c x (i x) = e (t x) ∧ c (i x) x = e (s x)) ∧
      ∃ r g r' g' : Bool × Bool,
        s g = t g ∧ s r = s g ∧
        s g' = t g' ∧ s r' = s g' ∧
        g = c r' (c g' (i r')) ∧
        s (c r r') ≠ s g := by
  refine ⟨fun p => p.1, fun p => p.2, fun x y => (y.1, x.2), fun a => (a, a),
    fun p => (p.2, p.1), ?_, ?_, ?_, ?_, ?_, ?_,
    (true, true), (true, true), (false, true), (false, false), ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
