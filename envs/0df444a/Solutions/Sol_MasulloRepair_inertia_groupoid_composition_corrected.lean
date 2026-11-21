-- Prove2me | solution 1 for MasulloRepair.inertia_groupoid_composition_corrected
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:17:31.110076+00:00
-- url     : https://prove2.me/submissions/006c1837-0106-4c8e-acc7-079882bb9f75

import Mathlib.Logic.Basic
import Mathlib.Tactic.Common

set_option autoImplicit false

theorem solution
    {X R : Type*} (s t : R → X) (c : R → R → R) (e : X → R) (i : R → R)
    (hc : ∀ x y, s x = t y → t (c x y) = t x ∧ s (c x y) = s y)
    (hassoc : ∀ x y z, s x = t y → s y = t z → c x (c y z) = c (c x y) z)
    (he : ∀ a, s (e a) = a ∧ t (e a) = a)
    (hid : ∀ x, c x (e (s x)) = x ∧ c (e (t x)) x = x)
    (hi : ∀ x, s (i x) = t x ∧ t (i x) = s x)
    (hinv : ∀ x, c x (i x) = e (t x) ∧ c (i x) x = e (s x))
    (r g r' g' : R)
    (hg : s g = t g) (hr : s r = s g)
    (hg' : s g' = t g') (hr' : s r' = s g')
    (hgeq : g = c r' (c g' (i r'))) :
    s r = t r' ∧
    (s (c r r') = s g ↔ s r' = t r') ∧
    s (c r r') = s g' ∧
    c (c r r') (c g' (i (c r r'))) = c r (c g (i r)) := by
  -- composability bookkeeping
  have A1 : s g' = t (i r') := by rw [(hi r').2, hr']
  have A2 : s r' = t (c g' (i r')) := by rw [(hc _ _ A1).1, ← hg', hr']
  have hsg : s g = t r' := by
    rw [hgeq, (hc _ _ A2).2, (hc _ _ A1).2, (hi r').1]
  have B : s r = t r' := hr.trans hsg
  have hu := hc r r' B
  have C1 : s (i r') = t (i r) := by rw [(hi r').1, (hi r).2]; exact B.symm
  have hv := hc _ _ C1
  refine ⟨B, ?_, ?_, ?_⟩
  · rw [hu.2, hsg]
  · rw [hu.2, hr']
  · -- the inverse of a composite
    have hvr : c (c (i r') (i r)) r = i r' := by
      rw [← hassoc (i r') (i r) r C1 (hi r).1, (hinv r).2, B, ← (hi r').1]
      exact (hid (i r')).1
    have hvu : c (c (i r') (i r)) (c r r') = e (s r') := by
      rw [hassoc _ r r' (by rw [hv.2, (hi r).1]) B, hvr]
      exact (hinv r').2
    have iu : i (c r r') = c (i r') (i r) := by
      have h1 : c (c (i r') (i r)) (e (t (c r r'))) = c (i r') (i r) := by
        have := (hid (c (i r') (i r))).1
        rwa [hv.2, (hi r).1, ← hu.1] at this
      have h2 : c (e (s r')) (i (c r r')) = i (c r r') := by
        have := (hid (i (c r r'))).2
        rwa [(hi (c r r')).2, hu.2] at this
      rw [← h1, ← (hinv (c r r')).1,
        hassoc _ (c r r') (i (c r r')) (by rw [hv.2, (hi r).1, hu.1]) (hi (c r r')).2.symm,
        hvu, h2]
    -- now compare both sides
    have D1 : s (c g' (i r')) = t (i r) := by
      rw [(hc _ _ A1).2, (hi r').1, (hi r).2]; exact B.symm
    have D2 : s g' = t (c (i r') (i r)) := by rw [hv.1, (hi r').2, hr']
    have D3 : s r' = t (c g' (c (i r') (i r))) := by rw [(hc _ _ D2).1, ← hg', hr']
    rw [iu, hgeq, ← hassoc r' (c g' (i r')) (i r) A2 D1,
      ← hassoc g' (i r') (i r) A1 C1, hassoc r r' _ B D3]
