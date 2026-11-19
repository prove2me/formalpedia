-- Prove2me | solution 1 for Kyprianou.Ch01.strictClockInverseBeforeHorizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:27:14.49084+00:00
-- url     : https://prove2.me/submissions/27e38e66-f13e-40e4-95cc-a7b00dfcc478

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

theorem solution
    (J : NNReal → ℝ) (hmono : Monotone J)
    (t horizon : NNReal) (ht : t < horizon)
    (hstrict : ∀ s : NNReal, t < s → s < horizon → J t < J s) :
    sInf {s : NNReal | J t < J s} = t := by
  let A : Set NNReal := {s | J t < J s}
  have hNonempty : A.Nonempty := by
    obtain ⟨u, htu, huH⟩ := exists_between ht
    exact ⟨u, hstrict u htu huH⟩
  have hBounded : BddBelow A := by
    refine ⟨t, ?_⟩
    intro s hs
    exact le_of_not_gt (fun hst => (not_lt_of_ge
      (hmono (le_of_lt hst))) hs)
  have hLower : t ≤ sInf A := by
    apply le_csInf hNonempty
    intro s hs
    exact le_of_not_gt (fun hst => (not_lt_of_ge
      (hmono (le_of_lt hst))) hs)
  have hUpper : sInf A ≤ t := by
    apply le_of_forall_gt
    intro u hu
    obtain ⟨s, hts, hsm⟩ := exists_between (lt_min hu ht)
    have hsH : s < horizon := lt_of_lt_of_le hsm (min_le_right u horizon)
    have hsU : s < u := lt_of_lt_of_le hsm (min_le_left u horizon)
    exact lt_of_le_of_lt (csInf_le hBounded (hstrict s hts hsH)) hsU
  exact le_antisymm hUpper hLower
