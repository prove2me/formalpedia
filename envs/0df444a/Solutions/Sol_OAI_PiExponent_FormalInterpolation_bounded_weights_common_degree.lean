-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_weights_common_degree
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:42:45.318989+00:00
-- url     : https://prove2.me/submissions/d2ba5d72-86f6-4356-a190-d8baf79b7e89

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_weights_common_degree_rounding
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_weights_common_degree_slack

theorem solution
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i : Fin d, 0 < (w i : Real))
    (R : Real) (s : Nat) (hs : 0 < s) (B : Nat)
    (hBR : (B : Real) < (s : Real) * R)
    (L : Nat) (hL : 0 < L) (c : Fin d → Nat)
    (hc : ∀ i : Fin d, 0 < c i ∧ (c i : Real) * (w i : Real) = (L : Real))
    (n : Fin d → Nat)
    (hn : ∀ i : Fin d, 0 < n i ∧ (n i : Real) * (w i : Real) ≤ (B : Real)) :
    ∃ q : Nat, ∃ D : Nat, 0 < q ∧ 0 < D ∧
      (D : Real) < ((s * q : Nat) : Real) * R ∧
      ∀ i : Fin d, ∃ m : Nat,
        q * n i ≤ m ∧ 0 < m ∧ (m : Real) * (w i : Real) = (D : Real) := by
  obtain ⟨Q, hslack⟩ :=
    OAI.PiExponent.FormalInterpolation.bounded_weights_common_degree_slack
      R s hs B hBR L hL
  obtain ⟨q, D, hq, hQq, hD, hbound, hcoords⟩ :=
    OAI.PiExponent.FormalInterpolation.bounded_weights_common_degree_rounding
      w hw B L hL c hc n hn Q
  exact ⟨q, D, hq, hD, lt_of_le_of_lt hbound (hslack q hQq), hcoords⟩