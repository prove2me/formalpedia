-- Prove2me | solution 1 for Kyprianou.Ch01.firstNegativePassageAfterPositiveInterval
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:04:39.354031+00:00
-- url     : https://prove2.me/submissions/1c9e201e-61b2-4c10-a229-2dc9441a4c15

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Basic
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open Kyprianou.Ch01
set_option autoImplicit false

theorem solution
    {Ω : Type*} (X : NNReal → Ω → ℤ) (ω : Ω) (t : NNReal)
    (hpositive : ∀ s : NNReal, s ≤ t → 0 < X s ω) :
    (t : WithTop NNReal) ≤ firstNegativePassage X ω := by
  unfold firstNegativePassage
  split_ifs with h
  · obtain ⟨u, hu⟩ := h
    apply WithTop.coe_le_coe.mpr
    apply le_csInf ⟨u, hu⟩
    rintro s ⟨-, hs⟩
    by_contra hlt0
    have hlt := not_le.mp hlt0
    exact absurd (hpositive s hlt.le) (not_lt.mpr hs.le)
  · exact le_top
