-- Prove2me | solution 1 for Kyprianou.Ch07.kestenOnefoldTailRatio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:46:25.030312+00:00
-- url     : https://prove2.me/submissions/cee9d09c-a4c1-4171-a4f2-33c6a0f2b87a

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_convolutionPowerOne
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (x : Real) (hx : 0 < x) :
    ((Kyprianou.Ch07.convolutionPower G 1) (Set.Ioi x)).toReal /
      (G (Set.Ioi x)).toReal = 1 := by
  rw [Kyprianou.Ch07.convolutionPowerOne]
  have hTop : G (Set.Ioi x) < ⊤ :=
    lt_of_le_of_lt (prob_le_one) (by norm_num)
  have hpos : 0 < (G (Set.Ioi x)).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hPositiveTail x hx, hTop⟩
  exact div_self (ne_of_gt hpos)
