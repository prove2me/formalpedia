-- Prove2me | solution 1 for Kyprianou.Ch05.renewalTailIntegralEqV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:45:33.713712+00:00
-- url     : https://prove2.me/submissions/3c5b703e-bc2d-4c5a-941c-f9903bbb765f

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Translate the positive-tail integral, using the nonnegative cutoff. -/
theorem solution (F : Measure Real) (u y : Real) (hy : 0 ≤ y) :
    (∫ z in Ici (0 : Real),
      (if y < z then (F (Ioi (z + u))).toReal else 0) ∂volume) =
    ∫ z in Ioi (u + y), (F (Ioi z)).toReal ∂volume := by
  let g : Real → Real := fun z => (F (Ioi z)).toReal
  change (∫ z in Ici (0 : Real), (Ioi y).indicator (fun t => g (t+u)) z ∂volume) =
    ∫ z in Ioi (u+y), g z ∂volume
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    show Ioi y ∩ Ici (0 : Real) = Ioi y from
      inter_eq_left.mpr (fun z hz => hy.trans (mem_Ioi.mp hz).le)]
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have he : (Ioi y).indicator (fun t => g (t+u)) =
      fun t => (Ioi (u+y)).indicator g (t+u) := by
    funext t
    have ht : y < t ↔ u+y < t+u := by constructor <;> intro h <;> linarith
    simp only [indicator, mem_Ioi, ht]
  rw [he]
  exact integral_add_right_eq_self ((Ioi (u+y)).indicator g) u
