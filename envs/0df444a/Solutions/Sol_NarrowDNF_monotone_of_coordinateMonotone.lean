-- Prove2me | solution 1 for NarrowDNF.monotone_of_coordinateMonotone
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:16:17.426206+00:00
-- url     : https://prove2.me/submissions/2d72f7fe-1d95-474d-bb10-5aaa66ab4b2a

import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_CoordinateShift

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

section


/-!
# Bias-matched shifts on a Boolean fiber

This file proves the two-point calculation used in Lemma 3.1 of
the 2026-11-06 STOC revision. The probability of the upper shift is `1 - p` and the
probability of the lower shift is `p`; the input fiber has the same bias `p`.

The error theorem is a conditional, single-fiber statement. Passing to an
arbitrary Boolean cube requires a separate summation/integration argument.
-/

namespace NarrowDNF.FiberShift

@[simp] private theorem true_not_le_false : ¬ ((true : Bool) ≤ false) := by decide



























end NarrowDNF.FiberShift


end

section


/-!
# Coordinate shifts on Boolean functions

The unbranched shift formulas are equivalent to the two-slice definitions in
the shift definitions preceding Lemma 3.1 of the 2026-11-06 STOC revision, by Boolean idempotence. This file concerns
monotonicity; the global biased-error bound requires a separate finite-sum
argument.
-/

namespace NarrowDNF

variable {ι : Type*} [DecidableEq ι]









@[simp] private theorem upperShift_lowerInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    upperShift i v (lowerInput i x) = v (lowerInput i x) := by
  simp [upperShift, lowerInput]

@[simp] private theorem upperShift_upperInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    upperShift i v (upperInput i x) = (v (lowerInput i x) || v (upperInput i x)) := by
  simp [upperShift, lowerInput, upperInput, Bool.or_comm]

@[simp] private theorem lowerShift_lowerInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    lowerShift i v (lowerInput i x) = (v (lowerInput i x) && v (upperInput i x)) := by
  simp [lowerShift, lowerInput, upperInput]

@[simp] private theorem lowerShift_upperInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    lowerShift i v (upperInput i x) = v (upperInput i x) := by
  simp [lowerShift, upperInput]



















private theorem coordinateMonotone_le_upperInput {i : ι} {v : Cube ι → Bool}
    (hv : CoordinateMonotone i v) (x : Cube ι) : v x ≤ v (upperInput i x) := by
  cases hxi : x i
  · have hx : lowerInput i x = x := by
      simpa only [lowerInput, hxi] using Function.update_eq_self i x
    simpa only [hx] using hv x
  · have hx : upperInput i x = x := by
      simpa only [upperInput, hxi] using Function.update_eq_self i x
    simp only [hx, le_refl]

private theorem coordinateMonotone_le_update {i : ι} {v : Cube ι → Bool}
    (hv : CoordinateMonotone i v) (x : Cube ι) (b : Bool) (hb : x i ≤ b) :
    v x ≤ v (Function.update x i b) := by
  cases b
  · have hxi : x i = false := Bool.eq_false_of_le_false hb
    have hx : Function.update x i false = x := by
      simpa only [hxi] using Function.update_eq_self i x
    simp only [hx, le_refl]
  · exact coordinateMonotone_le_upperInput hv x















end NarrowDNF


end

open NarrowDNF
variable {ι : Type*} [DecidableEq ι]
/-- On a finite cube, coordinatewise monotonicity implies the usual
pointwise-order monotonicity. The proof changes the coordinates one at a time. -/
theorem solution [Fintype ι] {v : Cube ι → Bool}
    (hv : ∀ i, CoordinateMonotone i v) : Monotone v := by
  have hfinite : ∀ (S : Finset ι) (x y : Cube ι), x ≤ y →
      (∀ i, i ∉ S → x i = y i) → v x ≤ v y := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x y _ hagree
      have hxy : x = y := funext fun i => hagree i (by simp)
      simp only [hxy, le_refl]
    | @insert i S _ ih =>
      intro x y hxy hagree
      let z := Function.update x i (y i)
      have hxz : v x ≤ v z := coordinateMonotone_le_update (hv i) x (y i) (hxy i)
      apply hxz.trans
      apply ih z y
      · intro j
        by_cases hji : j = i
        · subst j
          simp [z]
        · simpa [z, hji] using hxy j
      · intro j hjS
        by_cases hji : j = i
        · subst j
          simp [z]
        · simpa [z, hji] using hagree j (by simp [hji, hjS])
  intro x y hxy
  exact hfinite Finset.univ x y hxy (by simp)
