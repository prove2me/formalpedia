-- Prove2me | solution 1 for LevyStochCalc.integral_abs_add_four_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:49:08.442744+00:00
-- url     : https://prove2.me/submissions/90dc6a03-f21c-416f-a4be-707d627e2e90

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# First absolute moment from a second-moment bound

On a probability space the first absolute moment of a real random variable is bounded by the
square root of its second moment.

## Main statements

* `LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le` — `𝔼|f| ≤ √V` whenever `𝔼f² ≤ V`.
* `LevyStochCalc.integral_abs_le_of_bounded` — `𝔼|f| ≤ K` for `|f| ≤ K`.
* `LevyStochCalc.integral_abs_add_four_le` — the triangle inequality for four summands.
-/

namespace LevyStochCalc

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]



theorem _root_.solution {P : Measure Ω} [IsProbabilityMeasure P]
    {a b c d : Ω → ℝ} (ha : Integrable a P) (hb : Integrable b P) (hc : Integrable c P)
    (hd : Integrable d P) {A B C D : ℝ} (hA : ∫ ω, |a ω| ∂P ≤ A)
    (hB : ∫ ω, |b ω| ∂P ≤ B) (hC : ∫ ω, |c ω| ∂P ≤ C) (hD : ∫ ω, |d ω| ∂P ≤ D) :
    ∫ ω, |a ω + b ω + c ω + d ω| ∂P ≤ A + B + C + D := by
  have h1 : ∫ ω, |a ω + b ω + c ω + d ω| ∂P ≤ ∫ ω, (|a ω| + |b ω| + |c ω| + |d ω|) ∂P := by
    refine integral_mono (((ha.add hb).add hc).add hd).abs
      (((ha.abs.add hb.abs).add hc.abs).add hd.abs) fun ω => ?_
    simp only
    calc |a ω + b ω + c ω + d ω| ≤ |a ω + b ω + c ω| + |d ω| := abs_add_le _ _
      _ ≤ |a ω + b ω| + |c ω| + |d ω| := by gcongr; exact abs_add_le _ _
      _ ≤ |a ω| + |b ω| + |c ω| + |d ω| := by gcongr; exact abs_add_le _ _
  have h2 : ∫ ω, (|a ω| + |b ω| + |c ω| + |d ω|) ∂P =
      ∫ ω, |a ω| ∂P + ∫ ω, |b ω| ∂P + ∫ ω, |c ω| ∂P + ∫ ω, |d ω| ∂P := by
    rw [integral_add (f := fun ω => |a ω| + |b ω| + |c ω|) (g := fun ω => |d ω|)
        ((ha.abs.add hb.abs).add hc.abs) hd.abs,
      integral_add (f := fun ω => |a ω| + |b ω|) (g := fun ω => |c ω|)
        (ha.abs.add hb.abs) hc.abs,
      integral_add (f := fun ω => |a ω|) (g := fun ω => |b ω|) ha.abs hb.abs]
  linarith
