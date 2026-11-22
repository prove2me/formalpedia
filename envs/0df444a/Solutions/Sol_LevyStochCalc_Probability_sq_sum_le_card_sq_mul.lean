-- Prove2me | solution 1 for LevyStochCalc.Probability.sq_sum_le_card_sq_mul
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:46:28.52695+00:00
-- url     : https://prove2.me/submissions/f788188f-3c61-4444-a514-2df3a48b3668

import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Doob's `L²` maximal inequality in continuous time

For a right-continuous martingale on `[0, T]`, the supremum of the paths over the window is
square integrable, with `𝔼[sup_{t ≤ T} |M_t|²] ≤ 4 𝔼[|M_T|²]`.

The discrete inequality is `MeasureTheory.Martingale.eLpNorm_norm_runMax_le`; the passage to
continuous time samples the martingale along the dyadic partition of `[0, T]`, whose points are
increasing in the level, and uses right-continuity to identify the supremum over the window with
the supremum of the sampled maxima.

## Main statements

* `Filtration.compMono`, `martingale_compMono` — sampling along a monotone time map.
* `dyadicTime` — the dyadic partition points of `[0, T]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Sampling along a monotone time map -/

/-! ### The dyadic partition of `[0, T]` -/

/-! ### The sampled running maxima -/

variable {M : ℝ → Ω → ℝ} {T : ℝ}

/-! ### The supremum over the window -/

/-! ### Doob's `L²` inequality in continuous time -/

/-! ### Bounding the supremum over the window -/

/-! ### Finite sums -/



theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ≥0∞) ^ 2 * ∑ i ∈ s, f i ^ 2 := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨i, hi, hmax⟩ := s.exists_max_image f hs
    have h₁ : (∑ j ∈ s, f j) ≤ ∑ _j ∈ s, f i :=
      Finset.sum_le_sum fun j hj => hmax j hj
    have h₂ : f i ^ 2 ≤ ∑ j ∈ s, f j ^ 2 :=
      Finset.single_le_sum (f := fun j => f j ^ 2) (fun j _ => bot_le) hi
    change (∑ j ∈ s, f j) ^ 2 ≤ _
    calc
      _ ≤ (∑ _j ∈ s, f i) ^ 2 := by gcongr
      _ = (s.card : ℝ≥0∞) ^ 2 * f i ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul, mul_pow]
      _ ≤ _ := by gcongr
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
