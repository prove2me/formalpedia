-- Prove2me | solution 1 for LevyStochCalc.Probability.iSup_enorm_eq_iSup_dyadicRunMax
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:57:15.764862+00:00
-- url     : https://prove2.me/submissions/82e62a25-ad79-4ca8-bd17-d31478985fd7

import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F001

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



theorem _root_.solution (hT : 0 ≤ T) {ω : Ω}
    (hcad : ∀ t : ℝ, Filter.Tendsto (fun s => M s ω) (nhdsWithin t (Set.Ioi t))
      (nhds (M t ω))) :
    (⨆ t : Set.Icc (0 : ℝ) T, (‖M (t : ℝ) ω‖₊ : ℝ≥0∞))
      = ⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by
  apply le_antisymm
  · refine iSup_le (fun ⟨t, ht0, htT⟩ => ?_)
    -- every sampled value is below the right side
    have hpt : ∀ (n k : ℕ), k ≤ 2 ^ n →
        (‖M (dyadicTime T n k) ω‖₊ : ℝ≥0∞) ≤ ⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by
      intro n k hk
      refine le_trans ?_ (le_iSup _ n)
      have h1 : ‖M (dyadicTime T n k) ω‖ ≤ dyadicRunMax M T n ω :=
        Finset.le_sup' (f := fun k => ‖M (dyadicTime T n k) ω‖)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
      have h2 : ‖M (dyadicTime T n k) ω‖₊ ≤ ‖dyadicRunMax M T n ω‖₊ := by
        rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
          Real.norm_of_nonneg (dyadicRunMax_nonneg M T n ω)]
        exact h1
      exact_mod_cast h2
    rcases hT.eq_or_lt with h0 | hpos
    · subst h0
      have : t = 0 := le_antisymm htT ht0
      subst this
      have := hpt 0 0 (by norm_num)
      simpa [dyadicTime] using this
    · have hcw : ContinuousWithinAt (fun s => M s ω) (Set.Ici t) t :=
        continuousWithinAt_Ioi_iff_Ici.mp (hcad t)
      have hlim : Filter.Tendsto (fun n => (‖M (dyadicTime T n (dyadicIndex T t n)) ω‖₊ : ℝ≥0∞))
          Filter.atTop (nhds (‖M t ω‖₊ : ℝ≥0∞)) := by
        have := hcw.tendsto.comp (tendsto_dyadicTime_dyadicIndex hpos ht0 htT)
        exact (ENNReal.continuous_coe.comp continuous_nnnorm).continuousAt.tendsto.comp this
      exact le_of_tendsto' hlim (fun n => hpt n _ (dyadicIndex_le hpos htT n))
  · refine iSup_le (fun n => ?_)
    obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_range_add_one (n := 2 ^ n))
      (fun k => ‖M (dyadicTime T n k) ω‖)
    have : dyadicRunMax M T n ω = ‖M (dyadicTime T n k) ω‖ := hkeq
    rw [this, nnnorm_norm]
    exact le_iSup (fun t : Set.Icc (0 : ℝ) T => (‖M (t : ℝ) ω‖₊ : ℝ≥0∞))
      ⟨dyadicTime T n k, dyadicTime_mem_Icc hT n k⟩

