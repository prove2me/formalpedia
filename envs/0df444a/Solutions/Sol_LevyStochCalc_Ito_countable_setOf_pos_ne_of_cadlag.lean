-- Prove2me | solution 1 for LevyStochCalc.Ito.countable_setOf_pos_ne_of_cadlag
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:18:35.607097+00:00
-- url     : https://prove2.me/submissions/8120566a-3f23-4a49-8449-17504d15cbd3

import Definitions.Def_LevyStochCalc_Ito_JumpIntegrandLeftLim_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integrands evaluated along the left limits of a path

A path in `ℝⁿ` that is right continuous on `[0, ∞)` and has left limits at every positive time
meets those left limits off a countable, hence Lebesgue null, set of times. An integrand
evaluated along such a path and the same integrand evaluated along a process that meets the path
at all but countably many positive times therefore agree almost everywhere for the product of the
sample measure, Lebesgue measure on the horizon and the mark measure, so the compensated integral
takes the same value on the two integrands; the same null set serves the iterated integral
against the mark measure and Lebesgue measure and the integral against the reference intensity.

The identification is one of `L²` classes: it concerns the compensated integral constructed from
the energy isometry, not a pathwise Stieltjes integral against the jump measure, for which the
two conventions differ.

## Main statements

* `countable_setOf_pos_ne_of_cadlag` — a path right continuous on `[0, ∞)` differs from its left
  limits at only countably many positive times.
* `compensatedIntegral_congr_of_countable_ne` — the compensated integrals of an integrand
  evaluated along two processes meeting at all but countably many positive times agree almost
  surely.
* `setIntegral_congr_of_countable_ne` and
  `setIntegral_referenceIntensity_congr_of_countable_ne` — the same for the compensator drift
  term, in its iterated and its product-measure form.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito

universe u v w

section Cadlag

variable {n : ℕ}

theorem _root_.solution {f g : ℝ → Fin n → ℝ}
    (hright : ∀ t : ℝ, 0 ≤ t → Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ t : ℝ, 0 < t → ∀ i : Fin n,
      Tendsto (fun s => f s i) (𝓝[<] t) (𝓝 (g t i))) :
    {t : ℝ | 0 < t ∧ f t ≠ g t}.Countable := by
  set f' : ℝ → Fin n → ℝ := fun t => f (max t 0) with hf'
  have hpos : ∀ s : ℝ, 0 ≤ s → f' s = f s := fun s hs => by simp [f', max_eq_left hs]
  have hneg : ∀ s : ℝ, s ≤ 0 → f' s = f 0 := fun s hs => by simp [f', max_eq_right hs]
  have hleftf : ∀ t, 0 < t → ∀ i, Tendsto (fun s => f' s i) (𝓝[<] t) (𝓝 (g t i)) := by
    intro t ht i
    refine (hleft t ht i).congr' ?_
    filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds ht)] with s hs
    rw [hpos s hs.le]
  have hright' : ∀ t, Tendsto f' (𝓝[>] t) (𝓝 (f' t)) := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · rw [hneg t ht.le]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds ht)] with s hs
      rw [hneg s hs.le]
    · rw [hpos t ht]
      refine (hright t ht).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s (hs : t < s)
      rw [hpos s (ht.trans hs.le)]
  have hleft' : ∀ (t : ℝ) (i : Fin n), ∃ L : ℝ, Tendsto (fun s => f' s i) (𝓝[<] t) (𝓝 L) := by
    intro t i
    by_cases ht : 0 < t
    · exact ⟨g t i, hleftf t ht i⟩
    · refine ⟨f 0 i, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s (hs : s < t)
      rw [hneg s (by linarith [not_lt.1 ht])]
  have hc := countable_setOf_ne_leftLim_pi hright' hleft'
  refine hc.mono fun t ht => ?_
  obtain ⟨ht0, hne⟩ := ht
  simp only [Set.mem_setOf_eq]
  intro heq
  apply hne
  funext i
  have hl : Function.leftLim (fun s => f' s i) t = g t i :=
    leftLim_eq_of_tendsto (hleftf t ht0 i)
  have := congrFun heq i
  rw [hl, hpos t ht0.le] at this
  exact this

end Cadlag

end LevyStochCalc.Ito
