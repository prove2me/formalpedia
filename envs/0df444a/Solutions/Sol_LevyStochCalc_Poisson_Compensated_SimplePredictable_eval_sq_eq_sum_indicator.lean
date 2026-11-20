-- Prove2me | solution 1 for LevyStochCalc.Poisson.Compensated.SimplePredictable.eval_sq_eq_sum_indicator
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:47:30.760766+00:00
-- url     : https://prove2.me/submissions/3788e90e-f26b-4b0b-bdff-5f616cb6facf

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Compensated Poisson integral: simple predictable integrands

The simple predictable integrands `φ = ∑_i ξ_i · 1_{(t_i, t_{i+1}] × A_i}` and
their integral `simpleIntegral` against the compensated Poisson measure
`Ñ(dt, de) := N(dt, de) − ν(de) dt`, with the indicator/rectangle bookkeeping
lemmas. The moment identities are in `Poisson/CompensatedMoments.lean`; the
L²-isometry in `Poisson/CompensatedIsometry.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.solution
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (s : ℝ) (e : E) (ω : Ω) :
    (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 = ∑ i : Fin φ.N,
      (φ.fullRect i).indicator (fun _ => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e) := by
  classical
  have hmem : ∀ i, (s, e) ∈ φ.fullRect i ↔
      (φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ ∧ e ∈ φ.A i) := by
    intro i
    simp only [SimplePredictable.fullRect, Set.mem_prod, Set.mem_Ioc, and_assoc]
  have huniq : ∀ i j, (s, e) ∈ φ.fullRect i → (s, e) ∈ φ.fullRect j → i = j := by
    intro i j hi hj
    rw [hmem] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hle : i.succ ≤ j.castSucc := Fin.succ_le_castSucc_iff.2 h
      have := φ.partition_strictMono.monotone hle
      linarith [hi.2.1, hj.1]
    · have hle : j.succ ≤ i.castSucc := Fin.succ_le_castSucc_iff.2 h
      have := φ.partition_strictMono.monotone hle
      linarith [hj.2.1, hi.1]
  by_cases h : ∃ i, (s, e) ∈ φ.fullRect i
  · obtain ⟨i0, hi0⟩ := h
    have hev : φ.eval s e ω = φ.ξ i0 ω := by
      rw [SimplePredictable.eval, Finset.sum_eq_single i0]
      · rw [if_pos ((hmem i0).1 hi0)]
      · intro j _ hj
        rw [if_neg]
        intro hc
        exact hj (huniq j i0 ((hmem j).2 hc) hi0)
      · intro h; exact absurd (Finset.mem_univ i0) h
    rw [hev, Finset.sum_eq_single i0]
    · rw [Set.indicator_of_mem hi0]
    · intro j _ hj
      rw [Set.indicator_of_notMem]
      intro hc
      exact hj (huniq j i0 hc hi0)
    · intro h; exact absurd (Finset.mem_univ i0) h
  · push_neg at h
    have hev : φ.eval s e ω = 0 := by
      rw [SimplePredictable.eval]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg]
      intro hc
      exact h j ((hmem j).2 hc)
    rw [hev]
    simp only [nnnorm_zero, ENNReal.coe_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    symm
    exact Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (h j) _

end LevyStochCalc.Poisson.Compensated
