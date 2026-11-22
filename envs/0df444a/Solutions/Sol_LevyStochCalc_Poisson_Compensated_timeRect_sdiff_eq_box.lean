-- Prove2me | solution 1 for LevyStochCalc.Poisson.Compensated.timeRect_sdiff_eq_box
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:45:25.638492+00:00
-- url     : https://prove2.me/submissions/8e0215d3-dc65-4e8b-85fb-9909fc029f1e

import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Clamped compensator and increment boxes of the compensated simple integral

The compensator `∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds` of the quadratic variation in its explicit
clamped form `∑_i ν̂(timeRect i t) · ξᵢ²`, the a.e. decomposition of the increment
`simpleIntegral t − simpleIntegral s` over the increment rectangles
`timeRect i t \ timeRect i s` (each a clean box `Ioc a b ×ˢ Aᵢ`), and the box-level moment
identities behind the set-level isometry: independence of a future box increment from the
past, the weighted diagonal second moment, the vanishing of the weighted off-diagonal cross
terms, and cross-integrability of two compensated masses.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Clamped compensator

The compensator of the quadratic variation, `∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds`, in its
explicit clamped form `∑_i (referenceIntensity ν (timeRect i t)) · ξᵢ²`. -/

/-! ### Increment decomposition

The increment `simpleIntegral t − simpleIntegral s` decomposes (a.e.) over the
increment rectangles `timeRect i t \ timeRect i s`, the basis for the set-level
quadratic-variation isometry. -/



theorem _root_.solution
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) {s t : ℝ} (hst : s ≤ t) :
    φ.timeRect i t \ φ.timeRect i s
      = Set.Ioc (max s (min (φ.partition i.castSucc) t))
          (max s (min (φ.partition i.succ) t)) ×ˢ φ.A i := by
  ext p
  let a := φ.partition i.castSucc
  let b := φ.partition i.succ
  have hb (u : ℝ) : p ∈ φ.timeRect i u ↔
      (a < p.1 ∧ p.1 ≤ b ∧ p.1 ≤ u) ∧ p.2 ∈ φ.A i := by
    simp only [SimplePredictable.timeRect, Set.mem_prod, Set.mem_Ioc, le_min_iff]
    constructor
    · rintro ⟨⟨hl, hB, hu⟩, hA⟩
      have hL : a < p.1 := (min_lt_iff.mp hl).resolve_right (not_lt_of_ge hu)
      exact ⟨⟨hL, hB, hu⟩, hA⟩
    · rintro ⟨⟨hL, hB, hu⟩, hA⟩
      exact ⟨⟨(min_le_left _ _).trans_lt hL, hB, hu⟩, hA⟩
  simp only [Set.mem_sdiff, hb, Set.mem_prod, Set.mem_Ioc, max_lt_iff, le_max_iff,
    min_lt_iff, le_min_iff]
  constructor
  · rintro ⟨⟨⟨ha, hB, ht⟩, hA⟩, hn⟩
    have hs : s < p.1 := lt_of_not_ge fun h => hn ⟨⟨ha, hB, h⟩, hA⟩
    exact ⟨⟨⟨hs, Or.inl ha⟩, Or.inr ⟨hB, ht⟩⟩, hA⟩
  · rintro ⟨⟨⟨hs, hl⟩, hu⟩, hA⟩
    obtain ⟨hB, ht⟩ := hu.resolve_left (not_le_of_gt hs)
    exact ⟨⟨⟨hl.resolve_right (not_lt_of_ge ht), hB, ht⟩, hA⟩,
      fun h => (not_le_of_gt hs) h.1.2.2⟩
