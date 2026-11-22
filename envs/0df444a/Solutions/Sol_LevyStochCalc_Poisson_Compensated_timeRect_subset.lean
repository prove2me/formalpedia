-- Prove2me | solution 1 for LevyStochCalc.Poisson.Compensated.timeRect_subset
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:45:25.524611+00:00
-- url     : https://prove2.me/submissions/21b19486-6a24-4579-8f0b-fe8dc38a7844

import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F001

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
    φ.timeRect i s ⊆ φ.timeRect i t := by
  intro p hp
  simp only [SimplePredictable.timeRect, Set.mem_prod, Set.mem_Ioc, le_min_iff] at hp ⊢
  obtain ⟨⟨hl, hB, hs⟩, hA⟩ := hp
  have hlow : φ.partition i.castSucc < p.1 := by
    rcases min_lt_iff.mp hl with h | h
    · exact h
    · exact (not_lt_of_ge hs h).elim
  exact ⟨⟨(min_le_left _ _).trans_lt hlow, hB, hs.trans hst⟩, hA⟩
