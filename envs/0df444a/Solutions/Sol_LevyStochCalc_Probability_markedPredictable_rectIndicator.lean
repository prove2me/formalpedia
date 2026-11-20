-- Prove2me | solution 1 for LevyStochCalc.Probability.markedPredictable_rectIndicator
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:22:09.850351+00:00
-- url     : https://prove2.me/submissions/515fa0ce-01c4-4e13-8d2b-46bedd40cc69

import Definitions.Def_LevyStochCalc_Probability_MarkedPredictable_F000

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Probability

universe u v w

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [MeasurableSpace E]

section Deterministic

variable {ℱ : Filtration ℝ mΩ} {ν : Measure E}

theorem _root_.solution {F : Type w} [MeasurableSpace F] [Zero F] {r q : ℝ}
    (hr : 0 ≤ r) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {c : Ω → F}
    (hc : Measurable[ℱ r] c) :
    MarkedPredictable ℱ ν fun (ω : Ω) (s : ℝ) (e : E) =>
      (Set.Ioc r q ×ˢ A).indicator (fun _ : ℝ × E => c ω) (s, e) := by
  have key : ∀ U : Set F, MeasurableSet U → (0 : F) ∉ U →
      MeasurableSet[markedPredictableSigma ℱ ν]
        ((fun p : Ω × ℝ × E =>
          (Set.Ioc r q ×ˢ A).indicator (fun _ : ℝ × E => c p.1) (p.2.1, p.2.2)) ⁻¹' U) := by
    intro U hU h0
    have hset : (fun p : Ω × ℝ × E =>
          (Set.Ioc r q ×ˢ A).indicator (fun _ : ℝ × E => c p.1) (p.2.1, p.2.2)) ⁻¹' U
        = (c ⁻¹' U) ×ˢ (Set.Ioc r q ×ˢ A) := by
      ext ⟨ω, s, e⟩
      simp only [Set.mem_preimage, Set.mem_prod]
      by_cases hm : (s, e) ∈ Set.Ioc r q ×ˢ A
      · rw [Set.indicator_of_mem hm]
        simp only [Set.mem_prod] at hm
        tauto
      · rw [Set.indicator_of_notMem hm]
        simp only [Set.mem_prod] at hm
        constructor
        · intro h; exact absurd h h0
        · intro h; exact absurd ⟨h.2.1, h.2.2⟩ hm
    rw [hset]
    exact MeasurableSpace.measurableSet_generateFrom ⟨r, q, c ⁻¹' U, A, hr, hc hU, hA, hAν, rfl⟩
  intro U hU
  by_cases h0 : (0 : F) ∈ U
  · have hc := key Uᶜ hU.compl (fun h => h h0)
    have := hc.compl
    simpa [Set.preimage_compl] using this
  · exact key U hU h0

end Deterministic

end LevyStochCalc.Probability
