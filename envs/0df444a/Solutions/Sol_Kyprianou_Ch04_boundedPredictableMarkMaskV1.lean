-- Prove2me | solution 1 for Kyprianou.Ch04.boundedPredictableMarkMaskV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:31:23.428478+00:00
-- url     : https://prove2.me/submissions/5db85fff-c4f0-4a08-8865-bb2e6e76aa28

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Mark-masked predictable weights with bounded marks are measurable,
bounded and supported on the chosen finite mark band. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance)
    (B : Set ℝ) (hB : MeasurableSet B) (hmark : ∀ z ∈ B, |z| ≤ 1)
    (W : NNReal × Ω → ℝ) (hW : Measurable[F.predictable] W)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ p, |W p| ≤ K) :
    let g := fun p : (NNReal × Ω) × ℝ =>
      B.indicator (fun z => z * W p.1) p.2
    Measurable[F.predictable.prod inferInstance] g ∧
      (∀ p, ‖g p‖ ≤ K) ∧ (∀ p, p.2 ∉ B → g p = 0) := by
  letI : MeasurableSpace (NNReal × Ω) := F.predictable
  let g := fun p : (NNReal × Ω) × ℝ => B.indicator (fun z => z * W p.1) p.2
  have he : g = (univ ×ˢ B).indicator (fun p => p.2 * W p.1) := by
    funext p
    by_cases hp : p.2 ∈ B
    · simp [g,indicator_of_mem hp,indicator_of_mem (show p ∈ univ ×ˢ B from ⟨mem_univ _,hp⟩)]
    · simp [g,indicator_of_notMem hp,indicator_of_notMem (show p ∉ univ ×ˢ B from fun h => hp h.2)]
  change Measurable g ∧ (∀ p, ‖g p‖ ≤ K) ∧ (∀ p, p.2 ∉ B → g p = 0)
  refine ⟨?_,?_,?_⟩
  · rw [he]
    exact (measurable_snd.mul (hW.comp measurable_fst)).indicator (MeasurableSet.univ.prod hB)
  · intro p
    by_cases hp : p.2 ∈ B
    · rw [show g p = p.2 * W p.1 from indicator_of_mem hp _, Real.norm_eq_abs,abs_mul]
      exact (mul_le_mul_of_nonneg_right (hmark _ hp) (abs_nonneg _)).trans (by simpa using hb p.1)
    · simpa [g,indicator_of_notMem hp] using hK
  · intro p hp
    exact indicator_of_notMem hp _
