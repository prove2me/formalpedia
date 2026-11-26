-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41IndependentLevelSectionNullV23
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:07:23.085058+00:00
-- url     : https://prove2.me/submissions/9e97e9df-b2ef-498e-b1f6-79686161c6e2

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (X : ℝ × Ω → ℝ) (hX : Measurable X)
    (hOcc : ∀ᵐ w ∂P, ∀ b : ℝ, volume {s : ℝ | 0 ≤ s ∧ X (s,w) = b} = 0) :
    ∀ᵐ s ∂(volume : Measure ℝ), ∀ᵐ p ∂P.prod μ,
      ¬ (0 ≤ s ∧ X (s,p.1) + p.2 = 0) := by
  let B : Set ((Ω × ℝ) × ℝ) := {p | 0 ≤ p.2 ∧ X (p.2,p.1.1) + p.1.2 = 0}
  have hB : MeasurableSet B := by
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_eq_fun ((hX.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))).add
        (measurable_snd.comp measurable_fst)) measurable_const)
  have hM : MeasurableSet {p : Ω × ℝ | ∀ᵐ s ∂(volume : Measure ℝ), (p,s) ∉ B} := by
    simp_rw [ae_iff,not_not]
    change MeasurableSet {p : Ω × ℝ | volume ((fun s => (p,s)) ⁻¹' B) = 0}
    exact measurableSet_eq_fun (measurable_measure_prodMk_left hB) measurable_const
  have hAE : ∀ᵐ p ∂P.prod μ, ∀ᵐ s ∂(volume : Measure ℝ), (p,s) ∉ B := by
    apply (Measure.ae_prod_iff_ae_ae hM).2
    filter_upwards [hOcc] with w hw
    apply Eventually.of_forall
    intro y
    rw [ae_iff]
    apply measure_mono_null _ (hw (-y))
    intro s hs
    have h : 0 ≤ s ∧ X (s,w) + y = 0 := by simpa [B] using hs
    exact ⟨h.1,by linarith [h.2]⟩
  exact (Measure.ae_ae_comm hB.compl).mp hAE
