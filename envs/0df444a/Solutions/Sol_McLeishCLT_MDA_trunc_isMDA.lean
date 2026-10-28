-- Prove2me | solution 1 for McLeishCLT.MDA.trunc_isMDA
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:35:16.194681+00:00
-- url     : https://prove2.me/submissions/303174b8-9aa1-4566-8f21-91aac9c93153

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open McLeishCLT.MDA in
theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : ℕ → Filtration ℕ m0) (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (hmda : IsMDA P ℱ k X) :
    IsMDA P ℱ k (trunc X) := by
  intro n j hj
  obtain ⟨hXm, hXi, hXc⟩ := hmda n j hj
  set g : Ω → ℝ := fun ω => if ∑ i ∈ Finset.range j, X n i ω ^ 2 ≤ 2 then 1 else 0 with hg
  have hs : Measurable[ℱ n j] (fun ω => ∑ i ∈ Finset.range j, X n i ω ^ 2) := by
    apply Finset.measurable_sum
    intro i hi
    have hi' : i < j := Finset.mem_range.mp hi
    have hm := (hmda n i (lt_trans hi' hj)).1
    have hm' : StronglyMeasurable[ℱ n j] (X n i) := hm.mono ((ℱ n).mono (by omega))
    exact hm'.measurable.pow_const 2
  have hgm : Measurable[ℱ n j] g := by
    apply Measurable.ite _ measurable_const measurable_const
    exact measurableSet_le hs measurable_const
  have hgs : StronglyMeasurable[ℱ n j] g := hgm.stronglyMeasurable
  have htr : trunc X n j = X n j * g := rfl
  have hint : Integrable (trunc X n j) P := by
    apply hXi.mono
    · rw [htr]
      exact (hXm.mono ((ℱ n).le (j + 1))).aestronglyMeasurable.mul
        (hgs.mono ((ℱ n).le j)).aestronglyMeasurable
    · filter_upwards with ω
      rw [htr, Pi.mul_apply, norm_mul]
      have : ‖g ω‖ ≤ 1 := by
        simp only [hg]
        split_ifs <;> simp
      calc ‖X n j ω‖ * ‖g ω‖ ≤ ‖X n j ω‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = ‖X n j ω‖ := mul_one _
  refine ⟨?_, hint, ?_⟩
  · rw [htr]
    exact hXm.mul (hgs.mono ((ℱ n).mono (by omega)))
  · have hce := condExp_mul_of_aestronglyMeasurable_right (m := ℱ n j) (μ := P)
      hgs.aestronglyMeasurable (by rw [← htr]; exact hint) hXi
    rw [htr]
    filter_upwards [hce, hXc] with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
    simp
