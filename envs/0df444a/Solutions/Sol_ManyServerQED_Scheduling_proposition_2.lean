-- Prove2me | solution 1 for ManyServerQED.Scheduling.proposition_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T05:09:34.255863+00:00
-- url     : https://prove2.me/submissions/dc809e71-88fc-485b-9d72-45a14d6a49ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Theorems.Thm_ManyServerQED_Scheduling_proposition_2_existence
import Theorems.Thm_ManyServerQED_Scheduling_proposition_4_i

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

theorem solution {k : ℕ} [NeZero k] (D : DiffusionData k) (π : AdmissibleSystem k) (x : Fin k → ℝ) :
    (∃ X : ℝ≥0 → π.Ω → Fin k → ℝ, IsControlledProcess D π x X) ∧
      ∀ X Y : ℝ≥0 → π.Ω → Fin k → ℝ, IsControlledProcess D π x X → IsControlledProcess D π x Y →
        ∀ᵐ ω ∂π.P, ∀ t, X t ω = Y t ω := by
  refine ⟨proposition_2_existence D π x, ?_⟩
  intro X Y hX hY
  obtain ⟨c, hc⟩ := proposition_4_i D
  filter_upwards [hc π x x X Y hX hY] with ω hω
  intro t
  have h := hω t
  have h0 : l1norm (x - x) = 0 := by simp [l1norm]
  rw [h0, zero_mul] at h
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ |(X t ω - Y t ω) i| := fun i _ => abs_nonneg _
  have hz : l1norm (X t ω - Y t ω) = 0 :=
    le_antisymm h (Finset.sum_nonneg hnn)
  rw [l1norm, Finset.sum_eq_zero_iff_of_nonneg hnn] at hz
  funext i
  have := hz i (Finset.mem_univ _)
  rw [abs_eq_zero, Pi.sub_apply, sub_eq_zero] at this
  exact this
