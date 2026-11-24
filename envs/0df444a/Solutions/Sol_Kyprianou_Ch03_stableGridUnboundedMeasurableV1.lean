-- Prove2me | solution 1 for Kyprianou.Ch03.stableGridUnboundedMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:59:15.104855+00:00
-- url     : https://prove2.me/submissions/13015d4c-db7f-4dea-a7ed-2d7232f928b5

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → ℝ) (hnull : ∀ m : ℕ, P (⋂ n : ℕ, {w | Y n w ≤ (m : ℝ)}) = 0) :
    ∀ᵐ w ∂P, ∀ M : ℝ, ∃ n : ℕ, M < Y n w := by
  have hgood (m : ℕ) : ∀ᵐ w ∂P, ∃ n, (m : ℝ) < Y n w := by
    rw [ae_iff]
    have he : {w | ¬ ∃ n, (m : ℝ) < Y n w} = ⋂ n : ℕ, {w | Y n w ≤ (m : ℝ)} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_iInter, not_exists, not_lt]
    rw [he]
    exact hnull m
  filter_upwards [ae_all_iff.mpr hgood] with w hw
  intro M
  obtain ⟨m, hm⟩ := exists_nat_ge M
  obtain ⟨n, hn⟩ := hw m
  exact ⟨n, hm.trans_lt hn⟩
