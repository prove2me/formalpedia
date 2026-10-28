-- Prove2me | solution 1 for MeanRiskBellman.Recursion.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:04:46.37281+00:00
-- url     : https://prove2.me/submissions/3599fa91-a199-4c2a-b2d4-47ae1d1d9348

import Mathlib
import Definitions.Def_MeanRiskBellman_Recursion_Model

open MeasureTheory Filter Topology
open scoped Pointwise

open MeanRiskBellman.Recursion in
theorem solution {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] (M : Market Ω)
    (hM : M.Assumptions) (t : ℕ) (ht : t + 1 < M.T) (v : Ω → ℝ)
    (hv : StronglyMeasurable[M.ℱ t] v) (ψ : ℕ → Ω → Fin M.d → ℝ) :
    ψ ∈ feasible M t v ↔
      value M t (ψ t) = v ∧ ψ t ∈ M.Φ t ∧ ψ ∈ feasible M (t + 1) (value M (t + 1) (ψ t)) := by
  constructor
  · rintro ⟨hA, hB, hC⟩
    have h1 := hC (t + 1) le_rfl (by omega)
    simp only [Nat.add_sub_cancel] at h1
    exact ⟨hA, hB, h1.1.symm, h1.2, fun s hs1 hs2 => hC s (by omega) hs2⟩
  · rintro ⟨hA, hB, h1, h2, h3⟩
    refine ⟨hA, hB, fun s hs1 hs2 => ?_⟩
    rcases Nat.eq_or_lt_of_le hs1 with rfl | hlt
    · simp only [Nat.add_sub_cancel]
      exact ⟨h1.symm, h2⟩
    · exact h3 s (by omega) hs2
