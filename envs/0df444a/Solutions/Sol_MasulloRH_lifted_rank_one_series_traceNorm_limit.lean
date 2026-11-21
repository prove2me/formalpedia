-- Prove2me | solution 1 for MasulloRH.lifted_rank_one_series_traceNorm_limit
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:22:22.606316+00:00
-- url     : https://prove2.me/submissions/dd985958-08aa-4eac-86a9-48f83fe90109

import Theorems.Thm_MasulloGRH_traceNorm_tail_of_summable_rank_mul_opNorm

open MasulloGRH Filter InnerProductSpace
open scoped Topology

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (v η : ℕ → H)
    (hs : Summable fun i => ‖A (v i)‖ * ‖η i‖) :
    let R := fun i => rankOne ℂ (A (v i)) (η i)
    ∃ T : H →L[ℂ] H, HasSum R T ∧ IsNuclearOperator T ∧
      Tendsto (fun s : Finset ℕ => traceNorm (T - ∑ i ∈ s, R i)) atTop (𝓝 0) := by
  classical
  let R := fun i => rankOne ℂ (A (v i)) (η i)
  have hnorm : Summable fun i => ‖R i‖ := by simpa only [R, norm_rankOne] using hs
  let T := ∑' i, R i
  have hT : HasSum R T := hnorm.of_norm.hasSum
  have hpoint (u : H) : HasSum (fun i => R i u) (T u) := by
    have hu := (ContinuousLinearMap.apply ℂ H u).hasSum hT
    exact hu
  refine ⟨T, hT, ⟨η, fun i => A (v i), by simpa only [mul_comm] using hs, fun u => hpoint u⟩, ?_⟩
  let S := fun i => Submodule.span ℂ ({A (v i)} : Set H)
  letI (i : ℕ) : FiniteDimensional ℂ (S i) := FiniteDimensional.span_singleton ℂ _
  have hrange (i : ℕ) (u : H) : R i u ∈ S i :=
    (S i).smul_mem _ (Submodule.subset_span (Set.mem_singleton _))
  have hdim (i : ℕ) : Module.finrank ℂ (S i) ≤ 1 := by
    simpa [S] using (finrank_span_le_card (R := ℂ) ({A (v i)} : Set H))
  have hc : Summable fun i => (Module.finrank ℂ (S i) : ℝ) * ‖R i‖ := by
    apply hnorm.of_nonneg_of_le (fun i => by positivity)
    intro i
    exact mul_le_of_le_one_left (norm_nonneg _) (by exact_mod_cast hdim i)
  exact (traceNorm_tail_of_summable_rank_mul_opNorm R S hrange hc T hpoint).2
