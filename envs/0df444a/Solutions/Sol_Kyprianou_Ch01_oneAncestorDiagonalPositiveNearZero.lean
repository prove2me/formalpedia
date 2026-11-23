-- Prove2me | solution 1 for Kyprianou.Ch01.oneAncestorDiagonalPositiveNearZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:05:00.9138+00:00
-- url     : https://prove2.me/submissions/90cd1864-3ebc-45e2-a021-a60ea4ea2f4d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (rate : ℝ≥0) (offspring : PMF ℕ) (K : PopulationLaws)
    (hInit : K 1 0 = PMF.pure 1)
    (hGen : IsBranchingRateGenerator K rate offspring) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ≥0, (t : ℝ) < δ →
        0 < ((K 1 t) 1).toReal := by
  have hc : ContinuousWithinAt
      (fun x : ℝ => ((K 1 (Real.toNNReal x)) 1).toReal)
      (Set.Ici (0 : ℝ)) 0 :=
    (hGen 1 1).continuousWithinAt
  have hval :
      ((K 1 (Real.toNNReal (0 : ℝ))) 1).toReal = 1 := by
    simp [hInit]
  have hev : ∀ᶠ x in 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ),
      0 < ((K 1 (Real.toNNReal x)) 1).toReal := by
    apply hc.tendsto.eventually
    exact isOpen_Ioi.mem_nhds (by rw [hval]; norm_num)
  obtain ⟨S, hSnhds, hS⟩ :=
    (mem_nhdsWithin_iff_exists_mem_nhds_inter).mp hev
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hSnhds
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.property
  have htBall : (t : ℝ) ∈ Metric.ball (0 : ℝ) δ := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg ht0] using ht
  have hposReal :
      0 < ((K 1 (Real.toNNReal (t : ℝ))) 1).toReal :=
    hS ⟨hball htBall, ht0⟩
  simpa using hposReal
