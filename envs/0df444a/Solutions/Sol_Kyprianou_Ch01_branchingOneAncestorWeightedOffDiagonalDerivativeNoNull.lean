-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOneAncestorWeightedOffDiagonalDerivativeNoNull
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T11:31:25.191131+00:00
-- url     : https://prove2.me/submissions/d31415ab-39bf-4c02-b144-335c841cf467

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorWeightedQuotientTendstoNoNull
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
set_option autoImplicit false

/-- Source-exact weighted time-zero off-diagonal derivative from Scheffe limit. -/
theorem solution
    (law : PopulationLaws) (rate : NNReal) (offspring : PMF ℕ)
    (hNoNullJumps : offspring 1 = 0)
    (hinit : law 1 0 = PMF.pure 1)
    (hRates : IsBranchingRateGenerator law rate offspring)
    (q : ℝ) (hq : 0 < q) :
    HasDerivWithinAt
      (fun t : ℝ => ∑' k : ℕ,
        if k = 1 then (0 : ℝ)
        else ((law 1 (Real.toNNReal t)) k).toReal *
          Real.exp (-q * (k : ℝ)))
      ((rate : ℝ) * ∑' k : ℕ,
        (offspring k).toReal * Real.exp (-q * (k : ℝ)))
      (Set.Ici 0) 0 := by
  have hw := Kyprianou.Ch01.branchingOneAncestorWeightedQuotientTendstoNoNull
    law rate offspring hNoNullJumps hinit hRates q hq
  have hzero :
      (∑' k : ℕ, if k = 1 then (0 : ℝ)
        else ((law 1 (0 : NNReal)) k).toReal *
          Real.exp (-q * (k : ℝ))) = 0 := by
    rw [hinit]
    have heq :
        (fun k : ℕ => if k = 1 then (0 : ℝ)
          else (PMF.pure 1 k).toReal *
            Real.exp (-q * (k : ℝ))) =
        (fun _ : ℕ => (0 : ℝ)) := by
      funext k
      by_cases hk : k = 1
      · simp [hk]
      · simp [hk, PMF.pure_apply_of_ne 1 k hk]
    rw [heq]
    simp
  have hslope (t : ℝ) :
      (∑' k : ℕ,
        ((if k = 1 then (0 : ℝ)
          else ((law 1 (Real.toNNReal t)) k).toReal) / t) *
          Real.exp (-q * (k : ℝ))) =
      slope (fun s : ℝ =>
        ∑' k : ℕ, if k = 1 then (0 : ℝ)
          else ((law 1 (Real.toNNReal s)) k).toReal *
            Real.exp (-q * (k : ℝ))) 0 t := by
    calc
      (∑' k : ℕ,
        ((if k = 1 then (0 : ℝ)
          else ((law 1 (Real.toNNReal t)) k).toReal) / t) *
          Real.exp (-q * (k : ℝ))) =
        (∑' k : ℕ, if k = 1 then (0 : ℝ)
          else ((law 1 (Real.toNNReal t)) k).toReal *
            Real.exp (-q * (k : ℝ))) / t := by
          rw [← tsum_div_const]
          apply tsum_congr
          intro k
          by_cases hk : k = 1
          · simp [hk]
          · simp [hk, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      _ = slope (fun s : ℝ =>
          ∑' k : ℕ, if k = 1 then (0 : ℝ)
            else ((law 1 (Real.toNNReal s)) k).toReal *
              Real.exp (-q * (k : ℝ))) 0 t := by
        have h0 :
            (∑' k : ℕ, if k = 1 then (0 : ℝ)
              else ((law 1 (Real.toNNReal (0 : ℝ))) k).toReal *
                Real.exp (-q * (k : ℝ))) = 0 := by
          simpa using hzero
        rw [slope_def_field]
        rw [h0]
        simp
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext t
    simp only [Set.mem_diff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨hge, hne⟩
      exact lt_of_le_of_ne hge (fun heq => hne heq.symm)
    · intro ht
      exact ⟨ht.le, ne_of_gt ht⟩
  rw [hset]
  simpa only [hslope] using hw
