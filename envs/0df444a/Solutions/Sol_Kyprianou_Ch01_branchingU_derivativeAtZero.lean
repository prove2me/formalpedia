-- Prove2me | solution 1 for Kyprianou.Ch01.branchingU_derivativeAtZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:44:59.86537+00:00
-- url     : https://prove2.me/submissions/fd57c3e1-87bf-42b0-8078-aff55ac7368c

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- The cumulant derivative is obtained from the one-particle Laplace generator. -/
theorem solution
    (law : PopulationLaws)
    (rate : ℝ) (offspring : PMF ℕ)
    (hinit : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hgenerator : ∀ q : ℝ, 0 < q →
      HasDerivWithinAt
        (fun t : ℝ =>
          branchingLaplace law 1 (Real.toNNReal t) q)
        (-(branchingMechanism rate offspring q) * Real.exp (-q))
        (Set.Ici 0) 0)
    (q : ℝ) (hq : 0 < q) :
    HasDerivWithinAt
      (fun t : ℝ => branchingU law (Real.toNNReal t) q)
      (branchingMechanism rate offspring q)
      (Set.Ici 0) 0 := by
  have hLzero : branchingLaplace law 1 0 q = Real.exp (-q) := by
    unfold branchingLaplace
    simp only [hinit 1, PMF.pure_apply]
    rw [tsum_eq_single 1]
    · simp
    · intro n hn
      simp [hn]
  let f : ℝ → ℝ := fun t => branchingLaplace law 1 (Real.toNNReal t) q
  have hf : HasDerivWithinAt f
      (-(branchingMechanism rate offspring q) * Real.exp (-q))
      (Set.Ici 0) 0 := hgenerator q hq
  have hfzero : f 0 = Real.exp (-q) := by
    simpa [f] using hLzero
  have hne : f 0 ≠ 0 := by
    rw [hfzero]
    exact ne_of_gt (Real.exp_pos _)
  have hcoef :
      (-1 : ℝ) * (-(branchingMechanism rate offspring q) * Real.exp (-q) / f 0) =
        branchingMechanism rate offspring q := by
    rw [hfzero]
    field_simp [Real.exp_ne_zero]
  have hderiv := (hf.log hne).const_mul (-1)
  rw [hcoef] at hderiv
  simpa [branchingU, f] using hderiv
