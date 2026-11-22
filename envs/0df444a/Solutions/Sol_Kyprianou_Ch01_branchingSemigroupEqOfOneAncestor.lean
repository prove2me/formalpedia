-- Prove2me | solution 1 for Kyprianou.Ch01.branchingSemigroupEqOfOneAncestor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:37:21.24417+00:00
-- url     : https://prove2.me/submissions/2394ab02-6c38-4a72-97c2-771f0c8d8b31

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingZeroAbsorbing
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- One-ancestor equality determines every finite initial population using
the branching convolution identity and zero-population absorption. -/
theorem solution
    (K₁ K₂ : PopulationLaws)
    (hBranch₁ : HasBranchingProperty K₁)
    (hBranch₂ : HasBranchingProperty K₂)
    (hOne : ∀ t : ℝ≥0, K₁ 1 t = K₂ 1 t) :
    K₁ = K₂ := by
  funext y
  induction y with
  | zero =>
      funext t
      exact (Kyprianou.Ch01.branchingZeroAbsorbing K₁ hBranch₁ t).trans
        (Kyprianou.Ch01.branchingZeroAbsorbing K₂ hBranch₂ t).symm
  | succ y ih =>
      funext t
      change K₁ (y + 1) t = K₂ (y + 1) t
      calc
        K₁ (y + 1) t =
            (K₁ y t).bind (fun n => (K₁ 1 t).map (fun m => n + m)) :=
          hBranch₁ y 1 t
        _ = (K₂ y t).bind (fun n => (K₂ 1 t).map (fun m => n + m)) := by
          rw [congrFun ih t, hOne t]
        _ = K₂ (y + 1) t := (hBranch₂ y 1 t).symm
