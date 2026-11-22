-- Prove2me | solution 1 for MasulloRepair.nuclear_monotone_projection_traceNorm_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T21:47:10.161152+00:00
-- url     : https://prove2.me/submissions/2bb7ae52-6708-458b-b8e1-328297ce582b

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Theorems.Thm_MasulloRepair_nuclear_finite_sieve_traceNorm_tendsto

set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Topology MasulloGRH
open scoped BigOperators

private theorem solution_projection_telescope
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (U : ℕ → Submodule ℂ H)
    [hU : ∀ n, (U n).HasOrthogonalProjection] (n : ℕ) :
    (∑ i ∈ Finset.range n,
        ((U i).starProjection - (U (i + 1)).starProjection) ∘L A) =
      ((U 0).starProjection - (U n).starProjection) ∘L A := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ext x
      simp [ContinuousLinearMap.comp_apply]

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : IsNuclearOperator A)
    (U : ℕ → Submodule ℂ H)
    [hU : ∀ n, (U n).HasOrthogonalProjection]
    [hUcl : (⨆ n, U n).topologicalClosure.HasOrthogonalProjection]
    (hmono : Monotone U) :
    (∀ n, IsNuclearOperator
      (((U 0).starProjection - (U n).starProjection) ∘L A)) ∧
    IsNuclearOperator
      (((U 0).starProjection - (⨆ n, U n).topologicalClosure.starProjection) ∘L A) ∧
    Tendsto
      (fun n => traceNorm
        ((∑ i ∈ Finset.range n,
            ((U i).starProjection - (U (i + 1)).starProjection) ∘L A) -
          ((U 0).starProjection - (⨆ n, U n).topologicalClosure.starProjection) ∘L A))
      atTop (𝓝 0) ∧
    Tendsto
      (fun n => operatorTrace
        (∑ i ∈ Finset.range n,
          ((U i).starProjection - (U (i + 1)).starProjection) ∘L A)) atTop
      (𝓝 (operatorTrace
        (((U 0).starProjection - (⨆ n, U n).topologicalClosure.starProjection) ∘L A))) := by
  let P : ℕ → H →L[ℂ] H := fun n => (U n).starProjection
  let Pinf : H →L[ℂ] H := (⨆ n, U n).topologicalClosure.starProjection
  have hbd : ∀ᶠ n in atTop, ‖P n‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall (fun n => Submodule.starProjection_norm_le (U n))
  have hP : ∀ u : H, Tendsto (fun n => P n u) atTop (𝓝 (Pinf u)) := by
    intro u
    exact Submodule.starProjection_tendsto_closure_iSup U hmono u
  have hmain := MasulloRepair.nuclear_finite_sieve_traceNorm_tendsto
    (A := A) hA (P := P) (Pinf := Pinf) (C := (1 : ℝ)) hbd hP
  simpa [P, Pinf] using hmain
