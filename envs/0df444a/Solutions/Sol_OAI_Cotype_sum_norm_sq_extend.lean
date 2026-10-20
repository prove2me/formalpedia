-- Prove2me | solution 1 for OAI.Cotype.sum_norm_sq_extend
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:53:55.692618+00:00
-- url     : https://prove2.me/submissions/d8ba3f64-3e7f-4a1a-9a03-0daaf7dfd65f

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
omit [NormedSpace ℝ X] in
theorem t_ext {n m : ℕ} (j : Fin n ↪ Fin m) (x : Fin n → X) :
    (∑ u, ‖Function.extend j x (fun _ => 0) u‖^2) = ∑ i, ‖x i‖^2 := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map j))]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [j.injective.extend_apply]
  · intro k _ hk
    have : ¬ ∃ i, j i = k := by
      rintro ⟨i, rfl⟩; exact hk (Finset.mem_map_of_mem _ (Finset.mem_univ i))
    rw [Function.extend_apply' _ _ _ this]
    simp

omit [NormedSpace ℝ X] in
theorem solution {n m : ℕ} (j : Fin n ↪ Fin m) (x : Fin n → X) :
    (∑ u, ‖Function.extend j x (fun _ => 0) u‖^2) = ∑ i, ‖x i‖^2 := by
  exact t_ext j x

