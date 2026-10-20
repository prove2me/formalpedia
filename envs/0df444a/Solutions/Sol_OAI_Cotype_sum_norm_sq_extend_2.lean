-- Prove2me | solution 2 for OAI.Cotype.sum_norm_sq_extend
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:21:25.834764+00:00
-- url     : https://prove2.me/submissions/5963d870-47e2-4284-b0e4-1e4a3eb29f00

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/IndependentSigns.lean:L45-L58
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.sum_norm_sq_extend. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.Cotype.IndependentSigns ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
theorem sum_norm_sq_extend {n m : ℕ} (j : Fin n ↪ Fin m) (x : Fin n → X) :
    (∑ u, ‖Function.extend j x (fun _ => 0) u‖^2) = ∑ i, ‖x i‖^2 := by
  classical
  let y : Fin m → X := Function.extend j x (fun _ => 0)
  have hy i : y (j i) = x i := j.injective.extend_apply _ _ _
  have hz u (hu : u ∉ Finset.univ.image j) : y u = 0 := by
    apply Function.extend_apply'
    simpa using hu
  change (∑ u, ‖y u‖^2) = ∑ i, ‖x i‖^2
  calc
    _ = ∑ u ∈ Finset.univ.image j, ‖y u‖^2 :=
      (Finset.sum_subset (Finset.subset_univ _) (fun u _ hu => by rw [hz u hu,norm_zero,zero_pow (by norm_num)])).symm
    _ = _ := by rw [Finset.sum_image (fun _ _ _ _ he => j.injective he)]; simp only [hy]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.sum_norm_sq_extend := @_root_.OAI.Cotype.sum_norm_sq_extend
