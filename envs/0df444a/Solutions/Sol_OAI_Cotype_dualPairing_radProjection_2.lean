-- Prove2me | solution 2 for OAI.Cotype.dualPairing_radProjection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:42:26.92383+00:00
-- url     : https://prove2.me/submissions/9a4c5a84-ea43-4d58-9241-a1d1071fae26

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/KConvexDuality.lean:L40-L53
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.dualPairing_radProjection. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification

-- ---- from OAI.Analysis.Cotype.KConvexDuality ----
namespace OAI

noncomputable section

open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem dualPairing_radProjection {n : ℕ} (f : Cube n → X) (g : Cube n → (X →L[ℝ] ℝ)) :
    dualPairing f (radProjection (X →L[ℝ] ℝ) g) = dualPairing (radProjection X f) g := by
  calc
    _ = ∑ i, average (fun ε => sign (ε i) * (moment (X →L[ℝ] ℝ) g i) (f ε)) := by
      simp [dualPairing, radProjection, rademacherSum, average_sum]
    _ = ∑ i, (moment (X →L[ℝ] ℝ) g i) (moment X f i) := by
      apply Finset.sum_congr rfl; intro i hi
      generalize moment (X →L[ℝ] ℝ) g i = φ
      simp [moment, average]
    _ = ∑ i, average (fun η => sign (η i) * g η (moment X f i)) := by
      apply Finset.sum_congr rfl; intro i hi
      generalize moment X f i = x
      simp [moment, average]
    _ = _ := by simp [dualPairing, radProjection, rademacherSum, average_sum]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
open WithLp


theorem solution : type_of% @_root_.OAI.Cotype.dualPairing_radProjection := @_root_.OAI.Cotype.dualPairing_radProjection
