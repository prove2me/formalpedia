-- Prove2me | solution 1 for GlobalTheory.PullHermitian.hermForm_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:05.575626+00:00
-- url     : https://prove2.me/submissions/41221998-1527-4318-ac12-4b7b90dd4447

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.PullHermitian
namespace GlobalTheory.PullHermitian
theorem _root_.solution {g g' : ℕ} (H : Matrix (Fin g') (Fin g') ℂ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (z w : Fin g → ℂ) :
    hermForm ((LinearMap.toMatrix' F).transpose * H * (LinearMap.toMatrix' F).transpose.conjTranspose) z w =
      hermForm H (F z) (F w) := by
  rw [← LinearMap.toMatrix'_mulVec F z, ← LinearMap.toMatrix'_mulVec F w]
  generalize LinearMap.toMatrix' F = P
  unfold hermForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z,
    Matrix.vecMul_transpose, Matrix.mulVec_conjTranspose, star_star, Matrix.vecMul_transpose]
end GlobalTheory.PullHermitian
