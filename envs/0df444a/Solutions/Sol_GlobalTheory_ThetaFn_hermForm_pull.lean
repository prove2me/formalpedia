-- Prove2me | solution 1 for GlobalTheory.ThetaFn.hermForm_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:31:08.159308+00:00
-- url     : https://prove2.me/submissions/369ae0ac-7e00-4f6d-bf7f-a19aef26c686

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
namespace GlobalTheory.ThetaFn
theorem _root_.solution {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (Φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (z w : Fin g → ℂ) :
    hermForm ((LinearMap.toMatrix' Φ).transpose * Hm *
      (LinearMap.toMatrix' Φ).transpose.conjTranspose) z w = hermForm Hm (Φ z) (Φ w) := by
  rw [← LinearMap.toMatrix'_mulVec Φ z, ← LinearMap.toMatrix'_mulVec Φ w]
  generalize LinearMap.toMatrix' Φ = M
  rw [hermForm, hermForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec z, Matrix.vecMul_transpose, ← Matrix.vecMul_transpose M w,
    Matrix.star_vecMul]
end GlobalTheory.ThetaFn
