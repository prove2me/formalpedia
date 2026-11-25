-- Prove2me | solution 1 for GlobalTheory.LevelDict.ext_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:32.590836+00:00
-- url     : https://prove2.me/submissions/ff8fd86f-74d1-46bb-9d82-50ed6c760dfd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_UnimodularAndTangentOfIsAH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesTangentVectors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LineBundlePowSectionsEqThetaLevel
import Theorems.Thm_GlobalTheory_ThetaTangent_dense_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.LevelDict
namespace GlobalTheory.LevelDict
theorem _root_.solution {g : ℕ} {θ f f' : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0) (hf : Continuous f)
    (hf' : Continuous f') (h : ∀ z, θ z ≠ 0 → f z = f' z) : ∀ z, f z = f' z :=
  congrFun (Continuous.ext_on (ThetaTangent.dense_ne_zero hθ h0) hf hf' h)
end GlobalTheory.LevelDict
