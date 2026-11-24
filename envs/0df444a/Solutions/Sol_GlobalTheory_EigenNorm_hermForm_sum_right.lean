-- Prove2me | solution 1 for GlobalTheory.EigenNorm.hermForm_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:24:54.591158+00:00
-- url     : https://prove2.me/submissions/af2e4bbb-dbf4-4fba-91f5-8e78d67343b2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul

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
open GlobalTheory GlobalTheory.EigenNorm
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
namespace GlobalTheory.EigenNorm
theorem _root_.solution {κ : Type*} (s : Finset κ) (z : Fin g → ℂ) (w : κ → Fin g → ℂ) :
    hermForm Hm z (∑ i ∈ s, w i) = ∑ i ∈ s, hermForm Hm z (w i) := by
  simp [hermForm, star_sum, Matrix.mulVec_sum, dotProduct_sum]
end GlobalTheory.EigenNorm
