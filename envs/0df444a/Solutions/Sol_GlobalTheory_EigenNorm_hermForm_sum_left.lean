-- Prove2me | solution 1 for GlobalTheory.EigenNorm.hermForm_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:24:53.037848+00:00
-- url     : https://prove2.me/submissions/87b03062-6fe6-4651-bc35-ee788428adfe

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
theorem _root_.solution {κ : Type*} (s : Finset κ) (z : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i ∈ s, z i) w = ∑ i ∈ s, hermForm Hm (z i) w := by
  simp [hermForm, sum_dotProduct]
end GlobalTheory.EigenNorm
