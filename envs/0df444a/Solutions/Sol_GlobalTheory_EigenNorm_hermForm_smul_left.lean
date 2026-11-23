-- Prove2me | solution 1 for GlobalTheory.EigenNorm.hermForm_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:56.538187+00:00
-- url     : https://prove2.me/submissions/3848165c-b6e4-4fb5-8f7f-e46ba88503a4

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
namespace GlobalTheory.EigenNorm
namespace _root_.GlobalTheory.EigenNorm
theorem _root_.solution (r : ℂ) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (r • z) w = r * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, smul_eq_mul]
end _root_.GlobalTheory.EigenNorm
end GlobalTheory.EigenNorm
