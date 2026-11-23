-- Prove2me | solution 1 for GlobalTheory.EigenNorm.hermForm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:56.369156+00:00
-- url     : https://prove2.me/submissions/a58df197-fb83-4549-bffc-64e2b190cf63

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
theorem _root_.solution (z w w' : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z (w + w') = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w' := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_add, Matrix.mulVec_add, dotProduct_add]
end _root_.GlobalTheory.EigenNorm
end GlobalTheory.EigenNorm
