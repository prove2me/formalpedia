-- Prove2me | solution 1 for GlobalTheory.AppellHumbertTrivial.hermForm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:53.996504+00:00
-- url     : https://prove2.me/submissions/35a0daee-333b-4076-b7c7-4ebb31a49eaf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.AppellHumbertTrivial
variable {g : ℕ}
variable {g : ℕ}
namespace GlobalTheory.AppellHumbertTrivial
namespace _root_.GlobalTheory.AppellHumbertTrivial
theorem _root_.solution (B : Matrix (Fin g) (Fin g) ℂ) (x y w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w (x + y) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w x + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [star_add, Matrix.mulVec_add, dotProduct_add]
end _root_.GlobalTheory.AppellHumbertTrivial
end GlobalTheory.AppellHumbertTrivial
