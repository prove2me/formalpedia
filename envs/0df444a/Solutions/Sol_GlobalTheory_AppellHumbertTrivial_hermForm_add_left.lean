-- Prove2me | solution 1 for GlobalTheory.AppellHumbertTrivial.hermForm_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:01.424113+00:00
-- url     : https://prove2.me/submissions/a7f1461f-3706-494f-b6e2-f1893148b971

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
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B (x + y) w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x w + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B y w := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [add_dotProduct]
end _root_.GlobalTheory.AppellHumbertTrivial
end GlobalTheory.AppellHumbertTrivial
