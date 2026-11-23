-- Prove2me | solution 1 for GlobalTheory.AppellHumbertTrivial.hermForm_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:23:05.119156+00:00
-- url     : https://prove2.me/submissions/c2a4b61a-358e-48fe-9bf5-c59abc39d1a4

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
theorem _root_.solution {B : Matrix (Fin g) (Fin g) ℂ} (hB : B.IsHermitian) (x w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w x = star (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x w) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply,
    star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hB.apply j i]
  ring
end _root_.GlobalTheory.AppellHumbertTrivial
end GlobalTheory.AppellHumbertTrivial
