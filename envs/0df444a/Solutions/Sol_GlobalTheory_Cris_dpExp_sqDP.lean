-- Prove2me | solution 1 for GlobalTheory.Cris.dpExp_sqDP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:01:32.408802+00:00
-- url     : https://prove2.me/submissions/c68a2027-871e-4be2-b596-8f6ea8f74bef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration

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
open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Cris
open CatCoh
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
namespace GlobalTheory.Cris
theorem _root_.solution (h : J ^ 2 = 0) {a : B} (ha : a ∈ J) : dpExp (divided₂ h) a = 1 + a := by
  rw [dpExp, finsum_eq_sum_of_support_subset (fun n ↦ (divided₂ h).dpow n a) (s := Finset.range 2)
    fun n hn ↦ ?_]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, (divided₂ h).dpow_zero ha,
      (divided₂ h).dpow_one ha]
  · rw [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    exact hn (squareZeroDividedPowers_dpow h (by omega) a)
end GlobalTheory.Cris
