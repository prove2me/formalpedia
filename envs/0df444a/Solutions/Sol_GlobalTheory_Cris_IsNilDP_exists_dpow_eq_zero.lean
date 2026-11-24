-- Prove2me | solution 1 for GlobalTheory.Cris.IsNilDP.exists_dpow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:01:28.171202+00:00
-- url     : https://prove2.me/submissions/e5f3fb01-7cc0-4cd8-8d63-39ff9cb60743

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
namespace IsNilDP
theorem _root_.solution {δ : DividedPowers J} (h : IsNilDP δ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ a, δ.dpow n a = 0 := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn a ↦ ?_⟩
  by_cases ha : a ∈ J
  · simpa using hN [(n, a)] (by simpa using ha) (by simpa using hn)
  · exact δ.dpow_null ha
end IsNilDP
end GlobalTheory.Cris
