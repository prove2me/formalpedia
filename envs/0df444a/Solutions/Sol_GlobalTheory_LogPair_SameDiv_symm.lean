-- Prove2me | solution 1 for GlobalTheory.LogPair.SameDiv.symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:00:33.050829+00:00
-- url     : https://prove2.me/submissions/a221a3a4-2d5b-4049-a68f-5f446ccc0cf1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SameDiv

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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
namespace GlobalTheory.LogPair
namespace SameDiv
theorem _root_.solution {X : Scheme.{0}} {L M : LB X} {σ : L.Sec} {τ : M.Sec} (h : SameDiv σ τ) : SameDiv τ σ :=
  fun x => by
    obtain ⟨U, i, j, hi, hj, u, hx, e⟩ := h x
    exact ⟨U, j, i, hj, hi, u⁻¹, hx, by rw [e, Units.inv_mul_cancel_left]⟩
end SameDiv
end GlobalTheory.LogPair
