-- Prove2me | solution 1 for GlobalTheory.ConjugateMembership.eq_iff_conj_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:18:01.37454+00:00
-- url     : https://prove2.me/submissions/672d769b-7b7c-43b7-aa3b-2367c977aab2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Theorems.Thm_GlobalTheory_ConjugateMembership_conj_eq_neg_of_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConjugateMembership
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ConjugateMembership
theorem _root_.solution {x r : ℂ} {d : ℝ} (hd : 0 < d) (hx : x ^ 2 = -(d : ℂ)) (hr : r ^ 2 = -(d : ℂ)) :
    x = r ↔ ¬ (starRingEnd ℂ) x = r := by
  rw [conj_eq_neg_of_sq hd hx]
  constructor
  · rintro rfl h
    have h0 : x = 0 := by linear_combination (-1 / 2 : ℂ) * h
    rw [h0] at hx
    have : (d : ℂ) = 0 := by linear_combination hx
    exact hd.ne' (by exact_mod_cast this)
  · intro h
    have : (x - r) * (-x - r) = 0 := by linear_combination hr - hx
    rcases mul_eq_zero.1 this with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd (sub_eq_zero.1 h1) h
end GlobalTheory.ConjugateMembership
