-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Form.div_add_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:44:50.942808+00:00
-- url     : https://prove2.me/submissions/3ddc53b5-afcd-40a7-828d-3d1590a7fc61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms
import Theorems.Thm_GlobalTheory_Ex_NumD_Form_div_add_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.NumD
namespace Form
theorem _root_.solution {N : NumD O} {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k) (x y z : N.X) :
    β.be (x + j • y) z / j = β.be x z / j + β.be y z := by
  rcases eq_or_ne j 0 with rfl | h
  · obtain rfl : k = 0 := Nat.eq_zero_of_zero_dvd hj
    have h0 : β.be y z = 0 := by simpa using β.dvd y z
    simp [h0]
  · rw [β.div_add_left hj, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul,
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.2 h)]
end Form
end GlobalTheory.Ex.NumD
