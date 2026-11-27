-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.card_torsion_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:42:32.988542+00:00
-- url     : https://prove2.me/submissions/df7c821b-d5fe-450e-9897-c40058b67ee3

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
import Theorems.Thm_GroundTheory_Arith_Abelian_card_zsmul_eq_zero_le
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian_card_roots__Sq_le_of_odd_33bd30ed21d5
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian_card_roots__Sq_le_of_two_39a1c37b6e0f
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian__Sq_ne_zero_of_ne_zero_fd3fba5d47fb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [E.IsElliptic]
  (p : ℕ) [hp : Fact p.Prime] [CharP F p]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution : Nat.card {P : E.toAffine.Point // (p : ℤ) • P = 0} < p ^ 2 := by
  have hne : E.ΨSq p ≠ 0 := ΨSq_ne_zero_of_ne_zero E (by exact_mod_cast hp.out.ne_zero)
  refine (card_zsmul_eq_zero_le E hne).trans_lt ?_
  by_cases h2 : p = 2
  · have := card_roots_ΨSq_le_of_two E p h2
    subst h2
    omega
  · have := card_roots_ΨSq_le_of_odd E p h2
    have hp3 : 3 ≤ p := by
      have := hp.out.two_le
      omega
    have hodd : p ^ 2 % 2 = 1 := by
      have : Odd p := hp.out.odd_of_ne_two h2
      have : Odd (p ^ 2) := this.pow
      exact Nat.odd_iff.mp this
    have h9 : 9 ≤ p ^ 2 := by nlinarith
    omega
end GroundTheory.Arith.Abelian
