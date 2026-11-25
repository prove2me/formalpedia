-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.pairing_nsmul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:35.365752+00:00
-- url     : https://prove2.me/submissions/71f1df89-f465-4e55-b241-9c6b8c5d5014

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateDeterminant
import Theorems.Thm_GroundTheory_Arith_Abelian_pairing_zero_right
import Theorems.Thm_GroundTheory_Arith_Abelian_nsmul_nsmul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open PadicInt
variable {A : Type*} [AddCommGroup A] {L : Type*} [Field L] (N : ℕ) (e : A → A → L)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution
    (hr : ∀ P Q R, N • P = 0 → N • Q = 0 → N • R = 0 → e P (Q + R) = e P Q * e P R)
    (hpow : ∀ P Q, N • P = 0 → N • Q = 0 → e P Q ^ N = 1) (hN : N ≠ 0)
    {P R : A} (hP : N • P = 0) (hR : N • R = 0) (a : ℕ) : e P (a • R) = e P R ^ a := by
  induction a with
  | zero => rw [zero_nsmul, pow_zero, pairing_zero_right N e hr hpow hN hP]
  | succ a ih =>
    rw [succ_nsmul, hr _ _ _ hP (nsmul_nsmul_eq_zero N hR a) hR, ih, pow_succ]
end GroundTheory.Arith.Abelian
