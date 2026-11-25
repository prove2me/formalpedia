-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.pairing_nsmul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:50:26.15427+00:00
-- url     : https://prove2.me/submissions/3a9f0390-3545-4106-ab6d-b5cb5ffe9387

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateDeterminant
import Theorems.Thm_GroundTheory_Arith_Abelian_pairing_zero_left
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
    (hl : ∀ P Q R, N • P = 0 → N • Q = 0 → N • R = 0 → e (P + Q) R = e P R * e Q R)
    (hpow : ∀ P Q, N • P = 0 → N • Q = 0 → e P Q ^ N = 1) (hN : N ≠ 0)
    {P R : A} (hP : N • P = 0) (hR : N • R = 0) (a : ℕ) : e (a • P) R = e P R ^ a := by
  induction a with
  | zero => rw [zero_nsmul, pow_zero, pairing_zero_left N e hl hpow hN hR]
  | succ a ih =>
    rw [succ_nsmul, hl _ _ _ (nsmul_nsmul_eq_zero N hP a) hP hR, ih, pow_succ]
end GroundTheory.Arith.Abelian
