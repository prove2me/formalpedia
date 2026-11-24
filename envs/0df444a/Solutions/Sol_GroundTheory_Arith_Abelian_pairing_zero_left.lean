-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.pairing_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:06.457852+00:00
-- url     : https://prove2.me/submissions/98f1e4b1-62df-4cda-8e2d-f47635708b53

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateDeterminant
import Theorems.Thm_GroundTheory_Arith_Abelian_pairing_ne_zero

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
    {R : A} (hR : N • R = 0) : e 0 R = 1 := by
  have h := hl 0 0 R (nsmul_zero N) (nsmul_zero N) hR
  rw [add_zero] at h
  have hne := pairing_ne_zero N e hpow hN (nsmul_zero N) hR
  exact mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm)
end GroundTheory.Arith.Abelian
