-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.pairing_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:44:26.660946+00:00
-- url     : https://prove2.me/submissions/cbfca126-3f1c-4f2b-9da9-23223caebd19

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateDeterminant
import Theorems.Thm_GroundTheory_Arith_Abelian_nsmul_nsmul_eq_zero
import Theorems.Thm_GroundTheory_Arith_Abelian_pairing_nsmul_left
import Theorems.Thm_GroundTheory_Arith_Abelian_pairing_nsmul_right

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
    (hr : ∀ P Q R, N • P = 0 → N • Q = 0 → N • R = 0 → e P (Q + R) = e P Q * e P R)
    (hpow : ∀ P Q, N • P = 0 → N • Q = 0 → e P Q ^ N = 1)
    (hself : ∀ P, N • P = 0 → e P P = 1) (hN : N ≠ 0)
    {P Q : A} (hP : N • P = 0) (hQ : N • Q = 0) (a c b d : ℕ) :
    e (a • P + c • Q) (b • P + d • Q) * e P Q ^ (c * b) = e P Q ^ (a * d) := by
  have haP := nsmul_nsmul_eq_zero N hP a
  have hcQ := nsmul_nsmul_eq_zero N hQ c
  have hbP := nsmul_nsmul_eq_zero N hP b
  have hdQ := nsmul_nsmul_eq_zero N hQ d
  have hsum : N • (b • P + d • Q) = 0 := by rw [nsmul_add, hbP, hdQ, add_zero]
  have hPQ : N • (P + Q) = 0 := by rw [nsmul_add, hP, hQ, add_zero]
  have halt : e Q P * e P Q = 1 := by
    have h := hself (P + Q) hPQ
    rw [hl P Q _ hP hQ hPQ, hr P P Q hP hP hQ, hr Q P Q hQ hP hQ, hself P hP, hself Q hQ] at h
    rw [← h]
    ring
  rw [hl _ _ _ haP hcQ hsum, hr _ _ _ haP hbP hdQ, hr _ _ _ hcQ hbP hdQ,
    pairing_nsmul_left N e hl hpow hN hP hbP, pairing_nsmul_left N e hl hpow hN hP hdQ,
    pairing_nsmul_left N e hl hpow hN hQ hbP, pairing_nsmul_left N e hl hpow hN hQ hdQ,
    pairing_nsmul_right N e hr hpow hN hP hP, pairing_nsmul_right N e hr hpow hN hP hQ,
    pairing_nsmul_right N e hr hpow hN hQ hP, pairing_nsmul_right N e hr hpow hN hQ hQ,
    hself P hP, hself Q hQ]
  calc _ = e P Q ^ (a * d) * (e Q P * e P Q) ^ (c * b) := by ring
    _ = _ := by rw [halt, one_pow, mul_one]
end GroundTheory.Arith.Abelian
