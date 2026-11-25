-- Prove2me | solution 1 for GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:29:59.675808+00:00
-- url     : https://prove2.me/submissions/c8b287f8-0309-46de-8ec9-b2267dd80530

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyRevMulCharpolyRevEqOneOfTracePowAddEqZer
import Theorems.Thm_GroundTheory_Global_coe_derivative_charpolyRev


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution
    {K R : Type} [Field K] [CharZero K] [CommRing R] [Algebra K R] {p q : ℕ}
    (M : Matrix (Fin p) (Fin p) R) (N : Matrix (Fin q) (Fin q) R)
    (h : ∀ k, 1 ≤ k → (M ^ k).trace + (N ^ k).trace = 0) :
    M.charpolyRev * N.charpolyRev = 1 := by
  set f := M.charpolyRev
  set g := N.charpolyRev
  have hS : (PowerSeries.mk fun k => (M ^ (k + 1)).trace) +
      (PowerSeries.mk fun k => (N ^ (k + 1)).trace) = 0 := by
    ext k
    simp [h (k + 1) (Nat.le_add_left 1 k)]
  have hd : derivative (f * g) = 0 := by
    apply Polynomial.coe_injective
    rw [Polynomial.derivative_mul, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul,
      GroundTheory.Global.coe_derivative_charpolyRev, GroundTheory.Global.coe_derivative_charpolyRev,
      Polynomial.coe_zero]
    calc -(f : PowerSeries R) * PowerSeries.mk (fun k => (M ^ (k + 1)).trace) * (g : PowerSeries R) +
          (f : PowerSeries R) * (-(g : PowerSeries R) * PowerSeries.mk fun k => (N ^ (k + 1)).trace)
        = -((f : PowerSeries R) * (g : PowerSeries R)) *
          ((PowerSeries.mk fun k => (M ^ (k + 1)).trace) +
            (PowerSeries.mk fun k => (N ^ (k + 1)).trace)) := by ring
      _ = 0 := by rw [hS, mul_zero]
  have h0 : (f * g).coeff 0 = 1 := by
    rw [Polynomial.mul_coeff_zero, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev, Matrix.eval_charpolyRev,
      mul_one]
  ext k
  rcases k with _ | k
  · rw [h0, Polynomial.coeff_one_zero]
  · have hk := congrArg (fun r => r.coeff k) hd
    simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hk
    have hu : IsUnit ((k : R) + 1) := by
      have : ((k : R) + 1) = algebraMap K R ((k : K) + 1) := by simp
      rw [this]
      exact (IsUnit.mk0 _ (by exact_mod_cast Nat.succ_ne_zero k)).map _
    rw [Polynomial.coeff_one, if_neg (Nat.succ_ne_zero k)]
    exact hu.mul_left_eq_zero.mp hk
end GlobalTheory
