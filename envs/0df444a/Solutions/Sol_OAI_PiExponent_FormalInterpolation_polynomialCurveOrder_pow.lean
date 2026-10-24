-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_pow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T18:15:38.641261+00:00
-- url     : https://prove2.me/submissions/0d703356-7be2-42e5-83c0-6695db03b5b8

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib
import Mathlib.FieldTheory.IsAlgClosed.Basic

section

open OAI.PiExponent.FormalInterpolation

namespace PiL27

theorem logCoord {m : Nat} (c : Fin m → Complex)
    (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E]
    (x : Fin (m + 1) → E) (hfibre : x 0 = 1) (i : Fin m) :
    MvPolynomial.aeval x
      (logarithmicCoordinate c (fun _ => e 0) i.succ) =
      x i.succ - algebraMap Complex E (c i) := by
  have hL : MvPolynomial.aeval x (Polynomial.aeval (MvPolynomial.X 0 - 1 : MvPolynomial (Fin (m + 1)) ℂ)
      (OAI.PiExponent.InterpolationMatrix.truncatedLog (e 0))) = 0 := by
    rw [← Polynomial.aeval_algHom_apply]
    simp only [map_sub, MvPolynomial.aeval_X, hfibre, map_one, sub_self]
    rw [← Polynomial.coeff_zero_eq_aeval_zero', OAI.PiExponent.InterpolationMatrix.truncatedLog]
    simp [PowerSeries.coeff_trunc]
  simp only [logarithmicCoordinate, Fin.cases_succ, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  rw [hL, sub_zero]

theorem trans_ne {E : Type} [Field E] [Algebra Complex E]
    {y : E} (h : Transcendental Complex y) (a : Complex) :
    y - algebraMap Complex E a ≠ 0 := by
  intro h0
  apply h
  rw [sub_eq_zero.1 h0]
  exact isAlgebraic_algebraMap _

theorem order_pow {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (f : E) (n : Nat) :
    (polynomialCurveOrder nu (f ^ n) : Real) =
      (n : Real) * (polynomialCurveOrder nu f : Real) := by
  unfold polynomialCurveOrder
  rcases eq_or_ne (nu.1 f) ⊤ with h | h
  · have hf : f = 0 := (AddValuation.top_iff _).1 h
    subst hf
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rw [zero_pow hn.ne']; simp
  · rw [AddValuation.map_pow]
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 h
    rw [← hk, show n • ((k : ℤ) : WithTop ℤ) = ((n • k : ℤ) : WithTop ℤ) from
      (WithTop.coe_nsmul _ _).symm]
    simp only [WithTop.untop₀_coe, nsmul_eq_mul]
    push_cast; ring

end PiL27

end

open OAI OAI.PiExponent OAI.PiExponent.FormalInterpolation

open OAI.PiExponent.FormalInterpolation

theorem solution
    {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (f : E) (n : Nat) :
    (polynomialCurveOrder nu (f ^ n) : Real) =
      (n : Real) * (polynomialCurveOrder nu f : Real) := by
  apply PiL27.order_pow <;> assumption
