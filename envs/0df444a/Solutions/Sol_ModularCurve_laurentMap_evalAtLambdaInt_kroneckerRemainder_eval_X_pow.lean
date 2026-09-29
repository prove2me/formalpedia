-- Prove2me | solution 1 for ModularCurve.laurentMap_evalAtLambdaInt_kroneckerRemainder_eval_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7f54533e-2928-5b6d-a28d-bda8a4ae7517

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_laurentMap_evalAtLambdaInt_kroneckerRemainder_eval_X_pow

set_option autoImplicit false

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_laurentMap_evalAtLambdaInt_kroneckerRemainder_eval_X_pow.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "lambdaInt lambdaModC evalAtLambdaInt evalAtLambdaInt_X qExpand laurentMap laurentMap_qExpand laurentMap_injective LambdaModularPolynomialData"
namespace L3
p2m_open "ModularCurve"

theorem evalAtLambdaInt_eval_X_pow (R : Polynomial (Polynomial ℤ)) (q : ℕ) :
    evalAtLambdaInt (R.eval (Polynomial.X ^ q)) = R.eval₂ evalAtLambdaInt (lambdaInt ^ q) := by
  have h := Polynomial.hom_eval₂ R (RingHom.id _) evalAtLambdaInt (Polynomial.X ^ q)
  rw [RingHom.comp_id, map_pow, evalAtLambdaInt_X] at h
  exact h

theorem eval_int_eq_zero (q : ℕ) [NeZero q] (data : LambdaModularPolynomialData q) :
    data.Ψ.eval₂ evalAtLambdaInt (qExpand ℤ q lambdaInt) = 0 := by
  apply laurentMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
  rw [map_zero, Polynomial.hom_eval₂, laurentMap_qExpand]
  exact data.eval_eq_zero

theorem main (q : ℕ) [Fact q.Prime] (data : LambdaModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
            + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    (S : LaurentSeries ℤ) (hS : qExpand ℤ q lambdaInt - lambdaInt ^ q = (q : LaurentSeries ℤ) * S)
    (k : Type*) [Field k] [CharP k q] :
    laurentMap (Int.castRingHom k) (evalAtLambdaInt (R.eval (Polynomial.X ^ q))) =
      - laurentMap (Int.castRingHom k) S * (lambdaModC k ^ (q ^ 2) - lambdaModC k) := by
  have hqprime : q.Prime := Fact.out
  set J : LaurentSeries ℤ := lambdaInt with hJdef
  set Jq : LaurentSeries ℤ := qExpand ℤ q lambdaInt with hJqdef
  set qL : LaurentSeries ℤ := (q : LaurentSeries ℤ) with hqLdef
  have hqL0 : qL ≠ 0 := by
    rw [hqLdef, ← map_natCast (HahnSeries.C (Γ := ℤ) (R := ℤ)) q]
    intro h
    exact (Int.natCast_ne_zero.mpr hqprime.ne_zero) (HahnSeries.C_injective (h.trans HahnSeries.C_zero.symm))
  have hJq : Jq = J ^ q + qL * S := by
    rw [hJqdef]; linear_combination hS
  have h0 := eval_int_eq_zero q data
  rw [hR] at h0
  simp only [eval₂_add, eval₂_mul, eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, evalAtLambdaInt_X] at h0
  have hCq : evalAtLambdaInt (Polynomial.C (q : ℤ)) = qL := by
    rw [evalAtLambdaInt, Polynomial.coe_eval₂RingHom, eval₂_C, eq_intCast, Int.cast_natCast]
  rw [hCq] at h0
  change (J ^ q - Jq) * (J - Jq ^ q) + qL * R.eval₂ evalAtLambdaInt Jq = 0 at h0
  have hT : qL ^ 2 ∣ Jq ^ q - (J ^ q) ^ q := by
    have h1 : (q : LaurentSeries ℤ) ∣ Jq - J ^ q := ⟨S, by rw [hJq]; ring⟩
    simpa using dvd_sub_pow_of_dvd_sub h1 1
  obtain ⟨T, hT⟩ := hT
  have hU : qL ∣ R.eval₂ evalAtLambdaInt Jq - R.eval₂ evalAtLambdaInt (J ^ q) := by
    rw [eval₂_eq_eval_map, eval₂_eq_eval_map]
    exact (Dvd.intro S (by rw [hJq]; ring)).trans (Polynomial.sub_dvd_eval_sub Jq (J ^ q) _)
  obtain ⟨U, hU⟩ := hU
  have hkey : R.eval₂ evalAtLambdaInt (J ^ q) = S * (J - J ^ (q ^ 2)) - qL * (qL * S * T + U) := by
    apply mul_left_cancel₀ hqL0
    have e1 : Jq ^ q = (J ^ q) ^ q + qL ^ 2 * T := by linear_combination hT
    have e2 : R.eval₂ evalAtLambdaInt Jq = R.eval₂ evalAtLambdaInt (J ^ q) + qL * U := by linear_combination hU
    rw [e1, e2, hJq, ← pow_mul, ← sq] at h0
    linear_combination h0
  have hφq : laurentMap (Int.castRingHom k) qL = 0 := by
    rw [hqLdef, map_natCast, ← map_natCast (HahnSeries.C (Γ := ℤ) (R := k)) q, CharP.cast_eq_zero k q,
      map_zero]
  rw [evalAtLambdaInt_eval_X_pow, ← hJdef, hkey, lambdaModC, ← hJdef]
  simp only [map_sub, map_mul, map_pow, hφq, zero_mul, sub_zero]
  ring

end ModularCurve.L3

theorem solution (q : ℕ) [Fact q.Prime] (data : LambdaModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    (S : LaurentSeries ℤ) (hS : qExpand ℤ q lambdaInt - lambdaInt ^ q = (q : LaurentSeries ℤ) * S)
    (k : Type*) [Field k] [CharP k q] :
    laurentMap (Int.castRingHom k) (evalAtLambdaInt (R.eval (Polynomial.X ^ q))) =
      - laurentMap (Int.castRingHom k) S * (lambdaModC k ^ (q ^ 2) - lambdaModC k) :=
  ModularCurve.L3.main q data R hR S hS k

end S_ModularCurve_laurentMap_evalAtLambdaInt_kroneckerRemainder_eval_X_pow
end P2MW
export P2MW.S_ModularCurve_laurentMap_evalAtLambdaInt_kroneckerRemainder_eval_X_pow (solution)
