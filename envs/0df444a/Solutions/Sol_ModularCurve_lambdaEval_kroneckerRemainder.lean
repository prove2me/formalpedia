-- Prove2me | solution 1 for ModularCurve.lambdaEval_kroneckerRemainder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/dca4f01d-d584-559d-b6a7-43124f10969f

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_lambdaEval_kroneckerRemainder

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_lambdaEval_kroneckerRemainder.ModularCurve ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_lambdaEval_kroneckerRemainder.ModularCurve.LambdaNodeLocalized MvPolynomial"

namespace ModularCurve
p2m_export "ModularCurve" "lambdaModC lambdaNModC evalAtLambdaInt evalAtLambdaInt_X laurentMap laurentMap_qExpand laurentMap_laurentMap LambdaModularPolynomialData"
p2m_open "ModularCurve"
namespace LambdaNodeLocalized
p2m_export "ModularCurve.LambdaNodeLocalized" "lambdaEval"
p2m_open "ModularCurve.LambdaNodeLocalized"
namespace AlphaL

variable {q : ℕ} [Fact q.Prime] {L : Type*} [Field L] [Algebra ℚ L] (A : Subring L)

def transport : Polynomial (Polynomial ℤ) →+* MvPolynomial (Fin 2) A :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom _)) (MvPolynomial.X 0))
    (MvPolynomial.X 1)

theorem transport_apply (F : Polynomial (Polynomial ℤ)) :
    transport A F = Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom _)) (MvPolynomial.X 0))
      (MvPolynomial.X 1) F := rfl

theorem lambdaEval_transport (F : Polynomial (Polynomial ℤ)) :
    lambdaEval q A (transport A F)
      = F.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) (lambdaModC L)) (lambdaNModC L q) := by
  set mE := lambdaEval q A with hmE
  set θ : Polynomial ℤ →+* LaurentSeries L := Polynomial.eval₂RingHom (Int.castRingHom _) (lambdaModC L) with hθ
  have hgen0 : mE (MvPolynomial.X 0) = lambdaModC L := by
    rw [hmE, lambdaEval, MvPolynomial.eval₂Hom_X']; rfl
  have hgen1 : mE (MvPolynomial.X 1) = lambdaNModC L q := by
    rw [hmE, lambdaEval, MvPolynomial.eval₂Hom_X']; rfl
  rw [transport_apply, Polynomial.hom_eval₂, hgen1]
  congr 1
  apply Polynomial.ringHom_ext
  · intro n
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, hθ,
      map_intCast, eq_intCast]
  · rw [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hθ,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hgen0]

theorem eval₂_Ψ_eq_zero (data : LambdaModularPolynomialData q) :
    data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) (lambdaModC L)) (lambdaNModC L q) = 0 := by
  set θ : Polynomial ℤ →+* LaurentSeries L := Polynomial.eval₂RingHom (Int.castRingHom _) (lambdaModC L) with hθ
  set E : LaurentSeries ℚ →+* LaurentSeries L := laurentMap (algebraMap ℚ L) with hE
  have hZ : (algebraMap ℚ L).comp (Int.castRingHom ℚ) = Int.castRingHom L := RingHom.ext_int _ _
  have hE1 : E (lambdaNModC ℚ q) = lambdaNModC L q := by
    rw [hE, lambdaNModC, laurentMap_qExpand, lambdaNModC, lambdaModC, lambdaModC, laurentMap_laurentMap, hZ]
  have hEθ : E.comp ((laurentMap (Int.castRingHom ℚ)).comp evalAtLambdaInt) = θ := by
    apply Polynomial.ringHom_ext
    · intro n
      simp only [RingHom.coe_comp, Function.comp_apply, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        map_intCast, eq_intCast, evalAtLambdaInt]
    · rw [RingHom.coe_comp, Function.comp_apply, RingHom.coe_comp, Function.comp_apply, evalAtLambdaInt_X, hE,
        laurentMap_laurentMap, hZ, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, lambdaModC]
  have h := congrArg E data.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂, hEθ, hE1] at h
  exact h

end AlphaL
end LambdaNodeLocalized
end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_lambdaEval_kroneckerRemainder.ModularCurve _root_.ModularCurve.LambdaNodeLocalized _root_.P2MW.S_ModularCurve_lambdaEval_kroneckerRemainder.ModularCurve.LambdaNodeLocalized ModularCurve.LambdaNodeLocalized.AlphaL in
theorem solution
    {q : ℕ} [Fact q.Prime] (data : LambdaModularPolynomialData q) (R : Polynomial (Polynomial ℤ))
    (hR : data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
      + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    {L : Type*} [Field L] [Algebra ℚ L] (A : Subring L) :
    lambdaEval q A
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom A)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) A)
      = (algebraMap L (LaurentSeries L) (q : L))⁻¹
        * ((lambdaNModC L q - lambdaModC L ^ q) * (lambdaModC L - lambdaNModC L q ^ q)) := by
  have hΨ := eval₂_Ψ_eq_zero (L := L) data
  rw [hR, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_sub,
    Polynomial.eval₂_pow, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X] at hΨ
  have hθX : (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) (lambdaModC L)) Polynomial.X = lambdaModC L :=
    Polynomial.eval₂_X _ _
  have hθq : (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) (lambdaModC L)) (Polynomial.C (q : ℤ))
      = (q : LaurentSeries L) := by
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, eq_intCast, Int.cast_natCast]
  rw [hθX, hθq] at hΨ
  rw [← transport_apply, lambdaEval_transport, map_natCast]
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have hq0 : (q : LaurentSeries L) ≠ 0 := by
    rw [← map_natCast (algebraMap L (LaurentSeries L)) q]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)

  have key : (q : LaurentSeries L) *
      R.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) (lambdaModC L)) (lambdaNModC L q)
      = (lambdaNModC L q - lambdaModC L ^ q) * (lambdaModC L - lambdaNModC L q ^ q) := by
    linear_combination hΨ
  rw [← key, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul]

end

end S_ModularCurve_lambdaEval_kroneckerRemainder
end P2MW
export P2MW.S_ModularCurve_lambdaEval_kroneckerRemainder (solution)
