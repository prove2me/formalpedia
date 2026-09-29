-- Prove2me | solution 1 for ModularCurve.modularEval_kroneckerRemainder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1e8d4ba1-3eeb-57f3-b932-12f02d207804

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularEval_kroneckerRemainder
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

open Polynomial in
theorem solution
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (data : ModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) + Polynomial.C (Polynomial.C (q : ℤ)) * R) :
    NodeLocalized.modularEval (1 * q) A.toSubring
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
        (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)
      = ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (q : AlgebraicClosure ℚ))⁻¹
        * ((((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ :
        modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) - ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ :
        modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ^ q) * (((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ :
        modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) - ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ :
        modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ^ q))) := by

  set Qb := AlgebraicClosure ℚ
  set E : LaurentSeries ℚ →+* LaurentSeries Qb := coeffEmb Qb with hE
  set gJ : LaurentSeries Qb := coeffEmb Qb jq with hgJ
  set gJq : LaurentSeries Qb := coeffEmb Qb (qExpand ℚ (1 * q) jq) with hgJq
  set mE := NodeLocalized.modularEval (1 * q) A.toSubring with hmE
  set θ : Polynomial ℤ →+* LaurentSeries Qb := Polynomial.eval₂RingHom (Int.castRingHom _) gJ with hθ
  change mE (R.eval₂ (eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0)) (MvPolynomial.X 1))
    = (algebraMap Qb (LaurentSeries Qb) (q : Qb))⁻¹ * ((gJq - gJ ^ q) * (gJ - gJq ^ q))

  have hgen0 : mE (MvPolynomial.X 0) = gJ := by
    rw [hmE, NodeLocalized.modularEval, MvPolynomial.eval₂Hom_X', hgJ]
    show jqModC Qb = coeffMap (algebraMap ℚ Qb) (jqModC ℚ)
    exact (map_jqModC _).symm
  have hgen1 : mE (MvPolynomial.X 1) = gJq := by
    rw [hmE, NodeLocalized.modularEval, MvPolynomial.eval₂Hom_X', hgJq]
    show jqNModC Qb (1 * q) = coeffEmb Qb (qExpand ℚ (1 * q) jq)
    rw [jqNModC]
    have h1 : jqModC Qb = coeffEmb Qb jq := by
      show jqModC Qb = coeffMap (algebraMap ℚ Qb) (jqModC ℚ); exact (map_jqModC _).symm
    rw [h1]
    ext m
    unfold coeffEmb
    by_cases hm : ((1 * q : ℕ) : ℤ) ∣ m
    · obtain ⟨m', rfl⟩ := hm
      rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
    · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ hm, qExpand_coeff_of_not_dvd _ _ hm, map_zero]
  have hLHS : mE (R.eval₂ (eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
      (MvPolynomial.X 1)) = R.eval₂ θ gJq := by
    rw [Polynomial.hom_eval₂, hgen1]
    congr 1
    apply Polynomial.ringHom_ext
    · intro n
      simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, hθ,
        map_intCast, eq_intCast]
    · rw [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hθ,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hgen0]

  have hq1 : E (jqN q) = gJq := by
    rw [hgJq, hE, jqN]
    congr 1
    simp only [one_mul]
  have hEJ : E.comp evalAtJ = θ := by
    apply Polynomial.ringHom_ext
    · intro n; simp only [RingHom.coe_comp, Function.comp_apply, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        map_intCast, eq_intCast]
    · rw [RingHom.coe_comp, Function.comp_apply, evalAtJ_X, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hgJ, hE]
  have hΦ : data.Φ.eval₂ θ gJq = 0 := by
    have h := congrArg E data.eval_eq_zero
    rw [map_zero, Polynomial.hom_eval₂, hEJ, hq1] at h
    exact h

  rw [hR] at hΦ
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.eval₂_X, hθ, Polynomial.coe_eval₂RingHom] at hΦ

  rw [hLHS]
  have hq0 : algebraMap Qb (LaurentSeries Qb) (q : Qb) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  rw [eq_inv_mul_iff_mul_eq₀ hq0, map_natCast]
  rw [← hθ, eq_intCast, Int.cast_natCast] at hΦ
  linear_combination hΦ

end S_ModularCurve_modularEval_kroneckerRemainder
end P2MW
export P2MW.S_ModularCurve_modularEval_kroneckerRemainder (solution)
