-- Prove2me | solution 1 for ModularCurve.sub_mul_sub_mem_span_natCast_of_jqModC_mem_of_jqNModC_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/2c1b3bfb-c6a7-5143-a626-a86e02bc45d1

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ModularCurve_existsUnique_kroneckerRemainder
import Theorems.Thm_ModularCurve_exists_kroneckerCongruence_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sub_mul_sub_mem_span_natCast_of_jqModC_mem_of_jqNModC_mem
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_sub_mul_sub_mem_span_natCast_of_jqModC_mem_of_jqNModC_mem.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC evalModularPair map_evalModularPair evalModularPair_jq_eq_zero existsUnique_kroneckerRemainder exists_kroneckerCongruence_of_prime"
namespace KronSub
p2m_open "ModularCurve"

theorem jqNModC_one_mul (K : Type*) [Field K] (q : ℕ) [NeZero q] :
    jqNModC K (1 * q) = jqNModC K q := by
  simp only [one_mul]

theorem evalModularPair_eq_eval₂ {R : Type*} [CommRing R] (x y : R) (Φ : Polynomial (Polynomial ℤ)) :
    evalModularPair x y Φ = (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom R) x) y) Φ := rfl

end ModularCurve.KronSub

open ModularCurve.KronSub in
theorem solution
    (q : ℕ) [Fact q.Prime] (R : Subring (LaurentSeries (AlgebraicClosure ℚ)))
    (hj : jqModC (AlgebraicClosure ℚ) ∈ R) (hjq : jqNModC (AlgebraicClosure ℚ) (1 * q) ∈ R) :
    ((⟨jqModC (AlgebraicClosure ℚ), hj⟩ : ↥R) ^ q - ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), hjq⟩) *
        ((⟨jqModC (AlgebraicClosure ℚ), hj⟩ : ↥R) - (⟨jqNModC (AlgebraicClosure ℚ) (1 * q), hjq⟩ : ↥R) ^ q)
      ∈ Ideal.span {((q : ℕ) : ↥R)} := by

  obtain ⟨data, hK⟩ := exists_kroneckerCongruence_of_prime q
  obtain ⟨Rm, hRm, -⟩ := existsUnique_kroneckerRemainder q data hK
  set J : ↥R := ⟨jqModC (AlgebraicClosure ℚ), hj⟩ with hJ
  set Jq : ↥R := ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), hjq⟩ with hJq

  have hΦ : evalModularPair J Jq data.Φ = 0 := by
    apply Subtype.val_injective
    have h1 := map_evalModularPair R.subtype J Jq data.Φ
    rw [show (R.subtype J : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) from rfl,
      show (R.subtype Jq : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) (1 * q) from rfl,
      jqNModC_one_mul, evalModularPair_jq_eq_zero (AlgebraicClosure ℚ) data] at h1
    exact h1

  rw [hRm, evalModularPair_eq_eval₂, map_add, map_mul, map_mul, map_sub, map_sub, map_pow, map_pow] at hΦ
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_natCast,
    eq_intCast, Int.cast_natCast, map_natCast] at hΦ

  rw [add_eq_zero_iff_eq_neg] at hΦ
  rw [hΦ]
  exact neg_mem_iff.mpr (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

end S_ModularCurve_sub_mul_sub_mem_span_natCast_of_jqModC_mem_of_jqNModC_mem
end P2MW
export P2MW.S_ModularCurve_sub_mul_sub_mem_span_natCast_of_jqModC_mem_of_jqNModC_mem (solution)
