-- Prove2me | solution 1 for ModularCurve.exists_isIntegral_adjoin_inv_jq_mul_inv_atkinLehnerInvolutionFull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c4507905-6392-5c76-90c1-920fbf156f0a

import Mathlib
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_exists_reversed_eval2_inv_jq_inv_jqN_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isIntegral_adjoin_inv_jq_mul_inv_atkinLehnerInvolutionFull
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one"

set_option autoImplicit false

open ModularCurve Polynomial

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (R : Type*) [CommRing R] [Algebra R ℚ] [Algebra R (modularFunctionFieldFull (N * p))]
    [IsScalarTower R ℚ (modularFunctionFieldFull (N * p))] :
    ∃ a ∈ Algebra.adjoin R
        ({(⟨jq, modularFunctionField_le_full (N * p) (jq_mem (N * p))⟩ :
          modularFunctionFieldFull (N * p))⁻¹} : Set (modularFunctionFieldFull (N * p))),
      IsIntegral
        (Algebra.adjoin R
          ({(⟨jq, modularFunctionField_le_full (N * p) (jq_mem (N * p))⟩ :
            modularFunctionFieldFull (N * p))⁻¹} : Set (modularFunctionFieldFull (N * p))))
        ((1 + (⟨jq, modularFunctionField_le_full (N * p) (jq_mem (N * p))⟩ :
            modularFunctionFieldFull (N * p))⁻¹ * a) *
          (atkinLehnerInvolutionFull N p
            ⟨jq, modularFunctionField_le_full (N * p) (jq_mem (N * p))⟩)⁻¹) := by
  classical
  have hσ : IsAtkinLehnerAutFull N p (atkinLehnerInvolutionFull N p) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N p
      (ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N p Fact.out hpN)
  set J : modularFunctionFieldFull (N * p) :=
    ⟨jq, modularFunctionField_le_full (N * p) (jq_mem (N * p))⟩ with hJ
  set Jp : modularFunctionFieldFull (N * p) :=
    ⟨qExpand ℚ p jq, jqd_mem_full (N * p) (dvd_mul_left p N)⟩ with hJp
  have hwJ : atkinLehnerInvolutionFull N p J = Jp := by
    obtain ⟨h1, -⟩ := hσ 1 inferInstance (one_dvd N)
    have e1 : J = ⟨qExpand ℚ 1 jq, jqd_mem_full (N * p) (Dvd.dvd.mul_right (one_dvd N) p)⟩ :=
      Subtype.ext (qExpand_one_apply jq).symm
    have e2 : Jp =
        ⟨qExpand ℚ (1 * p) jq, jqd_mem_full (N * p) (Nat.mul_dvd_mul_right (one_dvd N) p)⟩ :=
      Subtype.ext (qExpand_congr (one_mul p).symm jq)
    rw [e1, e2]; exact h1
  rw [hwJ]
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p
  obtain ⟨Ψ, -, hdegΨ, hlead, -, -, hroot⟩ :=
    ModularCurve.ModularPolynomialData.exists_reversed_eval2_inv_jq_inv_jqN_eq_zero p data

  let A := Algebra.adjoin R ({J⁻¹} : Set (modularFunctionFieldFull (N * p)))
  let uA : A := ⟨J⁻¹, Algebra.self_mem_adjoin_singleton R _⟩
  let θ : Polynomial ℤ →+* A := Polynomial.eval₂RingHom (Int.castRingHom A) uA

  obtain ⟨a₀, ha₀⟩ : (X : Polynomial ℤ) ∣ Ψ.coeff (p + 1) - 1 := by
    rw [X_dvd_iff, coeff_sub, hlead, coeff_one_zero, sub_self]
  have hc : Ψ.coeff (p + 1) = 1 + X * a₀ := by rw [← ha₀]; ring
  refine ⟨θ a₀, (θ a₀).2, ?_⟩

  have hrootF : aeval Jp⁻¹ (Ψ.map θ) = 0 := by
    rw [aeval_def, eval₂_map]
    apply (algebraMap (modularFunctionFieldFull (N * p)) (LaurentSeries ℚ)).injective
    rw [map_zero, hom_eval₂]
    have hhom : (algebraMap (modularFunctionFieldFull (N * p)) (LaurentSeries ℚ)).comp
        ((algebraMap A (modularFunctionFieldFull (N * p))).comp θ)
          = (aeval (R := ℤ) jq⁻¹).toRingHom := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      rw [RingHom.comp_apply, RingHom.comp_apply]
      show ((((Polynomial.eval₂RingHom (Int.castRingHom A) uA) X : A) :
        modularFunctionFieldFull (N * p)) : LaurentSeries ℚ) = aeval jq⁻¹ (X : Polynomial ℤ)
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, aeval_X]
      rfl
    rw [hhom]
    have hJp : (algebraMap (modularFunctionFieldFull (N * p)) (LaurentSeries ℚ)) Jp⁻¹
        = (jqN p)⁻¹ := by
      rw [map_inv₀]; rfl
    rw [hJp]
    exact hroot

  have hint := isIntegral_leadingCoeff_smul (R := A) (Ψ.map θ) (x := Jp⁻¹) hrootF
  have hθc : ((θ (Ψ.coeff (p + 1)) : A) : modularFunctionFieldFull (N * p))
      = 1 + J⁻¹ * (θ a₀ : modularFunctionFieldFull (N * p)) := by
    rw [hc, θ.map_add, θ.map_one, θ.map_mul]
    show (1 : modularFunctionFieldFull (N * p)) + ((θ X : A) : modularFunctionFieldFull (N * p)) *
      (θ a₀ : modularFunctionFieldFull (N * p)) = _
    congr 2
    show ((Polynomial.eval₂RingHom (Int.castRingHom A) uA X : A) :
      modularFunctionFieldFull (N * p)) = J⁻¹
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  by_cases hzero : θ (Ψ.coeff (p + 1)) = 0
  · have h0 : (1 + J⁻¹ * (θ a₀ : modularFunctionFieldFull (N * p))) = 0 := by
      rw [← hθc, hzero]; rfl
    rw [h0, zero_mul]
    exact isIntegral_zero
  · have hlc : (Ψ.map θ).leadingCoeff = θ (Ψ.coeff (p + 1)) := by
      rw [leadingCoeff_map_of_leadingCoeff_ne_zero θ (by rwa [leadingCoeff, hdegΨ]), leadingCoeff,
        hdegΨ]
    rw [hlc, Algebra.smul_def] at hint
    rw [← hθc]
    exact hint

end S_ModularCurve_exists_isIntegral_adjoin_inv_jq_mul_inv_atkinLehnerInvolutionFull
end P2MW
export P2MW.S_ModularCurve_exists_isIntegral_adjoin_inv_jq_mul_inv_atkinLehnerInvolutionFull (solution)
