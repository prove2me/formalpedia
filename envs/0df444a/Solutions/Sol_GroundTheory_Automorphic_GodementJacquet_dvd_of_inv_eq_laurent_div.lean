-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.dvd_of_inv_eq_laurent_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:27.04378+00:00
-- url     : https://prove2.me/submissions/a319620d-0899-4212-ae1c-dbedc8c2476c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLaurentIdeal
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_mem_laurentSubalgebra_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Polynomial
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution {P P' : ℂ[X]} (hP' : P'.eval 0 ≠ 0) {L : RatFunc ℂ}
    (hL : L ∈ laurentSubalgebra)
    (h : (algebraMap ℂ[X] (RatFunc ℂ) P')⁻¹ = L / algebraMap ℂ[X] (RatFunc ℂ) P) : P' ∣ P := by
  have hP'0 : P' ≠ 0 := by
    rintro rfl
    simp at hP'
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, inv_eq_zero] at h
    exact RatFunc.algebraMap_ne_zero hP'0 h
  obtain ⟨Q, k, rfl⟩ := mem_laurentSubalgebra_iff.1 hL
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hφP := RatFunc.algebraMap_ne_zero hP0
  have hφP' := RatFunc.algebraMap_ne_zero hP'0
  have heq : P * Polynomial.X ^ k = Q * P' := by
    apply RatFunc.algebraMap_injective ℂ
    rw [map_mul, map_mul, map_pow, RatFunc.algebraMap_X]
    field_simp at h
    linear_combination h
  have hXP' : ¬ Polynomial.X ∣ P' := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact hP'
  have hcop : IsCoprime P' (Polynomial.X ^ k) :=
    Irreducible.coprime_pow_of_not_dvd k Polynomial.irreducible_X hXP'
  exact hcop.dvd_of_dvd_mul_right ⟨Q, by rw [heq, mul_comm]⟩
end GroundTheory.Automorphic.GodementJacquet
