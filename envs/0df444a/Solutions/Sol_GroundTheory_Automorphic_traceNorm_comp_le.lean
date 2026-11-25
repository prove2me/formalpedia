-- Prove2me | solution 1 for GroundTheory.Automorphic.traceNorm_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:55.399275+00:00
-- url     : https://prove2.me/submissions/492c60a9-560c-4ce8-9284-407d1eb7d5f9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Definitions.Def_GroundTheory_AutomorphicForms_TraceNormComp
import Theorems.Thm_GroundTheory_Automorphic_eq_zero_of_hsNorm_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_hsNorm_nonneg
import Theorems.Thm_GroundTheory_Automorphic_hsNorm_sq
import Theorems.Thm_GroundTheory_Automorphic_two_mul_traceNorm_comp_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace GroundTheory.Automorphic
theorem _root_.solution {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) : (traceNorm (A.comp B)).toReal ≤ hsNorm A * hsNorm B := by
  have key : ∀ t : ℝ, 0 < t → 2 * (traceNorm (A.comp B)).toReal ≤
      t ^ 2 * hsNorm A ^ 2 + (t⁻¹) ^ 2 * hsNorm B ^ 2 := by
    intro t ht
    have hAB : A.comp B = ((t : ℂ) • A).comp (((t⁻¹ : ℝ) : ℂ) • B) := by
      ext x
      simp only [comp_apply, smul_apply, map_smul, smul_smul]
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne', Complex.ofReal_one, one_smul]
    have h := two_mul_traceNorm_comp_le ((t : ℂ) • A) (((t⁻¹ : ℝ) : ℂ) • B)
    rw [← hAB, hsNormSq_smul, hsNormSq_smul] at h
    have hfin : ‖(t : ℂ)‖ₑ ^ 2 * hsNormSq A + ‖((t⁻¹ : ℝ) : ℂ)‖ₑ ^ 2 * hsNormSq B ≠ ∞ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) hA.ne, ENNReal.mul_ne_top (by simp) hB.ne⟩
    have h' := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) hA.ne)
      (ENNReal.mul_ne_top (by simp) hB.ne), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_pow, toReal_enorm, toReal_enorm, ← hsNorm_sq,
      ← hsNorm_sq, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos ht, abs_of_pos (inv_pos.2 ht)] at h'
    simpa using h'
  rcases (hsNorm_nonneg A).eq_or_lt with ha | ha
  · rw [eq_zero_of_hsNorm_eq_zero hA ha.symm, zero_comp, traceNorm_zero, ENNReal.toReal_zero]
    exact mul_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _)
  rcases (hsNorm_nonneg B).eq_or_lt with hb | hb
  · rw [eq_zero_of_hsNorm_eq_zero hB hb.symm, comp_zero, traceNorm_zero, ENNReal.toReal_zero]
    exact mul_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _)
  have h := key (Real.sqrt (hsNorm B / hsNorm A)) (Real.sqrt_pos.2 (div_pos hb ha))
  rw [inv_pow, Real.sq_sqrt (div_nonneg hb.le ha.le)] at h
  have e : hsNorm B / hsNorm A * hsNorm A ^ 2 + (hsNorm B / hsNorm A)⁻¹ * hsNorm B ^ 2 =
      2 * (hsNorm A * hsNorm B) := by
    field_simp
    ring
  linarith
end GroundTheory.Automorphic
