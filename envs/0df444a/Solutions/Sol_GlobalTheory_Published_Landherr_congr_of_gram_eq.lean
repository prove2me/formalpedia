-- Prove2me | solution 1 for GlobalTheory.Published.Landherr.congr_of_gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:39:57.659113+00:00
-- url     : https://prove2.me/submissions/842f5f8b-aa49-4504-b966-7d65f83441db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Theorems.Thm_GlobalTheory_Published_gram_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.Landherr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.Published.Landherr
theorem _root_.solution (τ : E →+* ℂ) {Q Q' : Matrix (Fin r) (Fin r) ℂ} (hQ : Q.det ≠ 0)
    (hQ' : Q'.det ≠ 0) (h : gram τ G Q = gram τ G' Q') :
    ∃ R : Matrix (Fin r) (Fin r) ℂ, R.det ≠ 0 ∧ G'.map τ = Rᵀ * G.map τ * R.map conj := by
  rw [gram_eq, gram_eq] at h
  have hu : IsUnit Q'.det := isUnit_iff_ne_zero.mpr hQ'
  refine ⟨Q * Q'⁻¹, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact mul_ne_zero hQ (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero
  · have e1 : Q'⁻¹ᵀ * Q'ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]
    have e2 : Q'.map conj * Q'⁻¹.map conj = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
    calc G'.map τ = (Q'⁻¹ᵀ * Q'ᵀ) * G'.map τ * (Q'.map conj * Q'⁻¹.map conj) := by
          rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = Q'⁻¹ᵀ * (Q'ᵀ * G'.map τ * Q'.map conj) * Q'⁻¹.map conj := by
          simp only [Matrix.mul_assoc]
      _ = (Q * Q'⁻¹)ᵀ * G.map τ * (Q * Q'⁻¹).map conj := by
          rw [← h, Matrix.transpose_mul, Matrix.map_mul]
          simp only [Matrix.mul_assoc]
end GlobalTheory.Published.Landherr
