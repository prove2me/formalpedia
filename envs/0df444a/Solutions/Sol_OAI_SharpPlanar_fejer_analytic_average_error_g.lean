-- Prove2me | solution 1 for OAI.SharpPlanar.fejer_analytic_average_error_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:26:03.044494+00:00
-- url     : https://prove2.me/submissions/a2f9e6b4-9b88-4f7e-9b44-0a47feafd492

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_analytic_taylor_error_g
import Theorems.Thm_OAI_SharpPlanar_fejerWeight_pos_g
import Theorems.Thm_OAI_SharpPlanar_fejer_exact_complex_g
import Theorems.Thm_OAI_SharpPlanar_fejer_exact_g
import Theorems.Thm_OAI_SharpPlanar_positive_quadrature_error_g
import Theorems.Thm_OAI_SharpPlanar_taylorPolynomial_zero_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

namespace SharpPlanar

lemma fejer_mass : ∑ v ∈ Finset.range 256, fejerWeight v = 1 := by
  have h := fejer_exact_g 1 (by norm_num)
  norm_num at h ⊢
  exact h

lemma fejerNode_mem (v : ℕ) : fejerNode v ∈ Set.Icc (-1:ℝ) 1 :=
  ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar
open MeasureTheory Set

lemma fejer_analytic_average_error_g_oai (f : ℂ → ℂ)
    (hf : DiffContOnCl ℂ f (Metric.ball 0 2))
    (hbound : ∀ z ∈ Metric.sphere 0 2, ‖f z‖ ≤ (10:ℝ)^53) :
    ‖(1/2:ℂ)*(∫ x in (-1:ℝ)..1, f x) -
      ∑ v : Fin 256, (fejerWeight v.val:ℂ)*f (fejerNode v.val)‖ < 1/10^22 := by
  let p : ℝ → ℂ := fun x => taylorPolynomial f 0 256 x
  let ε : ℝ := (10:ℝ)^53*(1/2:ℝ)^256/(1-(1/2:ℝ))
  have hb (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
      ‖f x-p x‖ ≤ ε := by
    apply analytic_taylor_error_g (by norm_num : (0:ℝ)<2) (by positivity)
      (by norm_num : (0:ℝ)≤1/2) (by norm_num) hf hbound _ 256
    simp only [sub_zero,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  have hp : Continuous p := by
    unfold p
    simp only [taylorPolynomial_zero_g]
    fun_prop
  have hc : ContinuousOn (fun x : ℝ => f x) (Icc (-1:ℝ) 1) := by
    apply hf.continuousOn.comp (Complex.continuous_ofReal.continuousOn)
    intro x hx
    apply subset_closure
    rw [Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
    have := abs_le.mpr hx
    linarith
  have hw (v : Fin 256) : 0 ≤ 2*fejerWeight v.val := by
    have := fejerWeight_pos_g v.val
    positivity
  have hmass : (∑ v : Fin 256, 2*fejerWeight v.val) = (1:ℝ)-(-1) := by
    rw [← Finset.mul_sum,Fin.sum_univ_eq_sum_range,fejer_mass]
    norm_num
  have hexact : (∫ x in (-1:ℝ)..1, p x) =
      ∑ v : Fin 256, ((2*fejerWeight v.val:ℝ):ℂ)*p (fejerNode v.val) := by
    have hh : (∑ v ∈ Finset.range 256, (fejerWeight v:ℂ)*p (fejerNode v)) =
        (1/2:ℂ)*(∫ x in (-1:ℝ)..1, p x) := by
      simpa only [p,taylorPolynomial,sub_zero] using
        fejer_exact_complex_g (fun k => (k.factorial:ℂ)⁻¹*iteratedDeriv k f 0)
    rw [Fin.sum_univ_eq_sum_range (fun v : ℕ => ((2*fejerWeight v:ℝ):ℂ)*p (fejerNode v)) 256]
    simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,mul_assoc,← Finset.mul_sum]
    rw [hh]
    ring
  have he := positive_quadrature_error_g (-1) 1 (by norm_num)
    (fun v : Fin 256 => 2*fejerWeight v.val) (fun v : Fin 256 => fejerNode v.val)
    (fun x : ℝ => f x) p ε hw (fun v => fejerNode_mem v.val) hmass hc hp.continuousOn hb hexact
  have heq : (1/2:ℂ)*((∫ x in (-1:ℝ)..1, f x)-
      ∑ v : Fin 256, ((2*fejerWeight v.val:ℝ):ℂ)*f (fejerNode v.val)) =
      (1/2:ℂ)*(∫ x in (-1:ℝ)..1, f x)-
        ∑ v : Fin 256, (fejerWeight v.val:ℂ)*f (fejerNode v.val) := by
    simp only [mul_sub,Complex.ofReal_mul,Complex.ofReal_ofNat,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [← heq,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖ = (1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(2*(1-(-1))*ε) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ < 1/10^22 := by norm_num [ε]

end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejer_analytic_average_error_g_oai := @OAI.SharpPlanar.fejer_analytic_average_error_g_oai
