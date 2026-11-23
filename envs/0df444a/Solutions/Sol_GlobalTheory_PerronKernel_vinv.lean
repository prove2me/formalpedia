-- Prove2me | solution 1 for GlobalTheory.PerronKernel.vinv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:05:58.228219+00:00
-- url     : https://prove2.me/submissions/6307669c-8b78-4764-ab66-436687c90282

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Theorems.Thm_GlobalTheory_PerronKernel_ne_zero_of_im
import Theorems.Thm_GlobalTheory_PerronKernel_cont_vinv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
namespace GlobalTheory.PerronKernel
private lemma hasDerivAt_half_log_sub_I_mul_arctan_eq_inv {s : ℝ} (hs : s ≠ 0) (x : ℝ) :
    HasDerivAt (fun x : ℝ => ((Real.log (x ^ 2 + s ^ 2) / 2 : ℝ) : ℂ) - I * (Real.arctan (x / s) : ℂ))
      ((x : ℂ) + s * I)⁻¹ x := by
  have hpos : 0 < x ^ 2 + s ^ 2 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 + s ^ 2) / 2) (x / (x ^ 2 + s ^ 2)) x :=
    ((((hasDerivAt_pow 2 x).add_const (s ^ 2)).log hpos.ne').div_const 2).congr_deriv
      (by field_simp; ring)
  have h2a : HasDerivAt (fun y : ℝ => y / s) (1 / s) x := (hasDerivAt_id' x).div_const s
  have h2b := (Real.hasDerivAt_arctan (x / s)).comp x h2a
  have h2 : HasDerivAt (fun x : ℝ => Real.arctan (x / s)) (s / (x ^ 2 + s ^ 2)) x :=
    h2b.congr_deriv (by field_simp; ring)
  refine (h1.ofReal_comp.sub (h2.ofReal_comp.const_mul I)).congr_deriv ?_
  have hz : (x : ℂ) + s * I ≠ 0 := ne_zero_of_im hs
  have hc : (x : ℂ) ^ 2 + (s : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hpos.ne'
  symm
  apply inv_eq_of_mul_eq_one_right
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring
end GlobalTheory.PerronKernel
end

set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronKernel
namespace GlobalTheory.PerronKernel
theorem _root_.solution {σ : ℝ} (h : σ ≠ 0) (T : ℝ) :
    ∫ t in (-T)..T, ((σ : ℂ) + t * I)⁻¹ = ((2 * Real.arctan (T / σ) : ℝ) : ℂ) := by
  have hs : -σ ≠ 0 := neg_ne_zero.mpr h
  have hd : ∀ t ∈ Set.uIcc (-T) T, HasDerivAt
      (fun t : ℝ => -I * (((Real.log (t ^ 2 + (-σ) ^ 2) / 2 : ℝ) : ℂ) -
        I * (Real.arctan (t / -σ) : ℂ))) ((σ : ℂ) + t * I)⁻¹ t := by
    intro t _
    refine ((hasDerivAt_half_log_sub_I_mul_arctan_eq_inv hs t).const_mul (-I)).congr_deriv ?_
    rw [show (t : ℂ) + ((-σ : ℝ) : ℂ) * I = -I * ((σ : ℂ) + t * I) by
      push_cast; ring_nf; rw [I_sq]; ring]
    rw [mul_inv, ← mul_assoc]
    rw [show -I * (-I)⁻¹ = 1 from mul_inv_cancel₀ (neg_ne_zero.mpr I_ne_zero), one_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((cont_vinv h).intervalIntegrable _ _)]
  simp only [neg_sq, neg_div, div_neg, neg_neg, Real.arctan_neg]
  push_cast
  ring_nf
  rw [I_sq]
  ring
end GlobalTheory.PerronKernel
