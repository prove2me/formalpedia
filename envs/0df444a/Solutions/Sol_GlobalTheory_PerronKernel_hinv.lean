-- Prove2me | solution 1 for GlobalTheory.PerronKernel.hinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:34.562798+00:00
-- url     : https://prove2.me/submissions/65a5ee95-7f1d-41da-9be1-52a0ebec8c22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Theorems.Thm_GlobalTheory_PerronKernel_ne_zero_of_im
import Theorems.Thm_GlobalTheory_PerronKernel_cont_hinv
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
theorem _root_.solution {T : ℝ} (h : T ≠ 0) (a b : ℝ) :
    (∫ x in a..b, ((x : ℂ) + ((-T : ℝ) : ℂ) * I)⁻¹) - ∫ x in a..b, ((x : ℂ) + T * I)⁻¹
      = 2 * I * ((Real.arctan (b / T) - Real.arctan (a / T) : ℝ) : ℂ) := by
  have hs : -T ≠ 0 := neg_ne_zero.mpr h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_half_log_sub_I_mul_arctan_eq_inv hs x)
      ((cont_hinv hs).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_half_log_sub_I_mul_arctan_eq_inv h x)
      ((cont_hinv h).intervalIntegrable _ _)]
  simp only [neg_sq, div_neg, Real.arctan_neg]
  push_cast
  ring
end GlobalTheory.PerronKernel
