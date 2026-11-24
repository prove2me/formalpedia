-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.integral_pow_mul_cexp_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:02:55.331798+00:00
-- url     : https://prove2.me/submissions/1b70a10c-dfbe-458b-8c65-ce50ac4da8e3

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierLipschitzOneVariableKernelEq
import Theorems.Thm_GlobalTheory_LipschitzTR_integrableOn_pow_mul_cexp_neg
import Theorems.Thm_GlobalTheory_LipschitzTR_tendsto_pow_mul_cexp_neg
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR
open Set Filter Topology
namespace GlobalTheory.LipschitzTR
theorem _root_.solution (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * Complex.exp (-(r * t)) = (n.factorial : ℂ) / r ^ (n + 1) := by
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  induction n with
  | zero =>
    have h := integral_exp_mul_complex_Ioi (a := -r) (by simpa using hr) 0
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    simp_rw [← neg_mul]
    rw [h]; simp [hr0]
  | succ n ih =>
    have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := fun t => (hasDerivAt_id t).ofReal_comp
    have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => Complex.exp (-(r * t)) / (-r))
        (Complex.exp (-(r * t))) t := by
      intro t _
      have h2 : HasDerivAt (fun t : ℝ => -(r * (t : ℂ))) (-r) t := by
        simpa using ((h1 t).const_mul (-r))
      have hv' := h2.cexp.div_const (-r)
      rwa [mul_div_assoc, div_self (neg_ne_zero.mpr hr0), mul_one] at hv'
    have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (t : ℂ) ^ (n + 1))
        (((n : ℂ) + 1) * (t : ℂ) ^ n) t := by
      intro t _
      convert (hasDerivAt_pow (n + 1) (t : ℂ)).comp_ofReal using 1
      simp
    have hint := integrableOn_pow_mul_cexp_neg n hr
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0) hu hv
      (integrableOn_pow_mul_cexp_neg (n + 1) hr)
      (by
        refine IntegrableOn.congr_fun (hint.const_mul (-((n : ℂ) + 1) / r)) (fun t _ => ?_) measurableSet_Ioi
        simp only [Pi.mul_apply]; field_simp)
      (by
        have hc : Continuous (fun t : ℝ => (t : ℂ) ^ (n + 1) * (Complex.exp (-(r * t)) / (-r))) := by
          fun_prop
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        convert this using 2 <;> simp)
      (by
        have := (tendsto_pow_mul_cexp_neg (n + 1) hr).const_mul (-1 / r)
        rw [mul_zero] at this
        refine this.congr (fun t => ?_)
        simp only [Pi.mul_apply]; field_simp)
    rw [hibp]
    have e : (fun t : ℝ => ((n : ℂ) + 1) * (t : ℂ) ^ n * (Complex.exp (-(r * t)) / (-r))) =
        fun t : ℝ => (-((n : ℂ) + 1) / r) * ((t : ℂ) ^ n * Complex.exp (-(r * t))) := by
      funext t; field_simp
    rw [e, integral_const_mul, ih, Nat.factorial_succ]
    push_cast
    field_simp
    ring
end GlobalTheory.LipschitzTR
