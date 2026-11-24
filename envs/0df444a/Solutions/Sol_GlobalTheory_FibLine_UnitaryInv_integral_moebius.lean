-- Prove2me | solution 1 for GlobalTheory.FibLine.UnitaryInv.integral_moebius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:51:17.832793+00:00
-- url     : https://prove2.me/submissions/e6bbcc63-7fc0-4339-bad1-9158273069b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivFractionsBilinearFormula
import Theorems.Thm_GlobalTheory_FibLine_UnitaryInv_det_smul_one
import Theorems.Thm_GlobalTheory_FibLine_UnitaryInv_ae_affine_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine GlobalTheory.FibLine.UnitaryInv
namespace GlobalTheory.FibLine.UnitaryInv
theorem _root_.solution (a b c d : ℂ) (hD : a * d - b * c ≠ 0) (G : ℂ → ℂ) :
    ∫ y : ℂ, G y = ∫ x : ℂ, (Complex.normSq ((a * d - b * c) / (a + b * x) ^ 2)) •
      G ((c + d * x) / (a + b * x)) := by
  set s : Set ℂ := {x | a + b * x ≠ 0} with hs
  have hso : IsOpen s := isOpen_ne_fun (by fun_prop) continuous_const
  have hder : ∀ x ∈ s, HasFDerivWithinAt (fun x : ℂ => (c + d * x) / (a + b * x))
      (((a * d - b * c) / (a + b * x) ^ 2) • (1 : ℂ →L[ℝ] ℂ)) s x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℂ => c + d * x) d x := by
      simpa using ((hasDerivAt_id x).const_mul d).const_add c
    have h2 : HasDerivAt (fun x : ℂ => a + b * x) b x := by
      simpa using ((hasDerivAt_id x).const_mul b).const_add a
    have h3 := h1.div h2 hx
    have h4 : HasDerivAt (fun x : ℂ => (c + d * x) / (a + b * x)) ((a * d - b * c) / (a + b * x) ^ 2) x := by
      have e : (a * d - b * c) / (a + b * x) ^ 2
          = (d * (a + b * x) - (c + d * x) * b) / (a + b * x) ^ 2 := by ring
      rw [e]
      exact h3
    exact h4.complexToReal_fderiv.hasFDerivWithinAt
  have hinj : Set.InjOn (fun x : ℂ => (c + d * x) / (a + b * x)) s := by
    intro x hx y hy hxy
    have hx' : a + b * x ≠ 0 := hx
    have hy' : a + b * y ≠ 0 := hy
    simp only at hxy
    rw [div_eq_div_iff hx' hy'] at hxy
    apply mul_left_cancel₀ hD
    linear_combination hxy
  have key := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure ℂ) hso.measurableSet hder hinj G
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h.1, h.2] at hD
  have hdb : d ≠ 0 ∨ -b ≠ 0 := by
    by_contra h
    push_neg at h
    have hb : b = 0 := by simpa using h.2
    simp [h.1, hb] at hD
  have him : ∀ᵐ y : ℂ, y ∈ (fun x : ℂ => (c + d * x) / (a + b * x)) '' s := by
    filter_upwards [ae_affine_ne d (-b) hdb] with y hy
    have e1 : a + b * ((a * y - c) / (d + -b * y)) = (a * d - b * c) / (d + -b * y) := by
      rw [eq_div_iff hy, add_mul, mul_assoc, div_mul_cancel₀ _ hy]
      ring
    have e2 : c + d * ((a * y - c) / (d + -b * y)) = y * ((a * d - b * c) / (d + -b * y)) := by
      rw [← mul_div_assoc y, eq_div_iff hy, add_mul, mul_assoc, div_mul_cancel₀ _ hy]
      ring
    have e3 : (a * d - b * c) / (d + -b * y) ≠ 0 := div_ne_zero hD hy
    refine ⟨(a * y - c) / (d + -b * y), ?_, ?_⟩
    · show a + b * ((a * y - c) / (d + -b * y)) ≠ 0
      rw [e1]; exact e3
    · show (c + d * ((a * y - c) / (d + -b * y))) / (a + b * ((a * y - c) / (d + -b * y))) = y
      rw [e1, e2, mul_div_assoc, div_self e3, mul_one]
  have hs' : ∀ᵐ x : ℂ, x ∈ s := ae_affine_ne a b hab
  rw [Measure.restrict_eq_self_of_ae_mem him, Measure.restrict_eq_self_of_ae_mem hs'] at key
  rw [key]
  congr 1
  ext x
  rw [det_smul_one, abs_of_nonneg (Complex.normSq_nonneg _)]
end GlobalTheory.FibLine.UnitaryInv
