-- Prove2me | solution 1 for MomentComparison.cpow_div_of_arg_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:21:15.193545+00:00
-- url     : https://prove2.me/submissions/004e8653-6605-4b8e-bc93-3f266cd34327

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Definitions.Def_MomentComparison_ComplexPower
public import Theorems.Thm_MomentComparison_arg_div_of_arg_sub

set_option autoImplicit true
@[expose] public section
public section
open MomentComparison
namespace MomentComparison
theorem _root_.solution {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hlo : -Real.pi < x.arg - y.arg) (hhi : x.arg - y.arg ≤ Real.pi) (b : ℂ) :
    (x / y) ^ b = x ^ b / y ^ b := by
  have hlog : Complex.log (x / y) = Complex.log x - Complex.log y := by
    apply Complex.ext
    · rw [Complex.log_re, Complex.sub_re, Complex.log_re, Complex.log_re, norm_div,
        Real.log_div (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)]
    · simpa only [Complex.sub_im, Complex.log_im] using arg_div_of_arg_sub hx hy hlo hhi
  simp only [Complex.cpow_def_of_ne_zero (div_ne_zero hx hy), Complex.cpow_def_of_ne_zero hx,
    Complex.cpow_def_of_ne_zero hy, hlog, sub_mul, Complex.exp_sub]
end MomentComparison
