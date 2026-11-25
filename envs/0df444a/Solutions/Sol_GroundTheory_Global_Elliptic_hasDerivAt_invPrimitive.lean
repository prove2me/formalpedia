-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.hasDerivAt_invPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:41.01881+00:00
-- url     : https://prove2.me/submissions/e3ed8c3a-8699-4b77-bd46-bc81d1a283e2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (invPrimitive c) ((x : ℂ) + c * I)⁻¹ x := by
  have hpos : 0 < x ^ 2 + c ^ 2 := by positivity
  have h1 : HasDerivAt (fun x : ℝ ↦ Real.log (x ^ 2 + c ^ 2) / 2) (x / (x ^ 2 + c ^ 2)) x := by
    have := (((hasDerivAt_pow 2 x).add_const (c ^ 2)).log hpos.ne').div_const 2
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  have h2 : HasDerivAt (fun x : ℝ ↦ Real.arctan (x / c)) (c / (x ^ 2 + c ^ 2)) x := by
    have := ((hasDerivAt_id' x).div_const c).arctan
    refine this.congr_deriv ?_
    field_simp
    ring
  have h3 : HasDerivAt (invPrimitive c)
      (((x / (x ^ 2 + c ^ 2) : ℝ) : ℂ) - I * ((c / (x ^ 2 + c ^ 2) : ℝ) : ℂ)) x :=
    h1.ofReal_comp.sub (h2.ofReal_comp.const_mul I)
  refine h3.congr_deriv ?_
  apply Complex.ext
  · rw [Complex.inv_re, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, add_im, mul_im, sub_re]
    ring
  · rw [Complex.inv_im, Complex.normSq_apply]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, add_im, mul_im, sub_im]
    ring
end GroundTheory.Global.Elliptic
