-- Prove2me | solution 1 for GlobalTheory.GaussWidths.integral_gauss_mul_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:18:15.274009+00:00
-- url     : https://prove2.me/submissions/c67728b3-1008-41f6-84b2-be949c4ce17a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzGaussWidth
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.GaussWidths
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory.GaussWidths
theorem _root_.solution (s c : ℝ) (hs : 0 < s) (hc : 0 < c) (y : E) :
    ∫ a : E, Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) =
      ((Real.pi : ℂ) / ((s + c : ℝ) : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
        Complex.exp (-(((s * c / (s + c)) * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
  have hsc : 0 < s + c := by linarith
  have key : ∀ a : E, Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) =
      Complex.exp (-((s + c : ℝ) : ℂ) * (‖a‖ : ℂ) ^ 2 + ((2 * c : ℝ) : ℂ) * ((inner ℝ y a : ℝ) : ℂ)) *
        Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
    intro a
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [norm_sub_sq_real]
    push_cast
    ring
  simp_rw [key]
  rw [integral_mul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (by simpa using hsc) _ y, mul_assoc, ← Complex.exp_add]
  congr 2
  have h1 : ((s + c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsc.ne'
  push_cast at h1 ⊢
  field_simp
  ring
end GlobalTheory.GaussWidths
