-- Prove2me | solution 1 for GroundTheory.Global.complexFourier_conj_pow_mul_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:54:23.153509+00:00
-- url     : https://prove2.me/submissions/f00bbe4c-df69-4a3f-a4c3-787a97d0fe78

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Theorems.Thm_GroundTheory_Global_complexFourier_pow_mul_gaussian
import Theorems.Thm_GroundTheory_Global_complexFourier_conj
import Theorems.Thm_GroundTheory_Global_conj_cexp_neg_two_pi_norm_sq
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution (n : ℕ) :
    complexFourier (fun z ↦ conj z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) =
      fun w ↦ (-I) ^ n * (w ^ n * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) := by
  funext w
  have e : (fun z : ℂ ↦ conj z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) =
      fun z ↦ conj (z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) := by
    funext z
    rw [map_mul, map_pow, conj_cexp_neg_two_pi_norm_sq]
  rw [e, complexFourier_conj, complexFourier_pow_mul_gaussian]
  simp only [map_mul, map_pow, map_neg, conj_I, conj_conj, conj_cexp_neg_two_pi_norm_sq,
    norm_neg]
  ring
end GroundTheory.Global
