-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.tendsto_pow_mul_exp_neg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:23.71239+00:00
-- url     : https://prove2.me/submissions/32650a48-7ed3-468d-8ab9-16478e81e446

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function
open scoped ContDiff FourierTransform
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {r : ℝ} (hr : 0 < r) (q : ℕ) :
    Tendsto (fun a : ℝ => (1 + a) ^ q * exp (-a * r)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun a : ℝ => (1 + a) * r) atTop atTop :=
    (tendsto_atTop_add_const_left _ 1 tendsto_id).atTop_mul_const hr
  have h2 := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero q).comp h1).const_mul (exp r / r ^ q)
  rw [mul_zero] at h2
  refine h2.congr fun a => ?_
  simp only [Function.comp_apply]
  rw [mul_pow, show -((1 + a) * r) = -a * r + -r by ring, exp_add, exp_neg]
  field_simp
end GroundTheory.Automorphic.LineKernel
