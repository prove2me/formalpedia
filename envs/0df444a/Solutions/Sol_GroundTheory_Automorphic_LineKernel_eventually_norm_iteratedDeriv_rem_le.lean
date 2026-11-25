-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.eventually_norm_iteratedDeriv_rem_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:38.241929+00:00
-- url     : https://prove2.me/submissions/e2092263-7065-4800-a0a0-7aa04365fce4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv_rem_le
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_tendsto_pow_mul_exp_neg_mul

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
theorem _root_.solution {r : ℝ} (hr : 0 < r) (q : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ a in atTop, ∀ t, ‖iteratedDeriv q (rem a r) t‖ ≤ δ := by
  obtain ⟨S, hS0, hS⟩ := norm_iteratedDeriv_rem_le hr q
  have ht : Tendsto (fun a : ℝ => 2 ^ q * ((1 + a) ^ q * exp (-a * r)) * S) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_mul_exp_neg_mul hr q).const_mul (2 ^ q)).mul_const S
  filter_upwards [ht.eventually (ge_mem_nhds hδ), eventually_ge_atTop 0] with a ha ha0 t
  refine (hS a ha0 t).trans ?_
  calc 2 ^ q * (1 + a) ^ q * exp (-a * r) * S = 2 ^ q * ((1 + a) ^ q * exp (-a * r)) * S := by ring
    _ ≤ δ := ha
end GroundTheory.Automorphic.LineKernel
