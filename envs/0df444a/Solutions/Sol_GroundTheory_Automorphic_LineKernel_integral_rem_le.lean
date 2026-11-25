-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.integral_rem_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:57.20254+00:00
-- url     : https://prove2.me/submissions/7d1b5272-1ec1-484d-9b22-e38c89adf3e8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_iteratedDeriv_deriv_cutoff_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_deriv_cutoff
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_rem_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_deriv_cutoff_nonpos
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_rem
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_deriv_cutoff

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
theorem _root_.solution {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r) : ∫ t, rem a r t ≤ exp (-a * r) := by
  have hint : Integrable (deriv (cutoff r)) :=
    (contDiff_deriv_cutoff r).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun t ht => by
        by_contra h
        exact ht (by simpa using iteratedDeriv_deriv_cutoff_eq_zero hr h 0)))
  calc ∫ t, rem a r t ≤ ∫ t, exp (-a * r) * -deriv (cutoff r) t := by
        refine integral_mono (integrable_rem hr) (hint.neg.const_mul _) fun t => ?_
        by_cases ht : t ∈ Icc r (2 * r)
        · unfold rem
          have h1 : exp (-a * t) ≤ exp (-a * r) := exp_le_exp.2 (by nlinarith [ht.1])
          have h2 := deriv_cutoff_nonpos hr t
          nlinarith
        · rw [rem_eq_zero hr ht]
          have := iteratedDeriv_deriv_cutoff_eq_zero hr ht 0
          simp only [iteratedDeriv_zero] at this
          simp [this]
    _ = exp (-a * r) := by
        rw [integral_const_mul, integral_neg, integral_deriv_cutoff hr]; ring
end GroundTheory.Automorphic.LineKernel
