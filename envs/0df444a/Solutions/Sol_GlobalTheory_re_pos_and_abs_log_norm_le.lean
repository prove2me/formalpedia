-- Prove2me | solution 1 for GlobalTheory.re_pos_and_abs_log_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:31:20.59913+00:00
-- url     : https://prove2.me/submissions/ab9e68bc-a79c-4fb9-883f-792f5950a7f2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {d : ℂ} {t : ℝ} (ht : t ≤ 1 / 6) (hd : ‖d - 1‖ ≤ 2 * t) :
    0 < d.re ∧ |Real.log ‖d‖| ≤ 3 * t := by
  have h0 : 0 ≤ t := by linarith [norm_nonneg (d - 1)]
  have h1 := abs_le.1 ((Complex.abs_re_le_norm _).trans hd)
  rw [Complex.sub_re, Complex.one_re] at h1
  have h2 := abs_le.1 ((abs_norm_sub_norm_le d 1).trans hd)
  rw [norm_one] at h2
  have hp : 0 < ‖d‖ := by linarith
  refine ⟨by linarith, abs_le.2 ⟨?_, ?_⟩⟩
  · have h3 := Real.one_sub_inv_le_log_of_pos hp
    have h4 : ‖d‖⁻¹ ≤ 1 + 3 * t := by
      rw [inv_le_iff_one_le_mul₀ hp]
      nlinarith
    linarith
  · linarith [Real.log_le_sub_one_of_pos hp]
end GlobalTheory
