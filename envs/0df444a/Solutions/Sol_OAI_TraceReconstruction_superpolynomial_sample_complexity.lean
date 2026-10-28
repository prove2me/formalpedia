-- Prove2me | solution 1 for OAI.TraceReconstruction.superpolynomial_sample_complexity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T09:47:50.867225+00:00
-- url     : https://prove2.me/submissions/20c74fa1-c106-4825-8c29-c4c4692dab38

import Mathlib
import Definitions.Def_TraceReconstruction
import Theorems.Thm_OAI_TraceReconstruction_quantitative_sample_lower_bound

section
-- module Solutions.OAIQ9_TR.TraceReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounds

Restored construction and final scales; quantitative sample lower bound and both fixed-channel superpolynomial endpoints.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical ENNReal

/-- Source Theorem 2's sample conclusion at the same fixed deletion channel. -/
theorem superpolynomial_sample_complexity_oai
    (q : ℝ) (hq : q ∈ Set.Ioo 0 1) (s : ℝ) (hs : s ∈ Set.Ioc 0 1)
    (C : ℝ) (hC : 0 < C) :
    Tendsto
      (fun n : ℕ => sampleComplexity n q s / ENNReal.ofReal ((n : ℝ) ^ C))
      atTop (𝓝 ⊤) := by
  let c : ℝ := 1/(8*Real.log 2)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hc : c ∈ Set.Ioo 0 (1/(4*Real.log 2)) := by
    refine ⟨hc0,?_⟩
    dsimp [c]
    apply one_div_lt_one_div_of_lt
    · positivity
    · nlinarith only [hl]
  have hn : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hH : Tendsto (fun n : ℕ => q^3*Real.log (n:ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp hn).const_mul_atTop (pow_pos hq.1 3)
  have hb := quantitative_sample_lower_bound s c hs hc id (fun _ => q) tendsto_id (fun _ => hq) hH
  have he := ((Real.tendsto_log_atTop.comp hH).const_mul_atTop hc0).eventually_ge_atTop (2*C+1)
  have hbound : ∀ᶠ n : ℕ in atTop,(n:ℝ≥0∞) ≤
      sampleComplexity n q s / ENNReal.ofReal ((n:ℝ)^C) := by
    filter_upwards [hb,he,hn.eventually_gt_atTop 1] with n hb he hn1
    dsimp only [Function.comp_apply] at he
    have hn0 : 0 < (n:ℝ) := zero_lt_one.trans hn1
    have hpow : (n:ℝ)^(C+1) ≤ (n:ℝ)^(c*Real.log (q^3*Real.log (n:ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith only [he,hC])
    have hnC : 0 < (n:ℝ)^C := Real.rpow_pos_of_pos hn0 C
    have hdiv : ENNReal.ofReal ((n:ℝ)^(C+1)) /
        ENNReal.ofReal ((n:ℝ)^C) = (n:ℝ≥0∞) := by
      rw [← ENNReal.ofReal_div_of_pos hnC,Real.rpow_add hn0,Real.rpow_one]
      rw [mul_div_cancel_left₀ _ hnC.ne',ENNReal.ofReal_natCast]
    rw [← hdiv]
    exact ENNReal.div_le_div_right ((ENNReal.ofReal_le_ofReal hpow).trans hb) _
  apply ENNReal.tendsto_nhds_top
  intro k
  filter_upwards [hbound,eventually_gt_atTop k] with n hn hk
  exact (show (k:ℝ≥0∞) < (n:ℝ≥0∞) by exact_mod_cast hk).trans_le hn

end TraceReconstruction

end
end
end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.TraceReconstruction.superpolynomial_sample_complexity_oai := @OAI.TraceReconstruction.superpolynomial_sample_complexity_oai
