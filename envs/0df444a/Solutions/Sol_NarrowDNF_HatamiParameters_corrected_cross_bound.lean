-- Prove2me | solution 1 for NarrowDNF.HatamiParameters.corrected_cross_bound
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:13:59.843297+00:00
-- url     : https://prove2.me/submissions/9131b6a3-7e32-4e03-9b41-eb7e9d35e0dc

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_HatamiParameters

namespace NarrowDNF.HatamiParameters
end NarrowDNF.HatamiParameters

section


/-! Explicit numerical bounds for the parameters in Appendix A. -/
noncomputable section
namespace NarrowDNF.HatamiParameters





private theorem delta_pos (k : ℝ) : 0 < delta k := Real.rpow_pos_of_pos (by norm_num) _
private theorem epsilonOne_pos {e0 : ℝ} (he0 : 0 < e0) (k : ℝ) : 0 < epsilonOne k e0 :=
  mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos he0 _)













end NarrowDNF.HatamiParameters

end

end

noncomputable section
open NarrowDNF
open NarrowDNF.HatamiParameters
theorem solution {e0 k : ℝ} (he0 : 0 < e0) (hk1 : 1 ≤ k)
    (hk : e0⁻¹ ≤ k) : correctedCrossExpression k e0 ≤ e0 := by
  have hk0 : 0 < k := by linarith
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have h2low : (1:ℝ)/2 ≤ Real.log 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
    rw [Real.log_inv] at this
    norm_num at this
    linarith
  have h3 : Real.log 3 ≤ (3:ℝ)/2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(3:ℝ)/2)
    rw [Real.log_div (by norm_num : (3:ℝ)≠0) (by norm_num : (2:ℝ)≠0)] at h
    linarith
  have hlogk : Real.log k ≤ k/2 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hk0 (by norm_num : (0:ℝ)<2))
    rw [Real.log_div hk0.ne' (by norm_num : (2:ℝ)≠0)] at h
    linarith
  have hloge : -Real.log e0 ≤ k/2 := by
    have h := Real.log_le_log (inv_pos.mpr he0) hk
    rw [Real.log_inv] at h
    exact h.trans hlogk
  have hr : 0 < correctedCrossExpression k e0 := by
    unfold correctedCrossExpression
    exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (delta_pos k))
      (sq_pos_of_pos (epsilonOne_pos he0 k))
  apply (Real.log_le_log_iff hr he0).mp
  have heq : Real.log (correctedCrossExpression k e0) =
      9*k*Real.log 2 - 100*k^2*Real.log 2 + 20*k^2*Real.log 3 + 20*k*(-Real.log e0) := by
    unfold correctedCrossExpression delta epsilonOne
    rw [Real.log_div, Real.log_mul, Real.log_pow, Real.log_mul]
    · rw [Real.log_rpow (by norm_num : (0:ℝ)<2), Real.log_rpow (by norm_num : (0:ℝ)<2),
        Real.log_rpow (by norm_num : (0:ℝ)<3), Real.log_rpow he0]
      ring
    all_goals positivity
  rw [heq]
  have hA := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 9*k)
  have hB := mul_le_mul_of_nonneg_left h2low (by positivity : 0 ≤ 100*k^2)
  have hC := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 20*k^2)
  have hD := mul_le_mul_of_nonneg_left hloge (by positivity : 0 ≤ 20*k)
  nlinarith [sq_nonneg (k-1)]
