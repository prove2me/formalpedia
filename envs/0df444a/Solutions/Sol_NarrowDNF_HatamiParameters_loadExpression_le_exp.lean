-- Prove2me | solution 1 for NarrowDNF.HatamiParameters.loadExpression_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:14:03.445656+00:00
-- url     : https://prove2.me/submissions/fa5e1dca-4de6-4642-8dce-3413d7bbad70

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

private theorem log_inverse_lower {e0 k : ℝ} (he0 : 0 < e0) (hk : e0⁻¹ ≤ k) :
    -Real.log e0 ≤ k := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr he0)
  rw [Real.log_inv] at h
  linarith











end NarrowDNF.HatamiParameters

end

end

noncomputable section
open NarrowDNF
open NarrowDNF.HatamiParameters
/-- A conservative bound that directly fits the paper's stated final L,
without changing δ or ε₁. -/
theorem solution {e0 k : ℝ} (he0 : 0 < e0) (hk1 : 1 ≤ k)
    (hk : e0⁻¹ ≤ k) : loadExpression k e0 ≤ Real.exp (10000*k^2) := by
  have hk0 : 0 < k := by linarith
  have hd := delta_pos k
  have he := epsilonOne_pos he0 k
  have hratio : 0 < loadExpression k e0 := by
    unfold loadExpression
    exact div_pos (mul_pos hk0 (Real.rpow_pos_of_pos (by norm_num) _)) (mul_pos hd (sq_pos_of_pos he))
  have hlog2 : Real.log 2 ≤ 1 := by convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2) using 1; norm_num
  have hlog3 : Real.log 3 ≤ 2 := by convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3) using 1; norm_num
  have hlogk : Real.log k ≤ k := by linarith [Real.log_le_sub_one_of_pos hk0]
  have hloge := log_inverse_lower he0 hk
  have hlog : Real.log (loadExpression k e0) ≤ 10000*k^2 := by
    calc
      Real.log (loadExpression k e0) = Real.log k + (2*k+100*k^2)*Real.log 2 +
          20*k^2*Real.log 3 + 20*k*(-Real.log e0) := by
        unfold loadExpression delta epsilonOne
        rw [Real.log_div, Real.log_mul, Real.log_mul, Real.log_pow, Real.log_mul]
        · rw [Real.log_rpow (by norm_num : (0:ℝ)<2), Real.log_rpow (by norm_num : (0:ℝ)<2),
            Real.log_rpow (by norm_num : (0:ℝ)<3), Real.log_rpow he0]
          ring
        all_goals positivity
      _ ≤ k + (2*k+100*k^2)*1 + 20*k^2*2 + 20*k*k := by gcongr
      _ ≤ 10000*k^2 := by nlinarith [sq_nonneg (k-1)]
  exact (Real.log_le_iff_le_exp hratio).mp hlog
