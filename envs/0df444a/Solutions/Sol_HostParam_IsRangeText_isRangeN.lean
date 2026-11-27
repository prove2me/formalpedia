-- Prove2me | solution 1 for HostParam.IsRangeText.isRangeN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:49:15.292846+00:00
-- url     : https://prove2.me/submissions/5f50e1ae-b951-4885-b4c0-f3aceb22cf51

import Definitions.Def_Development_AutomorphicArithmetic_QuadraticCharacters_LogDerivAtOne
import Definitions.Def_Development_AutomorphicArithmetic_QuadraticCharacters_PreHostA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction
open HostParam
namespace HostParam
namespace IsRangeText
theorem _root_.solution {T : HostType} {x : ℝ} {e : ℕ} (h : IsRangeText T x e) (hx : 3 ≤ x) :
    IsRangeN T x e := by
  have h1 : x ^ (2 : ℝ) ≤ x ^ (2 + 8 * T.eps) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [T.eps_pos])
  rw [Real.rpow_two] at h1
  have h2 := h.1
  have ho : (1 : ℝ) ≤ T.o := by exact_mod_cast T.o_pos
  refine ⟨?_, le_trans (div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)) h2, h.2⟩
  by_contra hlt
  have h4 : (2 : ℝ) ^ e ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith
end IsRangeText
end HostParam
