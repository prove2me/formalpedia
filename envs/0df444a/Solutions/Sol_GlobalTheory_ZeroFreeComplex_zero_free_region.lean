-- Prove2me | solution 1 for GlobalTheory.ZeroFreeComplex.zero_free_region
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:20:25.959405+00:00
-- url     : https://prove2.me/submissions/bf2d12f7-dbca-46b7-9a51-2934594a1312

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivativeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegSumLogDerivNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Theorems.Thm_GlobalTheory_ZeroFreeComplex_re_lt_one
import Theorems.Thm_GlobalTheory_ZeroFreeComplex_half_lt_log
import Theorems.Thm_GlobalTheory_ZeroFreeComplex_inv_le_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.ZeroFreeComplex
namespace GlobalTheory.ZeroFreeComplex
theorem _root_.solution : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), χ ≠ 1 → LFunction χ s = 0 → (χ ^ 2 ≠ 1 ∨ s.im ≠ 0) → s.re < 1 - c / Real.log (q * (|s.im| + 2)) := by
  obtain ⟨K, hK, hKb⟩ := inv_le_log
  refine ⟨min (1 / (2 * K)) (1 / 42), by positivity, fun q _ χ s hχ hs hcase => ?_⟩
  have hL : 1 / 2 < Real.log (q * (|s.im| + 2)) := half_lt_log q s.im
  set L := Real.log (q * (|s.im| + 2)) with hL_def
  have hLpos : 0 < L := by linarith
  have hre := re_lt_one hχ hs
  have hδ : 0 < 1 - s.re := by linarith
  have hcL : min (1 / (2 * K)) (1 / 42) / L < 1 - s.re := by
    rw [div_lt_iff₀ hLpos]
    by_cases hsmall : 1 - s.re ≤ 1 / 21
    · have hs' : LFunction χ (((1 - (1 - s.re) : ℝ) : ℂ) + s.im * I) = 0 := by
        rw [show (((1 - (1 - s.re) : ℝ) : ℂ) + s.im * I) = s by
          apply Complex.ext <;> simp]
        exact hs
      have hb := hKb q χ (1 - s.re) s.im hχ hs' hcase hδ hsmall
      rw [div_le_iff₀ hδ] at hb
      have hm : min (1 / (2 * K)) (1 / 42) ≤ 1 / (2 * K) := min_le_left _ _
      have hk : 1 / (2 * K) < (1 - s.re) * L := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    · push Not at hsmall
      have hm : min (1 / (2 * K)) (1 / 42) ≤ 1 / 42 := min_le_right _ _
      nlinarith
  linarith
end GlobalTheory.ZeroFreeComplex
