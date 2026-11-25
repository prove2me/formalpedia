-- Prove2me | solution 1 for GlobalTheory.ThetaRunParameters.exists_large_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:10.868981+00:00
-- url     : https://prove2.me/submissions/5b4de838-8257-49f1-b98e-1f392889fdb6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaRunParametersUniformTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.ThetaRunParameters
namespace GlobalTheory.ThetaRunParameters
theorem _root_.solution (B c₁ c₂ d C : ℝ) (hB : 0 < B) (hd : 0 ≤ d) :
    ∃ q : ℕ, 1 ≤ q ∧ c₁ < q ∧ c₂ ≤ (q : ℝ) / 2 ∧ 1 ≤ (q : ℝ) / B ∧
      4 * (7 + Real.log q) + d + 1 ≤ q * ((q : ℝ) / B) ∧ C ≤ q * ((q : ℝ) / B) := by
  obtain ⟨q, hq⟩ := exists_nat_gt (1 + |c₁| + 2 * |c₂| + B * (33 + d + |C|))
  have h1 := abs_nonneg c₁
  have h2 := abs_nonneg c₂
  have h3 := abs_nonneg C
  have h1' := le_abs_self c₁
  have h2' := le_abs_self c₂
  have h3' := le_abs_self C
  have h4 : 0 ≤ B * (33 + d + |C|) := by positivity
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hK : 33 + d + |C| ≤ (q : ℝ) / B := by
    rw [le_div_iff₀ hB]; linarith
  have hlog : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hm : (q : ℝ) * (33 + d + |C|) ≤ q * ((q : ℝ) / B) :=
    mul_le_mul_of_nonneg_left hK (by linarith)
  have hqd : d ≤ q * d := le_mul_of_one_le_left hd hq1
  have hqC : |C| ≤ q * |C| := le_mul_of_one_le_left h3 hq1
  refine ⟨q, by exact_mod_cast hq1, by linarith, by linarith, by linarith, ?_, ?_⟩
  · nlinarith
  · nlinarith
end GlobalTheory.ThetaRunParameters
