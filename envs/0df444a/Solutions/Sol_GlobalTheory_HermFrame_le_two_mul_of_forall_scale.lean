-- Prove2me | solution 1 for GlobalTheory.HermFrame.le_two_mul_of_forall_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:21.808852+00:00
-- url     : https://prove2.me/submissions/f6a09629-6ea7-44b2-a556-e0712b97c6f7

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero

set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable {H : Matrix m m ℂ} {K : Matrix n n ℂ} {L : Matrix l l ℂ}
namespace GlobalTheory.HermFrame
theorem _root_.solution {x c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ s, 0 < s → x ≤ c * (s * a ^ 2 + b ^ 2 / s)) : x ≤ 2 * c * a * b := by
  have h1 : ∀ ε : ℝ, 0 < ε → x ≤ 2 * c * (a + ε) * (b + ε) := fun ε hε => by
    have ha' : 0 < a + ε := by linarith
    have hb' : 0 < b + ε := by linarith
    refine (h ((b + ε) / (a + ε)) (by positivity)).trans ?_
    have e1 : (b + ε) / (a + ε) * a ^ 2 ≤ (a + ε) * (b + ε) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ ha']
      have : a ^ 2 ≤ (a + ε) ^ 2 := by nlinarith
      nlinarith
    have e2 : b ^ 2 / ((b + ε) / (a + ε)) ≤ (a + ε) * (b + ε) := by
      rw [div_div_eq_mul_div, div_le_iff₀ hb']
      have : b ^ 2 ≤ (b + ε) ^ 2 := by nlinarith
      nlinarith
    nlinarith
  have h2 : Filter.Tendsto (fun ε : ℝ => 2 * c * (a + ε) * (b + ε)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 * c * (a + 0) * (b + 0))) :=
    (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
  simpa using ge_of_tendsto h2 (eventually_nhdsWithin_of_forall h1)
end GlobalTheory.HermFrame
