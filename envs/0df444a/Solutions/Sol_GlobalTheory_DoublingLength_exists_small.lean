-- Prove2me | solution 1 for GlobalTheory.DoublingLength.exists_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:27:23.816375+00:00
-- url     : https://prove2.me/submissions/8054515d-e1a4-47ad-96a2-bd4b74d532b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.DoublingLength
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace GlobalTheory.DoublingLength
theorem _root_.solution (q : ℝ) (hq0 : 0 ≤ q) (γ : Fin n → ℂ) : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 ≤ x → x < δ → ∀ i : Fin n,
    q ^ (n - 1 - (i : ℕ)) * ‖γ i‖ * x < 1 ∧ q ^ (i : ℕ) * ‖γ i‖⁻¹ * x < 1 ∧ q ^ (i : ℕ) * x ^ 2 < 1 := by
  obtain ⟨S, hS, hS0⟩ : ∃ S : ℝ, (∀ i, ‖γ i‖ + ‖γ i‖⁻¹ ≤ S) ∧ 0 ≤ S :=
    ⟨∑ i, (‖γ i‖ + ‖γ i‖⁻¹), fun i => Finset.single_le_sum (f := fun i => ‖γ i‖ + ‖γ i‖⁻¹)
      (fun j _ => by positivity) (Finset.mem_univ i), Finset.sum_nonneg fun j _ => by positivity⟩
  have hq1 : 1 ≤ q + 1 := by linarith
  have hM1 : 1 ≤ (q + 1) ^ n * (1 + S) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq1) (by linarith)
  have hM0 : 0 < (q + 1) ^ n * (1 + S) := by linarith
  have hpow : ∀ m ≤ n, q ^ m ≤ (q + 1) ^ n := fun m hm =>
    (pow_le_pow_left₀ hq0 (by linarith) m).trans (pow_le_pow_right₀ hq1 hm)
  have key : ∀ m ≤ n, ∀ c : ℝ, 0 ≤ c → c ≤ 1 + S → ∀ x : ℝ, 0 ≤ x → x < ((q + 1) ^ n * (1 + S))⁻¹ →
      q ^ m * c * x < 1 := by
    intro m hm c hc0 hc x hx0 hx
    have h1 : q ^ m * c ≤ (q + 1) ^ n * (1 + S) := mul_le_mul (hpow m hm) hc hc0 (by positivity)
    calc q ^ m * c * x ≤ (q + 1) ^ n * (1 + S) * x := mul_le_mul_of_nonneg_right h1 hx0
      _ < (q + 1) ^ n * (1 + S) * ((q + 1) ^ n * (1 + S))⁻¹ := mul_lt_mul_of_pos_left hx hM0
      _ = 1 := mul_inv_cancel₀ hM0.ne'
  refine ⟨_, inv_pos.2 hM0, fun x hx0 hx i => ⟨?_, ?_, ?_⟩⟩
  · exact key _ (by omega) _ (norm_nonneg _) (by linarith [hS i, inv_nonneg.2 (norm_nonneg (γ i))]) x hx0 hx
  · exact key _ i.2.le _ (by positivity) (by linarith [hS i, norm_nonneg (γ i)]) x hx0 hx
  · have hx1 : x ≤ 1 := hx.le.trans (inv_le_one_of_one_le₀ hM1)
    rw [sq, ← mul_assoc]
    exact key _ i.2.le _ hx0 (by linarith) x hx0 hx
end GlobalTheory.DoublingLength
