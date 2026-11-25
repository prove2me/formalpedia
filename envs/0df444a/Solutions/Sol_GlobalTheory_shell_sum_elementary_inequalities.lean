-- Prove2me | solution 1 for GlobalTheory.shell_sum_elementary_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:34:18.64472+00:00
-- url     : https://prove2.me/submissions/2a4bc81b-2474-451b-89c4-df2802c3e64f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ShellSumElementaryInequalities
import Theorems.Thm_GlobalTheory_exp_neg_mul_two_pow_le_geometric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (s ep c : ℝ), 0 < ep → ep ≤ s → 0 < c → ep ≤ 1 / c → ep * s ≤ min (s ^ 2) (s / c)) ∧ (∀ T : ℝ, 1 ≤ T → Summable (fun i : ℕ => Real.exp (-T * 2 ^ i)) ∧ ∑' i : ℕ, Real.exp (-T * 2 ^ i) ≤ 2 * Real.exp (-T)) ∧ ∀ (al be : ℝ) (f : ℕ), 0 ≤ al → al ≤ 2 → 0 ≤ be → be ≤ 1 → (al + be) ^ f - al ^ f ≤ f * be * 3 ^ f := by
  refine ⟨?_, ?_, ?_⟩
  · intro s ep c hep hs hc hc'
    have hs0 : 0 ≤ s := le_trans hep.le hs
    refine le_min ?_ ?_
    · rw [sq]
      exact mul_le_mul_of_nonneg_right hs hs0
    · calc ep * s ≤ (1 / c) * s := mul_le_mul_of_nonneg_right hc' hs0
        _ = s / c := by ring
  · intro T hT
    have hg : Summable (fun i : ℕ => Real.exp (-T) * (1 / 2 : ℝ) ^ i) :=
      summable_geometric_two.mul_left _
    have hs : Summable (fun i : ℕ => Real.exp (-T * 2 ^ i)) :=
      Summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le)
        (fun i => exp_neg_mul_two_pow_le_geometric T hT i) hg
    refine ⟨hs, ?_⟩
    calc ∑' i : ℕ, Real.exp (-T * 2 ^ i) ≤ ∑' i : ℕ, Real.exp (-T) * (1 / 2 : ℝ) ^ i :=
          Summable.tsum_le_tsum (fun i => exp_neg_mul_two_pow_le_geometric T hT i) hs hg
      _ = 2 * Real.exp (-T) := by rw [tsum_mul_left, tsum_geometric_two, mul_comm]
  · intro al be f h0 h2 hb0 hb1
    induction f with
    | zero => simp
    | succ n ih =>
      have hX : 0 ≤ (al + be) ^ n - al ^ n :=
        sub_nonneg.mpr (pow_le_pow_left₀ h0 (by linarith) n)
      have ha : al ^ n ≤ 3 ^ n := pow_le_pow_left₀ h0 (by linarith) n
      have h1 : (al + be) * ((al + be) ^ n - al ^ n) ≤ 3 * ((n : ℝ) * be * 3 ^ n) :=
        mul_le_mul (by linarith) ih hX (by norm_num)
      have h3 : be * al ^ n ≤ be * 3 ^ n := mul_le_mul_of_nonneg_left ha hb0
      have h4 : 0 ≤ be * 3 ^ n := mul_nonneg hb0 (pow_nonneg (by norm_num) n)
      calc (al + be) ^ (n + 1) - al ^ (n + 1)
          = (al + be) * ((al + be) ^ n - al ^ n) + be * al ^ n := by ring
        _ ≤ 3 * ((n : ℝ) * be * 3 ^ n) + be * 3 ^ n := by linarith
        _ ≤ ((n + 1 : ℕ) : ℝ) * be * 3 ^ (n + 1) := by
          push_cast
          rw [pow_succ]
          nlinarith
end GlobalTheory
