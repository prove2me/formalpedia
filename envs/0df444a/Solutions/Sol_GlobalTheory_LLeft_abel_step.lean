-- Prove2me | solution 1 for GlobalTheory.LLeft.abel_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:37:31.560835+00:00
-- url     : https://prove2.me/submissions/d24f7c98-982c-485e-9337-850046a1d18f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open GlobalTheory.LLeft
namespace GlobalTheory.LLeft
theorem _root_.solution (q : ℕ) (hq : 0 < q) (a : ℕ → ℂ) (M : ℝ) (hp : Function.Periodic a q)
    (h0 : ∑ n ∈ Finset.range q, a n = 0) (hM : ∀ n, ‖a n‖ ≤ M) :
    ∃ (b : ℕ → ℂ) (μ : ℂ), Function.Periodic b q ∧ ∑ n ∈ Finset.range q, b n = 0 ∧
      (∀ n, ‖b n‖ ≤ 2 * q * M) ∧ ‖μ‖ ≤ q * M ∧
      ∀ f : ℕ → ℂ, Summable (fun n => ‖f n‖) →
        ∑' n, a n * f n = μ * f 0 + ∑' n, b n * (f n - f (n + 1)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set T : ℕ → ℂ := fun n => ∑ k ∈ Finset.range n, a k with hT
  have hTp : Function.Periodic T q := by
    intro n
    induction n with
    | zero => simp [hT, h0]
    | succ n ih =>
      have e : n + 1 + q = (n + q) + 1 := by ring
      simp only [hT] at ih ⊢
      rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, hp n]
  have hTb : ∀ n, ‖T n‖ ≤ q * M := by
    intro n
    rw [← hTp.map_mod_nat n]
    calc ‖T (n % q)‖ ≤ ∑ k ∈ Finset.range (n % q), ‖a k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (n % q), M := Finset.sum_le_sum fun k _ => hM k
      _ = (n % q : ℕ) * M := by simp
      _ ≤ q * M := by
        gcongr
        exact (Nat.mod_lt n hq).le
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  set μ : ℂ := (∑ n ∈ Finset.range q, T (n + 1)) / q with hμ
  have hμb : ‖μ‖ ≤ q * M := by
    rw [hμ, norm_div, Complex.norm_natCast, div_le_iff₀ hq']
    calc _ ≤ ∑ n ∈ Finset.range q, ‖T (n + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range q, q * M := Finset.sum_le_sum fun k _ => hTb _
      _ = _ := by simp; ring
  have hbb : ∀ n, ‖T (n + 1) - μ‖ ≤ 2 * q * M := fun n =>
    (norm_sub_le _ _).trans (by linarith [hTb (n + 1)])
  refine ⟨fun n => T (n + 1) - μ, μ, ?_, ?_, hbb, hμb, ?_⟩
  · intro n
    have e : n + q + 1 = (n + 1) + q := by ring
    simp only [e, hTp (n + 1)]
  · rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hμ]
    field_simp
    ring
  · intro f hf
    have hf1 : Summable (fun n => ‖f (n + 1)‖) := (summable_nat_add_iff 1).mpr hf
    have sm : ∀ (c g : ℕ → ℂ) (K : ℝ), (∀ n, ‖c n‖ ≤ K) → Summable (fun n => ‖g n‖) →
        Summable (fun n => c n * g n) := by
      intro c g K hc hg
      refine Summable.of_norm_bounded (hg.mul_left K) fun n => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _)
    have s1 := sm a f M hM hf
    have s2 := sm _ f _ hbb hf
    have s3 := sm _ _ _ hbb hf1
    have s4 := sm (fun n => T (n + 1 + 1) - μ) _ _ (fun n => hbb (n + 1)) hf1
    have e1 : ∀ n, a (n + 1) * f (n + 1)
        = (T (n + 1 + 1) - μ) * f (n + 1) - (T (n + 1) - μ) * f (n + 1) := by
      intro n
      simp only [hT, Finset.sum_range_succ _ (n + 1)]
      ring
    simp only [mul_sub _ (f _)]
    rw [s1.tsum_eq_zero_add, s2.tsum_sub s3, s2.tsum_eq_zero_add]
    simp only [e1]
    rw [s4.tsum_sub s3]
    simp only [hT, zero_add, Finset.sum_range_one]
    ring
end GlobalTheory.LLeft
