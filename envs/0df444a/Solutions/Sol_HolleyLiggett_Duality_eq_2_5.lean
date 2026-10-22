-- Prove2me | solution 1 for HolleyLiggett.Duality.eq_2_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:16:51.074987+00:00
-- url     : https://prove2.me/submissions/95a4a966-6aad-498d-b9b4-c6e2fd242e77

import Mathlib
import Definitions.Def_HolleyLiggett_Duality_Setting
set_option autoImplicit false
open HolleyLiggett.Duality
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution {I : Type*} [Countable I] [DecidableEq I] (N : I → ℕ → Finset I)
    (hN0 : ∀ i, N i 0 = ∅) (f : I → PMF ℕ)
    (n : ℕ) (η : Config I) (F : Finset I) :
    dualProb N f (n + 1) F η =
      ∑' k : (↥F → ℕ),
        dualProb N f n (Finset.univ.biUnion (fun i : ↥F => N i (k i))) η * ∏ i : ↥F, f i (k i) := by
  classical
  have e : ∀ (m : ℕ) (F B : Finset I), bpiProb N f (m + 1) F B =
      ∑' G, bpiProb N f m F G * bpiStep N f G B := fun _ _ _ => rfl
  have e0 : ∀ (F B : Finset I), bpiProb N f 0 F B = if F = B then 1 else 0 := fun _ _ => rfl
  -- Chapman-Kolmogorov, first-step form
  have ck : ∀ (n : ℕ) (F B : Finset I),
      bpiProb N f (n + 1) F B = ∑' G, bpiStep N f F G * bpiProb N f n G B := by
    intro n
    induction n with
    | zero =>
      intro F B
      rw [e]
      simp only [e0]
      rw [tsum_eq_single F (fun G hG => by simp [Ne.symm hG]), tsum_eq_single B (fun G hG => by simp [hG])]
      simp
    | succ n ih =>
      intro F B
      rw [e (n + 1) F B]
      have hF : ∀ G, bpiProb N f (n + 1) F G = ∑' H, bpiStep N f F H * bpiProb N f n H G := fun G => ih F G
      simp_rw [hF]
      simp_rw [← ENNReal.tsum_mul_right]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun H => ?_
      rw [e n H B, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun G => ?_
      ring
  have step : ∀ (G : Finset I), bpiStep N f F G =
      ∑' k : (↥F → ℕ), if Finset.univ.biUnion (fun i : ↥F => N i (k i)) = G then ∏ i : ↥F, f i (k i) else 0 := by
    intro G; rfl
  have h1 : dualProb N f (n + 1) F η = ∑' G, bpiStep N f F G * dualProb N f n G η := by
    unfold dualProb
    simp_rw [ck, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun G => tsum_congr fun B => ?_
    ring
  rw [h1]
  simp_rw [step, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  rw [tsum_eq_single (Finset.univ.biUnion (fun i : ↥F => N i (k i)))]
  · simp [mul_comm]
  · intro G hG
    rw [if_neg (Ne.symm hG), zero_mul]
