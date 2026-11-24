-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.exists_dyadic_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:54:55.252229+00:00
-- url     : https://prove2.me/submissions/458fa313-3ba1-4b01-bf7d-f54669542768

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxIntegralSmallBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
variable {P ι : Type} [Fintype P] [Fintype ι]
namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
theorem _root_.solution (f : (P → ι → ℝ) → ℝ) (N : ℕ) (K : ℝ) (x : P → ι → ℝ)
    (hf : 0 ≤ f x) (hx : f x * (1 + ∑ w, ‖x w‖) ^ N ≤ K) :
    ∃ j : ℕ, x ∈ (boxR (fun _ => (2 : ℝ) ^ j) : Set (P → ι → ℝ)) ∧
      f x ≤ K * 2 ^ N * (1 / 2) ^ (j * N) := by
  classical
  have hs0 : 0 ≤ ∑ w, ‖x w‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hle : ∀ w, ‖x w‖ ≤ ∑ w, ‖x w‖ := fun w =>
    Finset.single_le_sum (f := fun w => ‖x w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  have hex : ∃ j : ℕ, x ∈ (boxR (fun _ => (2 : ℝ) ^ j) : Set (P → ι → ℝ)) := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (∑ w, ‖x w‖) (by norm_num : (1 : ℝ) < 2)
    exact ⟨j, fun w => (hle w).trans hj.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  have h2 : (2 : ℝ) ^ (Nat.find hex) ≤ 2 * (1 + ∑ w, ‖x w‖) := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; norm_num; linarith
    · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hnot : x ∉ (boxR (fun _ => (2 : ℝ) ^ k) : Set (P → ι → ℝ)) :=
        Nat.find_min hex (by omega)
      simp only [boxR, Set.mem_setOf_eq, not_forall, not_le] at hnot
      obtain ⟨w, hw⟩ := hnot
      have := hle w
      rw [hk, pow_succ]
      linarith
  generalize Nat.find hex = j at h2
  have h3 : ((2 : ℝ) ^ j) ^ N ≤ 2 ^ N * (1 + ∑ w, ‖x w‖) ^ N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h2 N
  have h4 : f x * ((2 : ℝ) ^ j) ^ N ≤ K * 2 ^ N := by
    calc f x * ((2 : ℝ) ^ j) ^ N ≤ f x * (2 ^ N * (1 + ∑ w, ‖x w‖) ^ N) :=
          mul_le_mul_of_nonneg_left h3 hf
      _ = (f x * (1 + ∑ w, ‖x w‖) ^ N) * 2 ^ N := by ring
      _ ≤ K * 2 ^ N := by gcongr
  have h5 : ((2 : ℝ) ^ j) ^ N * ((1 : ℝ) / 2) ^ (j * N) = 1 := by
    rw [← pow_mul, ← mul_pow]; norm_num
  calc f x = f x * (((2 : ℝ) ^ j) ^ N * (1 / 2) ^ (j * N)) := by rw [h5, mul_one]
    _ = (f x * ((2 : ℝ) ^ j) ^ N) * (1 / 2) ^ (j * N) := by ring
    _ ≤ K * 2 ^ N * (1 / 2) ^ (j * N) := by gcongr
end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
