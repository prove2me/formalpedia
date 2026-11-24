-- Prove2me | solution 1 for GlobalTheory.PowerSumSecond.norm_sum_pow_mul_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:33.610136+00:00
-- url     : https://prove2.me/submissions/2df00964-758e-4db8-8d5f-a9b573cf9337

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsProdAbsSubGeOnSegment
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsInterpolationExteriorSmallCoeffsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TuranSecondMainTheoremPowerSumsUnitCoefficients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory
open GlobalTheory.PowerSumSecond
namespace GlobalTheory.PowerSumSecond
theorem _root_.solution {ι κ : Type*} [Fintype ι] (z : ι → ℂ) (a : κ → ℂ) (B : ℝ)
    (T : Finset κ) (ha : ∀ t ∈ T, ‖a t‖ ≤ 1) :
    ∀ m : ℕ, (∀ k, m ≤ k → k ≤ m + T.card → ‖∑ i, z i ^ k‖ ≤ B) →
      ‖∑ i, z i ^ m * ∏ t ∈ T, (z i - a t)‖ ≤ 2 ^ T.card * B := by
  classical
  induction T using Finset.induction_on with
  | empty => intro m h; simpa using h m le_rfl (by simp)
  | insert t T ht ih =>
    intro m h
    rw [Finset.card_insert_of_notMem ht] at h ⊢
    have ha' : ∀ s ∈ T, ‖a s‖ ≤ 1 := fun s hs => ha s (Finset.mem_insert_of_mem hs)
    have h1 := ih ha' (m + 1) (fun k h1 h2 => h k (by omega) (by omega))
    have h2 := ih ha' m (fun k h1 h2 => h k (by omega) (by omega))
    have e : ∑ i, z i ^ m * ∏ s ∈ insert t T, (z i - a s)
        = ∑ i, z i ^ (m + 1) * ∏ s ∈ T, (z i - a s)
          - a t * ∑ i, z i ^ m * ∏ s ∈ T, (z i - a s) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.prod_insert ht]; ring
    rw [e]
    have h3 : ‖a t * ∑ i, z i ^ m * ∏ s ∈ T, (z i - a s)‖ ≤ 2 ^ T.card * B := by
      rw [norm_mul]
      calc _ ≤ 1 * ‖∑ i, z i ^ m * ∏ s ∈ T, (z i - a s)‖ :=
            mul_le_mul_of_nonneg_right (ha t (Finset.mem_insert_self _ _)) (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h2
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ 2 ^ T.card * B + 2 ^ T.card * B := add_le_add h1 h3
      _ = _ := by ring
end GlobalTheory.PowerSumSecond
