-- Prove2me | solution 1 for GlobalTheory.ZeroBand.band_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:48.643388+00:00
-- url     : https://prove2.me/submissions/ec0a27e8-8f78-4c67-83cb-1bbac3dca40e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinsumMemLeOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteBox
import Theorems.Thm_GlobalTheory_ZeroBand_finite_box
import Theorems.Thm_GlobalTheory_ZeroBand_norm_term_le
import Theorems.Thm_GlobalTheory_LLeft_norm_term_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ZeroBand
namespace GlobalTheory.ZeroBand
theorem _root_.solution (f : ℂ → ℂ) (m : ℂ → ℕ) (B : ℝ → ℝ)
    (hW : ∀ t : ℝ, {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ f ρ = 0}.Finite ∧
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ f ρ = 0}, (m ρ : ℝ) ≤ B t)
    {u T T' : ℝ} (hT : 2 ≤ T) (hu : T ≤ u) (hT1 : T ≤ T') (hT2 : T' ≤ T + 1) :
    ‖(∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ f ρ = 0},
        (m ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) -
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ f ρ = 0},
        (m ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ (B T + B (-T)) * (u / T) := by
  classical
  have hT0 : 0 < T := by linarith
  have hS' := finite_box f (fun t => (hW t).1) T'
  have hS := finite_box f (fun t => (hW t).1) T
  have hA := (hW T).1
  have hA' := (hW (-T)).1
  rw [finsum_mem_eq_finite_toFinset_sum _ hS', finsum_mem_eq_finite_toFinset_sum _ hS]
  have hsub : hS.toFinset ⊆ hS'.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    obtain ⟨a, b, c, d⟩ := hρ
    exact ⟨a, b, c.trans_le hT1, d⟩
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hD : ∀ ρ ∈ hS'.toFinset \ hS.toFinset,
      ρ ∈ hA.toFinset ∪ hA'.toFinset ∧ ρ.re < 1 ∧ T ≤ |ρ.im| := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hρ
    rw [Set.Finite.mem_toFinset] at h1 h2
    obtain ⟨a, b, c, d⟩ := h1
    have hT' : T ≤ |ρ.im| := not_lt.1 fun h => h2 ⟨a, b, h, d⟩
    refine ⟨?_, b, hT'⟩
    rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    rw [abs_lt] at c
    rcases le_or_gt 0 ρ.im with h | h
    · left
      rw [abs_of_nonneg h] at hT'
      refine ⟨a, b, ?_, d⟩
      rw [abs_le]
      constructor <;> linarith
    · right
      rw [abs_of_neg h] at hT'
      refine ⟨a, b, ?_, d⟩
      rw [abs_le]
      constructor <;> linarith
  have hm : ∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ) ≤ B T + B (-T) := by
    calc ∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ)
        ≤ ∑ ρ ∈ hA.toFinset ∪ hA'.toFinset, (m ρ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => (hD ρ hρ).1)
            (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ ∑ ρ ∈ hA.toFinset, (m ρ : ℝ) + ∑ ρ ∈ hA'.toFinset, (m ρ : ℝ) := by
          rw [← Finset.sum_union_inter]
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      _ ≤ B T + B (-T) := by
          rw [← finsum_mem_eq_finite_toFinset_sum _ hA, ← finsum_mem_eq_finite_toFinset_sum _ hA']
          exact add_le_add (hW T).2 (hW (-T)).2
  calc _ ≤ ∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ) * (u / T) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
        obtain ⟨-, h1, h2⟩ := hD ρ hρ
        exact norm_term_le (m ρ) hT hu h1 h2
    _ = (∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ)) * (u / T) := by rw [Finset.sum_mul]
    _ ≤ (B T + B (-T)) * (u / T) :=
        mul_le_mul_of_nonneg_right hm (div_nonneg (by linarith) hT0.le)
end GlobalTheory.ZeroBand
