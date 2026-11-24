-- Prove2me | solution 1 for GlobalTheory.lift_hasSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:44.6245+00:00
-- url     : https://prove2.me/submissions/5fee86a5-6000-4d4d-918b-9f5076232774

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LiftHasSumZeroOfSurjectiveModPrime
import Theorems.Thm_GlobalTheory_padicComplex_norm_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (X ι : Type) (η : X → ι → ℂ_[l]) (τ : ι → ℝ) (S : Set X), (∀ t : ι → ℂ_[l], (∀ i, ‖t i‖ ≤ τ i) → ∃ y ∈ S, ∀ i, ‖η y i - t i‖ ≤ ‖(l : ℂ_[l])‖ * τ i) → ∀ x ∈ S, (∀ i, ‖η x i‖ ≤ ‖(l : ℂ_[l])‖ * τ i) → ∃ y : ℕ → X, y 0 = x ∧ (∀ k, y k ∈ S) ∧ ∀ i, HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (y k) i) 0 := by
  intro l _ X ι η τ S hS x hx hxb
  have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := padicComplex_norm_prime l
  have hp : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := by rw [hl]; positivity
  have hllt : ‖(l : ℂ_[l])‖ < 1 := by rw [hl]; exact inv_lt_one_of_one_lt₀ hp
  have hl0 : (l : ℂ_[l]) ≠ 0 := norm_pos_iff.mp hlpos
  let T := {t : ι → ℂ_[l] // ∀ i, ‖t i‖ ≤ τ i}
  have hg : ∀ t : T, ∃ y ∈ S, ∀ i, ‖η y i + t.1 i‖ ≤ ‖(l : ℂ_[l])‖ * τ i := by
    intro t
    obtain ⟨y, hyS, hy⟩ := hS (-t.1) (fun i => by simpa using t.2 i)
    exact ⟨y, hyS, fun i => by simpa [sub_eq_add_neg] using hy i⟩
  choose g hgS hgb using hg
  have hdiv : ∀ z : ℂ_[l], ∀ i, ‖z‖ ≤ ‖(l : ℂ_[l])‖ * τ i → ‖z / l‖ ≤ τ i := by
    intro z i hz
    rw [norm_div, div_le_iff₀ hlpos]; linarith [mul_comm (‖(l : ℂ_[l])‖) (τ i)]
  let step : T → T := fun t => ⟨fun i => (t.1 i + η (g t) i) / l,
    fun i => hdiv _ i (by rw [add_comm]; exact hgb t i)⟩
  let t0 : T := ⟨fun i => η x i / l, fun i => hdiv _ i (hxb i)⟩
  let ts : ℕ → T := fun k => step^[k] t0
  let y : ℕ → X := fun k => Nat.casesOn k x (fun k => g (ts k))
  have hy0 : y 0 = x := rfl
  have hysucc : ∀ k, y (k+1) = g (ts k) := fun k => rfl
  have htsucc : ∀ k, ts (k+1) = step (ts k) := fun k => Function.iterate_succ_apply' step k t0
  refine ⟨y, hy0, ?_, ?_⟩
  · intro k; cases k with
    | zero => exact hx
    | succ k => exact hgS _
  intro i

  have hinv : ∀ k, ∑ m ∈ Finset.range (k+1), (l : ℂ_[l]) ^ m * η (y m) i = (l : ℂ_[l]) ^ (k+1) * (ts k).1 i := by
    intro k
    induction k with
    | zero => simp [hy0, ts, t0]; field_simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, hysucc, htsucc]
      simp only [step]
      field_simp
      ring

  have hτ : ∀ k, 0 ≤ τ i := fun k => le_trans (norm_nonneg _) ((ts k).2 i)
  have hbd : ∀ k, ‖η (y k) i‖ ≤ τ i := by
    intro k; cases k with
    | zero => exact le_trans (hxb i) (by nlinarith [hτ 0])
    | succ k =>
      rw [hysucc]
      have h1 := hgb (ts k) i
      have h2 := (ts k).2 i
      have : η (g (ts k)) i = (η (g (ts k)) i + (ts k).1 i) - (ts k).1 i := by ring
      rw [this]
      rw [sub_eq_add_neg]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ (by rw [norm_neg]; exact h2))
      exact le_trans h1 (by nlinarith [hτ 0])
  have hterm : ∀ k, ‖(l : ℂ_[l]) ^ k * η (y k) i‖ ≤ τ i * ‖(l : ℂ_[l])‖ ^ k := by
    intro k; rw [norm_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbd k) (pow_nonneg (norm_nonneg _) _)
  have hsum : Summable (fun k : ℕ => (l : ℂ_[l]) ^ k * η (y k) i) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg _) hllt).mul_left (τ i)) hterm
  rw [hsum.hasSum_iff_tendsto_nat]
  have hlim : Filter.Tendsto (fun k : ℕ => (l : ℂ_[l]) ^ (k+1) * (ts k).1 i) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) (g := fun k : ℕ => ‖(l : ℂ_[l])‖ ^ (k+1) * τ i) ?_
    · rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left ((ts k).2 i) (pow_nonneg (norm_nonneg _) _)
    · have := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hllt).comp (Filter.tendsto_add_atTop_nat 1)
      simpa using this.mul_const (τ i)
  have hlim2 : Filter.Tendsto (fun k : ℕ => ∑ m ∈ Finset.range (k+1), (l : ℂ_[l]) ^ m * η (y m) i) Filter.atTop (nhds 0) := by
    simpa only [hinv] using hlim
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp hlim2
end GlobalTheory
