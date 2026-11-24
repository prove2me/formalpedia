-- Prove2me | solution 1 for GlobalTheory.NearlyPrimitive.norm_smul_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:53:01.220855+00:00
-- url     : https://prove2.me/submissions/e14737b4-f9e0-4e51-a1ae-dc65cbf5ee15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormSmulLeOneOfPrimitiveBoundedPowers
import Theorems.Thm_GlobalTheory_NearlyPrimitive_norm_smul_le_one_of_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NearlyPrimitive
open Finset Filter Topology
namespace GlobalTheory.NearlyPrimitive
theorem _root_.solution : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (B₁ B₂ : Type) [CommRing B₁] [Algebra C B₁] [CommRing B₂] [Algebra C B₂] (N₁ : B₁ → ℝ) (N₂ : B₂ → ℝ) (Δ i j : B₁ →ₐ[C] B₂), (∀ (c : C) x, N₁ (c • x) = ‖c‖ * N₁ x) → (∀ (c : C) x, N₂ (c • x) = ‖c‖ * N₂ x) → (∀ x, 0 ≤ N₁ x) → (∀ x, 0 ≤ N₂ x) → (∀ x y, N₂ (x + y) ≤ max (N₂ x) (N₂ y)) → (∀ x y, N₂ (x * y) ≤ N₂ x * N₂ y) → (∀ x, N₂ (Δ x) ≤ N₁ x) → (∀ x y, N₂ (i x * j y) = N₁ x * N₁ y) → ∀ y : B₁, (∃ K : ℝ, ∀ k : ℕ, N₁ (y ^ k) ≤ K) → N₂ (Δ y - i y - j y) ≤ 1 → ∀ a : C, ‖a‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → N₁ (a • y) ≤ 1 := by
  intro C _ _ _ _ p hp hpn B₁ B₂ _ _ _ _ N₁ N₂ Δ i j hs₁ hs₂ hn₁ hn₂ hadd hmul hΔ hij y ⟨K, hK⟩
    he a ha
  by_contra hcon
  push Not at hcon
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (p : ℝ) hcon
  have hn0 : n ≠ 0 := by rintro rfl; rw [pow_zero] at hn; linarith
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (p : C) (Nat.pos_of_ne_zero hn0)
  have hbn : ‖b‖ ^ n = (p : ℝ)⁻¹ := by rw [← norm_pow, hb, hpn]
  have hb1 : ‖b‖ < 1 := by
    rw [← pow_lt_one_iff_of_nonneg (norm_nonneg b) hn0, hbn]
    exact inv_lt_one_of_one_lt₀ hp1
  have hpos : 0 < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := Real.rpow_pos_of_pos (by linarith) _
  have hc : ‖b * a‖ < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left ha (norm_nonneg b)).trans_lt
      (mul_lt_of_lt_one_left hpos hb1)
  have h := norm_smul_le_one_of_lt C p hpn B₁ B₂ N₁ N₂ Δ i j hs₁ hs₂ hn₁ hn₂ hadd hmul hΔ hij y K
    hK he (b * a) hc
  rw [mul_smul, hs₁] at h
  have h2 := pow_le_one₀ (n := n) (mul_nonneg (norm_nonneg b) (hn₁ _)) h
  rw [mul_pow, hbn, inv_mul_le_iff₀ (by linarith), mul_one] at h2
  linarith
end GlobalTheory.NearlyPrimitive
