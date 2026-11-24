-- Prove2me | solution 1 for GlobalTheory.gramDet_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:59:02.398576+00:00
-- url     : https://prove2.me/submissions/8340f5e7-08c6-4bf5-9543-c51b4ab05bca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : (∀ (r : ℕ) (a : Matrix (Fin r) (Fin r) ℂ), ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix (Fin r) ι ℂ), (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re)) → (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ η : ℝ, 0 < η ∧ ∀ (i : ℕ), 0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (((M)ᴴ * (M)).det.re) → η ≤ ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) → (∀ (N : ℕ) (ω η : ℝ), 1 ≤ ω → 0 < η → ∃ δ c : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ ∀ (σ : Type) (S : Finset σ) (t : σ → ℝ), S.card = N → (∀ s ∈ S, ω⁻¹ ≤ t s ∧ t s ≤ ω) → η ≤ ∑ s ∈ S, Real.log (t s) → ∑ s ∈ S, t s ^ (-δ) ≤ N * c) → (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ δ c ω : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ 1 ≤ ω ∧ ∀ (i : ℕ) (M : Matrix (Fin r) (Fin i) ℂ), 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re) ∧ (((M)ᴴ * (M)).det.re) ≤ ω * (((a * M)ᴴ * (a * M)).det.re)) ∧ (0 < i → i < r → ∑ a ∈ S, ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) ^ (-δ) ≤ S.card * c)) := by
  intro h1 h2 h3 r S hS hirr
  choose w hw1 hw using h1 r
  obtain ⟨η, hη, hη2⟩ := h2 r S hS hirr
  have hw0 : ∀ a, 0 ≤ w a := fun a => le_trans zero_le_one (hw1 a)
  have hΩ1 : (1:ℝ) ≤ 1 + ∑ a ∈ S, w a := by
    have := Finset.sum_nonneg (s := S) (fun a _ => hw0 a)
    linarith
  have hwΩ : ∀ a ∈ S, w a ≤ 1 + ∑ a ∈ S, w a := by
    intro a ha
    have := Finset.single_le_sum (s := S) (fun a _ => hw0 a) ha
    linarith
  generalize (1 + ∑ a ∈ S, w a) = Ω at hΩ1 hwΩ
  obtain ⟨δ, c, hδ, hc0, hc1, hc⟩ := h3 S.card Ω η hΩ1 hη
  refine ⟨δ, c, Ω, hδ, hc0, hc1, hΩ1, ?_⟩
  intro i M hM
  have hΩ0 : 0 < Ω := lt_of_lt_of_le one_pos hΩ1
  have key : ∀ a ∈ S, (((a * M)ᴴ * (a * M)).det.re) ≤ Ω * (((M)ᴴ * (M)).det.re) ∧
      (((M)ᴴ * (M)).det.re) ≤ Ω * (((a * M)ᴴ * (a * M)).det.re) := by
    intro a ha
    obtain ⟨-, hdet, hinv⟩ := hS a ha
    refine ⟨(hw a (Fin i) M).trans (mul_le_mul_of_nonneg_right (hwΩ a ha) hM.le), ?_⟩
    have h := hw a⁻¹ (Fin i) (a * M)
    have e : a⁻¹ * (a * M) = M := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul a (isUnit_iff_ne_zero.mpr hdet),
        Matrix.one_mul]
    rw [e] at h
    have hpos : 0 < (((a * M)ᴴ * (a * M)).det.re) := by
      by_contra hn
      have := mul_nonpos_of_nonneg_of_nonpos (hw0 a⁻¹) (not_lt.mp hn)
      linarith
    exact h.trans (mul_le_mul_of_nonneg_right (hwΩ _ hinv) hpos.le)
  refine ⟨key, fun hi hir => ?_⟩
  refine hc _ S (fun a => (((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) rfl ?_
    (hη2 i hi hir M hM)
  intro a ha
  obtain ⟨k1, k2⟩ := key a ha
  refine ⟨?_, (div_le_iff₀ hM).mpr k1⟩
  rw [le_div_iff₀ hM, inv_mul_le_iff₀ hΩ0]
  exact k2
end GlobalTheory
