-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpLower.lower_from_counts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:05:18.994633+00:00
-- url     : https://prove2.me/submissions/e4af31ad-9141-4f4f-a3d3-eb3bdd079af1

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanes
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpLower_re_sesq_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpLower_card_filter_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpLower_row_identity
import Theorems.Thm_GlobalTheory_CompanionTheory_GapOpLower_sum_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpLower
open Finset
namespace GlobalTheory.CompanionTheory.GapOpLower
theorem _root_.solution : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
  (w : (Fin (n + 1) → k) → V) (c A : ℝ),
  (∀ x, 0 ≤ (B x x).re) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 →
    Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1)) →
  (∀ a b : Fin (n + 1) → k, a ≠ 0 → (∀ s : k, b ≠ s • a) →
    Fintype.card k ^ 2 * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1)) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 → ∀ s : k, s ≠ 0 → w (s • a) = w a) →
  (∀ a : Fin (n + 1) → k, a ≠ 0 → (B (w a) (w a)).re = c) →
  (∀ x : Fin (n + 1) → k, x ≠ 0 →
    (B (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), w a)
       (∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), w a)).re = A) →
  (Fintype.card k : ℝ) ^ n * c ≤ (Fintype.card k : ℝ) * A := by
  intro k _ _ n V _ _ B w c A hpos h1 h2 hw hc hA
  have hq1 : (1 : ℝ) < (Fintype.card k : ℝ) := by exact_mod_cast Fintype.one_lt_card
  set q : ℝ := (Fintype.card k : ℝ) with hq
  have hq0 : q ≠ 0 := by linarith
  let N : (Fin (n + 1) → k) → (Fin (n + 1) → k) → ℝ := fun a b =>
    ((univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card : ℝ)
  let R : (Fin (n + 1) → k) → (Fin (n + 1) → k) → ℝ := fun a b => (B (w a) (w b)).re
  let Z : Finset (Fin (n + 1) → k) := univ.filter (fun b => b ≠ 0)
  have hZc : (Z.card : ℝ) = q ^ (n + 1) - 1 := by
    have h := card_filter_ne_zero (α := Fin (n + 1) → k)
    have hc' : (Fintype.card (Fin (n + 1) → k) : ℝ) = q ^ (n + 1) := by simp [hq]
    rw [hc'] at h
    rw [← h]
    simp only [Z]
    congr!
  have hrow : ∀ a, a ≠ 0 → q * ∑ b, N a b * R a b
      = q ^ n * ∑ b ∈ Z, R a b + q ^ n * c := by
    intro a ha
    refine row_identity a ha (N a) (R a) c ?_ ?_ ?_ ?_ ?_
    · simp [N]
    · have h := h1 a ha
      have : N a a = ((univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card : ℝ) := by
        simp only [N, and_self]
      rw [this]
      exact_mod_cast h
    · intro s hs
      have : univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ (s • a) ⬝ᵥ x = 1) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr ?_
        rintro x - ⟨hx, hx'⟩
        rw [smul_dotProduct, hx] at hx'
        exact hs (by simpa using hx')
      simp only [N, this, card_empty, Nat.cast_zero]
    · intro b hb
      have h := h2 a b ha hb
      have h' : q ^ 2 * N a b = q ^ (n + 1) := by
        simp only [N]; rw [hq]; exact_mod_cast h
      apply mul_left_cancel₀ hq0
      rw [← mul_assoc, ← pow_two, h', pow_succ]; ring
    · intro s hs
      simp only [R, hw a ha s hs, hc a ha]

  have hleft : ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
      = (q ^ (n + 1) - 1) * A := by
    have hZ : ∑ x ∈ Z, ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b
        = ∑ x : Fin (n + 1) → k,
      ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b := by
      refine Finset.sum_subset (filter_subset _ _) ?_
      intro x _ hx
      have hx0 : x = 0 := by simpa [Z] using hx
      subst hx0
      simp
    rw [← hZ]
    have hconst : ∀ x ∈ Z, ∑ a ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1),
        ∑ b ∈ univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ x = 1), R a b = A := by
      intro x hx
      have hx0 : x ≠ 0 := by simpa [Z] using hx
      rw [← hA x hx0, re_sesq_sum]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hZc]

  have hright : q * ∑ a, ∑ b, N a b * R a b
      = q ^ n * ∑ a ∈ Z, ∑ b ∈ Z, R a b + (q ^ (n + 1) - 1) * (q ^ n * c) := by
    have hZ : ∑ a ∈ Z, ∑ b, N a b * R a b = ∑ a, ∑ b, N a b * R a b := by
      refine Finset.sum_subset (filter_subset _ _) ?_
      intro a _ ha
      have ha0 : a = 0 := by simpa [Z] using ha
      subst ha0
      simp [N]
    rw [← hZ, Finset.mul_sum, Finset.sum_congr rfl (fun a ha => hrow a (by simpa [Z] using ha)),
      Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hZc]
  have hP : 0 ≤ ∑ a ∈ Z, ∑ b ∈ Z, R a b := by
    have := hpos (∑ a ∈ Z, w a)
    rwa [re_sesq_sum] at this
  have hmain : q * ((q ^ (n + 1) - 1) * A)
      = q ^ n * ∑ a ∈ Z, ∑ b ∈ Z, R a b + (q ^ (n + 1) - 1) * (q ^ n * c) := by
    rw [← hleft, sum_expand R]
    exact hright
  have hQ : 0 < q ^ (n + 1) - 1 := by
    have : 1 < q ^ (n + 1) := one_lt_pow₀ hq1 (Nat.succ_ne_zero n)
    linarith
  have hqn : 0 ≤ q ^ n := by positivity
  have hfin : 0 ≤ (q ^ (n + 1) - 1) * (q * A - q ^ n * c) := by
    have : (q ^ (n + 1) - 1) * (q * A - q ^ n * c) = q ^ n * ∑ a ∈ Z, ∑ b ∈ Z, R a b := by
      linear_combination hmain
    rw [this]
    exact mul_nonneg hqn hP
  have := nonneg_of_mul_nonneg_right hfin hQ
  linarith
end GlobalTheory.CompanionTheory.GapOpLower
