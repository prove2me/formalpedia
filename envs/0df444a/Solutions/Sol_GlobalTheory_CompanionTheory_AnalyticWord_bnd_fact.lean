-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.bnd_fact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:20:13.114323+00:00
-- url     : https://prove2.me/submissions/e81c9ba2-323c-4d08-b27d-4db11a0e8cc2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_bnd_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_weightConst_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_bnd_succ_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticWord
variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type}
variable [Fintype ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V) {m : ℕ} (y : Fin m → V)
  (S Ω : Module.End ℂ V) (K : Finset ι) (c : ι → ι → ι → ℂ) (d o : Fin m → Fin m → ℂ)
namespace GlobalTheory.CompanionTheory.AnalyticWord
theorem _root_.solution
    (hskew : ∀ i v w, inner ℂ (j (Z i v)) (j w) = - inner ℂ (j v) (j (Z i w)))
    (hT : ∑ i, Z i * Z i = Ω + S + S)
    (hS : ∀ i, S * Z i - Z i * S = ∑ κ ∈ K, ∑ n, c κ i n • (Z κ * Z n + Z n * Z κ))
    (hΩ : ∀ i, Ω * Z i = Z i * Ω)
    (hSy : ∀ b, S (y b) = ∑ e, d b e • y e) (hOy : ∀ b, Ω (y b) = ∑ e, o b e • y e) (k : ℕ) :
    bnd j Z y k ≤ (√(tot o + 2 * tot d) + 2 * c0 K c + 1) ^ k * (k.factorial : ℝ) *
      bnd j Z y 0 := by
  have step : ∀ a s b0 bk b1 P F r : ℝ, 0 ≤ a → 0 ≤ s → 0 ≤ b0 → 0 ≤ P → 0 ≤ F → 0 ≤ r →
      b1 ≤ (a + 2 * r * s) * bk → bk ≤ P * F * b0 →
      b1 ≤ P * (a + 2 * s + 1) * ((r + 1) * F) * b0 := by
    intro a s b0 bk b1 P F r ha hs hb0 hP hF hr h1 h2
    have hX : 0 ≤ P * F * b0 := mul_nonneg (mul_nonneg hP hF) hb0
    have hc : 0 ≤ a + 2 * r * s := add_nonneg ha (mul_nonneg (mul_nonneg zero_le_two hr) hs)
    calc b1 ≤ (a + 2 * r * s) * bk := h1
      _ ≤ (a + 2 * r * s) * (P * F * b0) := mul_le_mul_of_nonneg_left h2 hc
      _ ≤ ((a + 2 * s + 1) * (r + 1)) * (P * F * b0) :=
          mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg ha hr]) hX
      _ = P * (a + 2 * s + 1) * ((r + 1) * F) * b0 := by ring
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := GlobalTheory.CompanionTheory.AnalyticWord.bnd_succ_le j Z y S Ω K c d o hskew hT hS hΩ hSy hOy k
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    exact step _ _ _ _ _ _ _ _ (Real.sqrt_nonneg _) (GlobalTheory.CompanionTheory.AnalyticWord.weightConst_nonneg K c)
      (GlobalTheory.CompanionTheory.AnalyticWord.bnd_nonneg j Z y 0)
      (pow_nonneg (add_nonneg (add_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg zero_le_two (GlobalTheory.CompanionTheory.AnalyticWord.weightConst_nonneg K c))) zero_le_one) k)
      (Nat.cast_nonneg _) (Nat.cast_nonneg k) hs ih
end GlobalTheory.CompanionTheory.AnalyticWord
