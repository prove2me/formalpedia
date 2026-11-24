-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.bnd_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:03:17.681398+00:00
-- url     : https://prove2.me/submissions/5f3a0ef3-83a0-473b-b342-1400451d7bbf

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_bnd_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_bnd_le
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_quad_step
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_weightConst_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_tot_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_sq_le

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
    (hSy : ∀ b, S (y b) = ∑ e, d b e • y e) (hOy : ∀ b, Ω (y b) = ∑ e, o b e • y e) (n : ℕ) :
    bnd j Z y (n + 1) ≤ (√(tot o + 2 * tot d) + 2 * n * c0 K c) * bnd j Z y n := by
  have hA : 0 ≤ GlobalTheory.CompanionTheory.AnalyticWord.tot o + 2 * GlobalTheory.CompanionTheory.AnalyticWord.tot d :=
    add_nonneg (GlobalTheory.CompanionTheory.AnalyticWord.tot_nonneg o) (mul_nonneg zero_le_two (GlobalTheory.CompanionTheory.AnalyticWord.tot_nonneg d))
  have hC : 0 ≤ 2 * (n : ℝ) * GlobalTheory.CompanionTheory.AnalyticWord.c0 K c :=
    mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg n)) (GlobalTheory.CompanionTheory.AnalyticWord.weightConst_nonneg K c)
  have hBn := GlobalTheory.CompanionTheory.AnalyticWord.bnd_nonneg j Z y n
  have hBn1 := GlobalTheory.CompanionTheory.AnalyticWord.bnd_nonneg j Z y (n + 1)
  have hR0 : 0 ≤ GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y n *
      ((GlobalTheory.CompanionTheory.AnalyticWord.tot o + 2 * GlobalTheory.CompanionTheory.AnalyticWord.tot d) * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y n +
        2 * n * GlobalTheory.CompanionTheory.AnalyticWord.c0 K c * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (n + 1)) :=
    mul_nonneg hBn (add_nonneg (mul_nonneg hA hBn) (mul_nonneg hC hBn1))
  have hbound : GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (n + 1) ≤ √(GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y n *
      ((GlobalTheory.CompanionTheory.AnalyticWord.tot o + 2 * GlobalTheory.CompanionTheory.AnalyticWord.tot d) * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y n +
        2 * n * GlobalTheory.CompanionTheory.AnalyticWord.c0 K c * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (n + 1))) := by
    refine GlobalTheory.CompanionTheory.AnalyticWord.bnd_le j Z y (Real.sqrt_nonneg _) fun l e hl => ?_
    cases l with
    | nil => simp at hl
    | cons i l' =>
      have hl' : l'.length = n := by simpa using hl
      have h := GlobalTheory.CompanionTheory.AnalyticWord.word_sq_le j Z y S Ω K c d o hskew hT hS hΩ hSy hOy l' i e
      rw [hl'] at h
      exact (le_abs_self _).trans (Real.abs_le_sqrt h)
  have hsq : GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (n + 1) ^ 2 ≤ GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y n *
      ((GlobalTheory.CompanionTheory.AnalyticWord.tot o + 2 * GlobalTheory.CompanionTheory.AnalyticWord.tot d) * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y n +
        2 * n * GlobalTheory.CompanionTheory.AnalyticWord.c0 K c * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (n + 1)) :=
    (pow_le_pow_left₀ hBn1 hbound 2).trans_eq (Real.sq_sqrt hR0)
  exact GlobalTheory.CompanionTheory.AnalyticWord.quad_step hBn1 hBn hA hC hsq
end GlobalTheory.CompanionTheory.AnalyticWord
