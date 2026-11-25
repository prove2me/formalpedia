-- Prove2me | solution 1 for GlobalTheory.hhJ_nonneg_of_cloud_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:55:55.73711+00:00
-- url     : https://prove2.me/submissions/9de54b8f-0fd7-45fc-8c26-75efc07c15c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterFinBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WeightNearDiagonalOperatorsBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirOffDiagonalNormSqLeOfLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantHermitianFormNonnegOfCloudEigen
import Theorems.Thm_GlobalTheory_T_splitCasimir_offDiagonal_norm_sq_le_of_level
import Theorems.Thm_GlobalTheory_shape_position
import Theorems.Thm_GlobalTheory_wtNear_diag_bounds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → ∀ s : Fin n, s.val + 1 < kk → splitCas E x = ((-μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • x → 0 ≤ (hhJ ε x x).re := by
  intro M _ _ n ε E μ kk j bv x hM hS hj hL s hs hx
  obtain ⟨hb, hω, hζ⟩ := GlobalTheory.shape_position n kk j ε μ bv hS hj
  have hO := GlobalTheory.T.splitCasimir_offDiagonal_norm_sq_le_of_level M n ε E μ kk j bv x hM hS hj hL
  set ζ : ℝ := -μ s + (1 - (n : ℝ)) / 2 with hζdef
  have hζs : ζ ≤ bv / 32 := ((hζ s).1 hs).2
  have hnode : ∀ c : Fin n, kk ≤ c.val + 1 →
      (15 * bv / 16) ^ 2 * ‖x c‖ ^ 2 ≤ ‖∑ a ∈ univ.erase c, E c a (x a)‖ ^ 2 := by
    intro c hc
    have h1 := (GlobalTheory.wtNear_diag_bounds M n ε E (lowK ε μ) (j : ℝ) (x c) hM.2.1 (hL c).2).2.1 c (ζ : ℂ)
      (15 * bv / 16) (by positivity) (by
        intro ω hw
        have h2 := ((hω ω hw c).2 hc).1
        rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
        have := neg_abs_le (ζ + ω c)
        linarith)
    have h3 := congrFun hx c
    simp only [splitCas, Pi.smul_apply] at h3
    rw [← Finset.add_sum_erase univ (fun a => E c a (x a)) (mem_univ c)] at h3
    have h4 : (ζ : ℂ) • x c + E c c (x c) = -∑ a ∈ univ.erase c, E c a (x a) := by
      rw [← h3]; abel
    rw [h4, norm_neg] at h1
    exact h1
  have hterm : ∀ c : Fin n, (15 * bv / 16) ^ 2 * ‖x c‖ ^ 2 - 2 * ‖∑ a ∈ univ.erase c, E c a (x a)‖ ^ 2 ≤
      (15 * bv / 16) ^ 2 * ((if ε c then 1 else -1) * ⟪x c, x c⟫_ℂ : ℂ).re := by
    intro c
    have hin : (⟪x c, x c⟫_ℂ : ℂ).re = ‖x c‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (x c)
    by_cases he : ε c = true
    · rw [if_pos he, one_mul, hin]
      have := sq_nonneg ‖∑ a ∈ univ.erase c, E c a (x a)‖
      linarith
    · have hc : kk ≤ c.val + 1 := by
        by_contra h
        exact he (hS.2.2.2.1 c (not_le.mp h)).1
      rw [if_neg he, neg_one_mul, Complex.neg_re, hin]
      have := hnode c hc
      linarith
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ (univ : Finset (Fin n))) => hterm c)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Complex.re_sum] at hsum
  have hS0 : 0 ≤ ∑ c, ‖x c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hpos : 0 < (15 * bv / 16) ^ 2 := by positivity
  have hkey : 0 ≤ (15 * bv / 16) ^ 2 * (hhJ ε x x).re := by
    unfold hhJ
    have : 0 ≤ bv ^ 2 * ∑ c, ‖x c‖ ^ 2 := mul_nonneg (sq_nonneg _) hS0
    nlinarith
  exact (mul_nonneg_iff_of_pos_left hpos).mp hkey
end GlobalTheory
