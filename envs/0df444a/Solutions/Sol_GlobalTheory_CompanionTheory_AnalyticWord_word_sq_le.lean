-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.word_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:48:22.981135+00:00
-- url     : https://prove2.me/submissions/dd7abf47-da00-4590-a734-401b401bd602

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_nil
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_cons
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_bnd_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_le_bnd
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_comb_le
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_sum_sq_le
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_comm_word
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_row_le_tot

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
    (hSy : ∀ b, S (y b) = ∑ e, d b e • y e) (hOy : ∀ b, Ω (y b) = ∑ e, o b e • y e)
    (l : List ι) (i : ι) (e : Fin m) :
    ‖j (word Z (i :: l) (y e))‖ ^ 2 ≤ bnd j Z y l.length *
      ((tot o + 2 * tot d) * bnd j Z y l.length +
        2 * l.length * c0 K c * bnd j Z y (l.length + 1)) := by
  have hB0 := GlobalTheory.CompanionTheory.AnalyticWord.bnd_nonneg j Z y l.length
  have hv : ‖j (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e))‖ ≤ GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y l.length :=
    GlobalTheory.CompanionTheory.AnalyticWord.le_bnd j Z y (l := l) rfl e
  have hOmega : ‖j (Ω (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e)))‖ ≤
      GlobalTheory.CompanionTheory.AnalyticWord.tot o * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y l.length := by
    have h : Ω (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e)) = GlobalTheory.CompanionTheory.AnalyticWord.word Z l (∑ f, o e f • y f) := by
      rw [← hOy e]
      exact LinearMap.congr_fun (GlobalTheory.CompanionTheory.AnalyticWord.word_comm Z Ω hΩ l) (y e)
    rw [h]
    exact (GlobalTheory.CompanionTheory.AnalyticWord.comb_le j Z y (l := l) rfl (o e)).trans
      (mul_le_mul_of_nonneg_right (GlobalTheory.CompanionTheory.AnalyticWord.row_le_tot o e) hB0)
  have hSv : ‖j (S (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e)))‖ ≤
      GlobalTheory.CompanionTheory.AnalyticWord.tot d * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y l.length +
        l.length * GlobalTheory.CompanionTheory.AnalyticWord.c0 K c * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (l.length + 1) := by
    have hdec : S (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e)) = GlobalTheory.CompanionTheory.AnalyticWord.word Z l (∑ f, d e f • y f) +
        GlobalTheory.CompanionTheory.AnalyticWord.word Z [] ((S * GlobalTheory.CompanionTheory.AnalyticWord.word Z l - GlobalTheory.CompanionTheory.AnalyticWord.word Z l * S) (y e)) := by
      rw [GlobalTheory.CompanionTheory.AnalyticWord.word_nil, Module.End.one_apply, LinearMap.sub_apply, Module.End.mul_apply,
        Module.End.mul_apply, ← hSy e]
      abel
    have hc := GlobalTheory.CompanionTheory.AnalyticWord.comm_word j Z y S K c hS l [] e
    rw [List.length_nil, zero_add] at hc
    rw [hdec, map_add]
    exact (norm_add_le _ _).trans (add_le_add
      ((GlobalTheory.CompanionTheory.AnalyticWord.comb_le j Z y (l := l) rfl (d e)).trans
        (mul_le_mul_of_nonneg_right (GlobalTheory.CompanionTheory.AnalyticWord.row_le_tot d e) hB0)) hc)
  have hmain := GlobalTheory.CompanionTheory.AnalyticWord.sum_sq_le j Z hskew S Ω hT
    (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e)) i
  rw [GlobalTheory.CompanionTheory.AnalyticWord.word_cons, Module.End.mul_apply]
  have hnn : 0 ≤ ‖j (Ω (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e)))‖ + 2 * ‖j (S (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e)))‖ := by
    positivity
  refine hmain.trans ((mul_le_mul hv (add_le_add hOmega (mul_le_mul_of_nonneg_left hSv zero_le_two))
    hnn hB0).trans (le_of_eq ?_))
  ring
end GlobalTheory.CompanionTheory.AnalyticWord
