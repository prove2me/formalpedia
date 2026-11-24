-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.comm_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:19.697976+00:00
-- url     : https://prove2.me/submissions/d9f76a92-a0d8-416a-9ec1-e15068283ec8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_cons
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_append
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_bnd_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_le_bnd

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
    (hS : ∀ i, S * Z i - Z i * S = ∑ κ ∈ K, ∑ n, c κ i n • (Z κ * Z n + Z n * Z κ))
    (p l : List ι) (i : ι) (e : Fin m) :
    ‖j (word Z p ((S * Z i - Z i * S) (word Z l (y e))))‖ ≤
      c0 K c * bnd j Z y (p.length + l.length + 2) := by
  have hw : ∀ a b : ι, ‖j (GlobalTheory.CompanionTheory.AnalyticWord.word Z p ((Z a * Z b) (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e))))‖ ≤
      GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (p.length + l.length + 2) := by
    intro a b
    have h := GlobalTheory.CompanionTheory.AnalyticWord.le_bnd j Z y (l := p ++ a :: b :: l)
      (k := p.length + l.length + 2)
      (by simp only [List.length_append, List.length_cons]; omega) e
    simpa only [GlobalTheory.CompanionTheory.AnalyticWord.word_append, GlobalTheory.CompanionTheory.AnalyticWord.word_cons, Module.End.mul_apply] using h
  have hB0 := GlobalTheory.CompanionTheory.AnalyticWord.bnd_nonneg j Z y (p.length + l.length + 2)
  rw [hS i]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, map_sum, map_smul, map_add]
  calc _ ≤ ∑ κ ∈ K, ∑ n, ‖c κ i n‖ * (2 * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (p.length + l.length + 2)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_))
        rw [norm_smul, two_mul]
        exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hw κ n) (hw n κ)))
          (norm_nonneg _)
    _ = (∑ κ ∈ K, ∑ n, ‖c κ i n‖) * (2 * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (p.length + l.length + 2)) := by
        simp only [Finset.sum_mul]
    _ ≤ (∑ i', ∑ κ ∈ K, ∑ n, ‖c κ i' n‖) *
          (2 * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (p.length + l.length + 2)) :=
        mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := fun i' => ∑ κ ∈ K, ∑ n, ‖c κ i' n‖)
            (fun i' _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (Finset.mem_univ i))
          (mul_nonneg zero_le_two hB0)
    _ = GlobalTheory.CompanionTheory.AnalyticWord.c0 K c * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (p.length + l.length + 2) := by
        unfold GlobalTheory.CompanionTheory.AnalyticWord.c0
        ring
end GlobalTheory.CompanionTheory.AnalyticWord
