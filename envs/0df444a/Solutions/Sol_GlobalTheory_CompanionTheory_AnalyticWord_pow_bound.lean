-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.pow_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:20.667491+00:00
-- url     : https://prove2.me/submissions/e5a144ad-f1cf-47c4-acda-c6163b7cd139

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_nil
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_cons
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_append
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
theorem _root_.solution (x : ι → ℂ) (k : ℕ) : ∀ (p : List ι) (e : Fin m),
    ‖j (word Z p (((∑ i, x i • Z i) ^ k) (y e)))‖ ≤
      (∑ i, ‖x i‖) ^ k * bnd j Z y (p.length + k) := by
  induction k with
  | zero =>
    intro p e
    simp only [pow_zero, Module.End.one_apply, one_mul]
    exact GlobalTheory.CompanionTheory.AnalyticWord.le_bnd j Z y (l := p) rfl e
  | succ k ih =>
    intro p e
    have hexp : GlobalTheory.CompanionTheory.AnalyticWord.word Z p (((∑ i, x i • Z i) ^ (k + 1)) (y e)) =
        ∑ i, x i • GlobalTheory.CompanionTheory.AnalyticWord.word Z (p ++ [i]) (((∑ i, x i • Z i) ^ k) (y e)) := by
      rw [pow_succ', Module.End.mul_apply, LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.smul_apply, map_smul, GlobalTheory.CompanionTheory.AnalyticWord.word_append, GlobalTheory.CompanionTheory.AnalyticWord.word_cons, GlobalTheory.CompanionTheory.AnalyticWord.word_nil,
        mul_one, Module.End.mul_apply]
    rw [hexp, map_sum]
    refine (norm_sum_le _ _).trans ?_
    rw [pow_succ', mul_assoc, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_smul, norm_smul]
    have h := ih (p ++ [i]) e
    have hlen : (p ++ [i]).length + k = p.length + (k + 1) := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [hlen] at h
    exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
end GlobalTheory.CompanionTheory.AnalyticWord
