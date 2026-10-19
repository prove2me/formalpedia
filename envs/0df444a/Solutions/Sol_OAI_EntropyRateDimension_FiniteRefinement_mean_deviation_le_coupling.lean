-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteRefinement.mean_deviation_le_coupling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:47:43.141303+00:00
-- url     : https://prove2.me/submissions/d36657ab-8899-4f20-aeef-d52b3c9803d8

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteRefinement
universe uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory
open FiniteEntropy
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]


theorem solution (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 < p a) :
    (∑ a, p a * |v a-cellMean p v g (g a)|) ≤
      ∑ a, ∑ b, (if g a = g b then p a*p b/mass Finset.univ p g (g a) else 0) *
        |v a-v b| := by
  classical
  refine Finset.sum_le_sum fun a _ => ?_
  set M := mass Finset.univ p g (g a) with hMdef
  have hM : 0 < M := Finset.sum_pos (fun b _ => hp b)
    ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, rfl⟩⟩
  have h1 : ∑ b, (if g b = g a then p b else 0) / M = 1 := by
    rw [← Finset.sum_div, ← Finset.sum_filter, div_eq_one_iff_eq hM.ne']
    rfl
  have e : v a - cellMean p v g (g a) =
      ∑ b, ((if g b = g a then p b else 0) / M) * (v a - v b) := by
    unfold cellMean
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
    rfl
  rw [e]
  have h2 : |∑ b, ((if g b = g a then p b else 0) / M) * (v a - v b)| ≤
      ∑ b, ((if g b = g a then p b else 0) / M) * |v a - v b| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
    rw [abs_mul, abs_of_nonneg]
    apply div_nonneg _ hM.le
    split_ifs
    · exact (hp b).le
    · exact le_rfl
  refine (mul_le_mul_of_nonneg_left h2 (hp a).le).trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : g a = g b
  · rw [if_pos hab.symm, if_pos hab]; ring
  · rw [if_neg (Ne.symm hab), if_neg hab]; simp

