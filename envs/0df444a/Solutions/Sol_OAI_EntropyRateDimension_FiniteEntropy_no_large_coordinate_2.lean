-- Prove2me | solution 2 for OAI.EntropyRateDimension.FiniteEntropy.no_large_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:38:25.254882+00:00
-- url     : https://prove2.me/submissions/893f9920-2839-403f-bd30-ee98023ca8a7

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean:L612-L645
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteEntropy.no_large_coordinate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

theorem no_large_coordinate {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) {a : ℝ} (ha : 0 < a)
    (hE : ¬∃ i j, i ≠ j ∧ a / (4 * Fintype.card ι) ≤ |x i| ∧
      a / (4 * Fintype.card ι) ≤ |x j|)
    (hB : |∑ i, x i| < a / 2) (i : ι) : |x i| < a := by
  by_contra hn
  have hi : a ≤ |x i| := le_of_not_gt hn
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  have hka : a / (4 * Fintype.card ι) ≤ a := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Fintype.card ι)).mpr
    have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
    nlinarith
  have hsmall : ∀ j ∈ Finset.univ.erase i, |x j| < a / (4 * Fintype.card ι) := by
    intro j hj
    by_contra hn
    exact hE ⟨i,j,Ne.symm (Finset.mem_erase.mp hj).1,hka.trans hi,le_of_not_gt hn⟩
  have habs : |∑ j ∈ Finset.univ.erase i, x j| ≤ a / 4 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      (∑ j ∈ Finset.univ.erase i, |x j|) ≤
          ∑ _j ∈ Finset.univ.erase i, a / (4 * Fintype.card ι) :=
        Finset.sum_le_sum (fun j hj => (hsmall j hj).le)
      _ ≤ ∑ _j : ι, a / (4 * Fintype.card ι) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => by positivity)
      _ = a / 4 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
  have hiabs : |x i| ≤ |∑ j, x j| + |∑ j ∈ Finset.univ.erase i, x j| := by
    have he := Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)
    have hx : x i = (∑ j, x j) - ∑ j ∈ Finset.univ.erase i, x j := by linarith
    rw [hx]
    exact abs_sub _ _
  linarith

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.FiniteEntropy.no_large_coordinate.{uι} := @_root_.OAI.EntropyRateDimension.FiniteEntropy.no_large_coordinate.{uι}
