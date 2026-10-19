-- Prove2me | solution 2 for OAI.EntropyRateDimension.FiniteRefinement.mean_deviation_le_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:48:37.703355+00:00
-- url     : https://prove2.me/submissions/c1c3b22e-9f81-4e34-bb04-13251889e4c0

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteRefinement.lean:L170-L204
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteRefinement.mean_deviation_le_coupling. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteRefinement ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteRefinement

open FiniteEntropy

variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

omit [Fintype α] in
theorem mass_pos {γ : Type uγ} [DecidableEq γ] (s : Finset α) (p : α → ℝ)
    (g : α → γ) (hp : ∀ a ∈ s, 0 < p a) {b : γ} (hb : b ∈ s.image g) :
    0 < mass s p g b := by
  classical
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  exact (hp a ha).trans_le (Finset.single_le_sum
    (fun x hx => (hp x (Finset.mem_filter.mp hx).1).le) (by simp [ha]))

theorem mean_deviation_le_coupling (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 < p a) :
    (∑ a, p a * |v a-cellMean p v g (g a)|) ≤
      ∑ a, ∑ b, (if g a = g b then p a*p b/mass Finset.univ p g (g a) else 0) *
        |v a-v b| := by
  classical
  apply Finset.sum_le_sum
  intro a _
  have hP : 0 < mass Finset.univ p g (g a) :=
    mass_pos Finset.univ p g (fun x _ => hp x) (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
  let q : α → ℝ := fun b => (if g b = g a then p b else 0)/mass Finset.univ p g (g a)
  have hq : ∀ b, 0 ≤ q b := by
    intro b
    exact div_nonneg (by split_ifs <;> first | exact (hp b).le | exact le_rfl) hP.le
  have hq1 : ∑ b, q b = 1 := by
    dsimp only [q]
    rw [← Finset.sum_div]
    simpa only [mass, Finset.sum_filter] using div_self (ne_of_gt hP)
  have he : v a-cellMean p v g (g a) = ∑ b, q b*(v a-v b) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq1, one_mul]
    rfl
  rw [he]
  calc
    p a * |∑ b, q b*(v a-v b)| ≤ p a * ∑ b, |q b*(v a-v b)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (hp a).le
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [abs_mul, abs_of_nonneg (hq b)]
      dsimp only [q]
      by_cases hg : g a = g b
      · simp only [hg, ite_true]
        ring
      · simp only [hg, Ne.symm hg, ite_false, zero_div, mul_zero, zero_mul]

end FiniteRefinement

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteRefinement
open scoped BigOperators ENNReal
open MeasureTheory
open FiniteEntropy


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.FiniteRefinement.mean_deviation_le_coupling.{uα,uβ} := @_root_.OAI.EntropyRateDimension.FiniteRefinement.mean_deviation_le_coupling.{uα,uβ}
