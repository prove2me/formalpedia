-- Prove2me | solution 2 for OAI.EntropyRateDimension.ProductLaw.moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:36:13.464432+00:00
-- url     : https://prove2.me/submissions/433b2b12-9381-49fb-86e3-369c9220fac0

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/ProductLaw.lean:L29-L43
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.ProductLaw.moment. The node keeps its source
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

-- ---- from OAI.MeasureTheory.SelfSimilar.ProductLaw ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace ProductLaw

variable {ι : Type uι} {α : Type uα} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem moment (p f : ι → α → ℝ) (s : Finset ι)
    (hp : ∀ i, ∑ a, p i a = 1) :
    (∑ x, weight p x * ∏ i ∈ s, f i (x i)) = ∏ i ∈ s, ∑ a, p i a * f i a := by
  classical
  have h := (Fintype.prod_sum (fun i a => p i a * if i ∈ s then f i a else 1)).symm
  have hleft : ∀ x : ι → α, (∏ i, p i (x i) * if i ∈ s then f i (x i) else 1) =
      weight p x * ∏ i ∈ s, f i (x i) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq]
    rfl
  have hright : ∀ i, (∑ a, p i a * if i ∈ s then f i a else 1) =
      if i ∈ s then ∑ a, p i a * f i a else 1 := by
    intro i
    split_ifs <;> simp_all only [mul_one]
  simpa only [hleft, hright, Finset.prod_ite_mem_eq] using h

variable {β : Type uβ} [DecidableEq β]

end ProductLaw

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.ProductLaw
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uι,uα} : type_of% @_root_.OAI.EntropyRateDimension.ProductLaw.moment.{uι,uα} := @_root_.OAI.EntropyRateDimension.ProductLaw.moment.{uι,uα}
