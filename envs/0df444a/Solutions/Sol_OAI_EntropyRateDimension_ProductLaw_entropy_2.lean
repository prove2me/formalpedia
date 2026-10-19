-- Prove2me | solution 2 for OAI.EntropyRateDimension.ProductLaw.entropy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:38:52.354916+00:00
-- url     : https://prove2.me/submissions/a3383676-aff7-474b-91ff-e95d79ec30e5

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/ProductLaw.lean:L68-L87
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.ProductLaw.entropy. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_ProductLaw_moment

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

theorem entropy (p : ι → α → ℝ) (hp : ∀ i, ∑ a, p i a = 1) :
    FiniteEntropy.entropy Finset.univ (weight p) =
      ∑ i, FiniteEntropy.entropy Finset.univ (p i) := by
  classical
  have hm : ∀ i, (∑ x, weight p x * Real.log (p i (x i))) = ∑ a, p i a * Real.log (p i a) := by
    intro i
    simpa only [Finset.prod_singleton] using moment p (fun j a => Real.log (p j a)) {i} hp
  have hn : ∀ x : ι → α, Real.negMulLog (weight p x) =
      -(∑ i, weight p x * Real.log (p i (x i))) := by
    intro x
    by_cases hx : weight p x = 0
    · simp only [hx, Real.negMulLog_zero, zero_mul, Finset.sum_const_zero, neg_zero]
    · change -(weight p x) * Real.log (weight p x) = _
      have hfac : ∀ i ∈ (Finset.univ : Finset ι), p i (x i) ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hx)
      rw [weight, Real.log_prod hfac, Finset.mul_sum]
      simp only [neg_mul, Finset.sum_neg_distrib]
  simp only [FiniteEntropy.entropy, hn, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp only [hm, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]

variable {β : Type uβ} [DecidableEq β]

end ProductLaw

end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.ProductLaw
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uι,uα} : type_of% @_root_.OAI.EntropyRateDimension.ProductLaw.entropy.{uι,uα} := @_root_.OAI.EntropyRateDimension.ProductLaw.entropy.{uι,uα}
