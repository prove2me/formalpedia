-- Prove2me | solution 1 for OAI.EntropyRateDimension.ProductLaw.moment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:30:57.931477+00:00
-- url     : https://prove2.me/submissions/74e3f0a8-a465-4c77-a824-2391f3757e61

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.ProductLaw
universe uι uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory
variable {ι : Type uι} {α : Type uα} [Fintype ι] [DecidableEq ι] [Fintype α]


theorem solution (p f : ι → α → ℝ) (s : Finset ι)
    (hp : ∀ i, ∑ a, p i a = 1) :
    (∑ x, weight p x * ∏ i ∈ s, f i (x i)) = ∏ i ∈ s, ∑ a, p i a * f i a := by
  classical
  have e1 : ∀ x : ι → α, weight p x * ∏ i ∈ s, f i (x i) =
      ∏ i, (p i (x i) * (if i ∈ s then f i (x i) else 1)) := by
    intro x
    rw [Finset.prod_mul_distrib, weight, ← Finset.prod_filter]
    congr 2
    ext i; simp
  simp only [e1]
  have h := Finset.sum_prod_piFinset (Finset.univ : Finset α)
    (fun i a => p i a * (if i ∈ s then f i a else 1))
  rw [Fintype.piFinset_univ] at h
  rw [h, ← Finset.prod_subset (Finset.subset_univ s)
    (f := fun i => ∑ j, p i j * if i ∈ s then f i j else 1) (fun i _ hi => by simp [hi, hp i])]
  exact Finset.prod_congr rfl fun i hi => by simp [hi]

