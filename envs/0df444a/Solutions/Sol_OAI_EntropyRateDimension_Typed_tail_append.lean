-- Prove2me | solution 1 for OAI.EntropyRateDimension.Typed.tail_append
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:00:58.114992+00:00
-- url     : https://prove2.me/submissions/de0dbe83-4ed6-49d6-bbc5-f894498e8024

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
universe uι uα uβ uγ uM
open MeasureTheory FairPairs FiniteCondition
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]
theorem h41n_map_fsum {κ : Type*} (s : Finset κ) (m : κ → Measure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) : (∑ i ∈ s, m i).map f = ∑ i ∈ s, (m i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hf, ih]

theorem h41n_wordAffine_append {ι : Type*} [Fintype ι] (S : System ι) (l1 l2 : List ι) (x : ℝ) :
    (S.wordAffine (l1 ++ l2)).1 * x + (S.wordAffine (l1 ++ l2)).2 =
      (S.wordAffine l1).1 * ((S.wordAffine l2).1 * x + (S.wordAffine l2).2) + (S.wordAffine l1).2 := by
  induction l1 with
  | nil => simp [System.wordAffine]
  | cons i l ih =>
    simp only [List.cons_append, System.wordAffine]
    linear_combination S.ratio i * ih

theorem h41n_wordMap_append {ι : Type*} [Fintype ι] (S : System ι) {m n : ℕ}
    (v1 : Fin m → ι) (v2 : Fin n → ι) :
    S.wordMap (Fin.append v1 v2) = S.wordMap v1 ∘ S.wordMap v2 := by
  funext x
  simp only [System.wordMap, System.completeMap, Function.comp, List.ofFn_fin_append]
  exact h41n_wordAffine_append S _ _ x

theorem solution (S : System α) (tag : α → β) (μ : Measure ℝ)
    {m n : ℕ} (w : Fin m → α) (z : Fin n → α) :
    tail S tag μ (Fin.append w z)=tail S tag (tail S tag μ z) w := by
  have hprob : ∀ (v1 : Fin m → α) (v2 : Fin n → α),
      prob S tag (Fin.append w z) (Fin.append v1 v2) = prob S tag w v1 * prob S tag z v2 := by
    intro v1 v2
    simp only [prob]
    rw [Fin.prod_univ_add]
    simp [Fin.append_left, Fin.append_right]
  unfold tail
  rw [← (Fin.appendEquiv m n).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v1 _
  rw [h41n_map_fsum _ _ (S.wordMap_measurable _), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro v2 _
  rw [show (Fin.appendEquiv m n) (v1, v2) = Fin.append v1 v2 from rfl]
  rw [Measure.map_smul, Measure.map_map (S.wordMap_measurable _) (S.wordMap_measurable _),
    smul_smul, ← ENNReal.ofReal_mul (prob_nonneg S tag w v1), hprob, h41n_wordMap_append]

