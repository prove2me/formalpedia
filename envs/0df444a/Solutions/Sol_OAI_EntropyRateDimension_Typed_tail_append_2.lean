-- Prove2me | solution 2 for OAI.EntropyRateDimension.Typed.tail_append
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:24:28.740073+00:00
-- url     : https://prove2.me/submissions/f429218b-9e3d-44c1-950b-7a2976af8dd6

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/TypedLaw.lean:L159-L172
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Typed.tail_append. The node keeps its source
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

-- ---- from OAI.MeasureTheory.SelfSimilar.WordTypes ----
namespace OAI

universe uι

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace System
variable {ι : Type uι} [Fintype ι]

theorem wordAffine_append (S : System ι) (v w : List ι) :
    S.wordAffine (v++w) = ((S.wordAffine v).1*(S.wordAffine w).1,
      (S.wordAffine v).1*(S.wordAffine w).2+(S.wordAffine v).2) := by
  induction v with
  | nil => simp [wordAffine]
  | cons i v ih => simp only [List.cons_append,wordAffine,ih]; ext <;> dsimp <;> ring

end System
end EntropyRateDimension

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.TypedLaw ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ uM

namespace EntropyRateDimension.FiniteCondition
open scoped BigOperators ENNReal
open MeasureTheory

end EntropyRateDimension.FiniteCondition

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

theorem sum_words_append {M : Type uM} [AddCommMonoid M] (m n : ℕ)
    (f : (Fin (m+n) → ι) → M) :
    (∑ w, f w)=∑ u : Fin m → ι, ∑ v : Fin n → ι, f (Fin.append u v) := by
  classical
  rw [← (Fin.appendEquiv m n).sum_comp f,Fintype.sum_prod_type]
  rfl

theorem completeMap_append (S : System ι) {m n : ℕ} (u : Fin m → ι) (v : Fin n → ι) :
    S.completeMap (Fin.append u v)=
      ((S.completeMap u).1*(S.completeMap v).1,
        (S.completeMap u).1*(S.completeMap v).2+(S.completeMap u).2) := by
  simp only [completeMap,List.ofFn_fin_append,wordAffine_append]

theorem wordMap_append (S : System ι) {m n : ℕ} (u : Fin m → ι) (v : Fin n → ι) :
    S.wordMap (Fin.append u v)=S.wordMap u ∘ S.wordMap v := by
  funext x
  simp only [wordMap,completeMap_append,Function.comp_apply]
  ring

end EntropyRateDimension.System

namespace EntropyRateDimension.Typed
open MeasureTheory FairPairs FiniteCondition
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem prob_append (S : System α) (tag : α → β) {m n : ℕ}
    (w u : Fin m → α) (z v : Fin n → α) :
    prob S tag (Fin.append w z) (Fin.append u v)=prob S tag w u*prob S tag z v := by
  simp only [prob,Fin.prod_univ_add,Fin.append_left,Fin.append_right]

theorem tail_append (S : System α) (tag : α → β) (μ : Measure ℝ)
    {m n : ℕ} (w : Fin m → α) (z : Fin n → α) :
    tail S tag μ (Fin.append w z)=tail S tag (tail S tag μ z) w := by
  classical
  rw [tail,System.sum_words_append]
  simp only [tail]
  apply Finset.sum_congr rfl
  intro u _
  rw [Measure.map_finset_sum (S.wordMap_measurable u).aemeasurable,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [prob_append,ENNReal.ofReal_mul (prob_nonneg S tag w u),
    Measure.map_smul _ _ (S.wordMap u),smul_smul,
    Measure.map_map (S.wordMap_measurable u) (S.wordMap_measurable v),S.wordMap_append]

end EntropyRateDimension.Typed

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
open MeasureTheory FairPairs FiniteCondition
open scoped BigOperators ENNReal


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.Typed.tail_append.{uα,uβ} := @_root_.OAI.EntropyRateDimension.Typed.tail_append.{uα,uβ}
