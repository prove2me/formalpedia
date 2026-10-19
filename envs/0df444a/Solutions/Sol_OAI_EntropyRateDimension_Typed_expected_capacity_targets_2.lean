-- Prove2me | solution 2 for OAI.EntropyRateDimension.Typed.expected_capacity_targets
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:03:46.325345+00:00
-- url     : https://prove2.me/submissions/8051b6a7-f51b-4cf9-b7cb-256828d4baaa

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/WindowGain.lean:L94-L113
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Typed.expected_capacity_targets. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RetainedLoss
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairBands
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowCount
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowGain
import Theorems.Thm_OAI_EntropyRateDimension_System_wordAverage_segment
import Theorems.Thm_OAI_EntropyRateDimension_Windows_sum_target_shift

-- ---- from OAI.MeasureTheory.SelfSimilar.UpperBound ----
namespace OAI

universe uι uM

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

theorem completeMap_log_slope (S : System ι) {n : ℕ} (w : Fin n → ι) :
    Real.log |(S.completeMap w).1| = ∑ j, Real.log |S.ratio (w j)| := by
  rw [completeMap_slope,Finset.abs_prod,Real.log_prod]
  exact fun j _ => (S.ratio_pos (w j)).ne'

end EntropyRateDimension.System

namespace EntropyRateDimension.Coding
open MeasureTheory
open scoped BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_5
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_5
end EntropyRateDimension.Coding

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.System.instMeasurableSpace_1
attribute [local instance] OAI.EntropyRateDimension.System.instMeasurableSingletonClass_1
end EntropyRateDimension.System

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteVariance ----
namespace OAI

universe uα

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

theorem wordDepth_sum (S : System α) {n : ℕ} (w : Fin n → α) :
    S.wordDepth w=∑ j, S.letterDepth (w j) := by
  simp only [wordDepth,letterDepth,S.completeMap_log_slope,← Finset.sum_div,← Finset.sum_neg_distrib]

end EntropyRateDimension.System

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.SuffixLaw ----
namespace OAI

universe uα uβ uγ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

omit [Fintype α] [DecidableEq β] in
theorem apply_word_congr {γ : Type uγ} (F : (n : ℕ) → (Fin n → α) → γ)
    {m n : ℕ} (h : m=n) (v : Fin m → α) (w : Fin n → α)
    (he : ∀ i, v i=w (Fin.cast h i)) : F m v=F n w := by
  subst n
  exact congrArg (F m) (funext he)

theorem listLaw_ofFn (S : System α) (tag : α → β) {n : ℕ} (w : Fin n → α) :
    listLaw S tag (List.ofFn w)=law S tag w := by
  apply apply_word_congr (fun _ v => law S tag v) (List.length_ofFn ..)
  intro i
  simp only [List.get_eq_getElem,List.getElem_ofFn]
  rfl

end EntropyRateDimension.Typed

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

theorem listDepth_ofFn (S : System α) {n : ℕ} (w : Fin n → α) :
    S.listDepth (List.ofFn w)=S.wordDepth w := by
  simp only [listDepth,List.map_ofFn,List.sum_ofFn,wordDepth_sum,Function.comp_apply]

theorem listDepth_append (S : System α) (U V : List α) : S.listDepth (U++V)=S.listDepth U+S.listDepth V := by
  simp only [listDepth,List.map_append,List.sum_append]

theorem listDepth_take_add (S : System α) (W : List α) (j n : ℕ) :
    S.listDepth (W.take (j+n))=S.listDepth (W.take j)+S.listDepth ((W.drop j).take n) := by
  rw [List.take_add,listDepth_append]

end EntropyRateDimension.System

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.WordAverage ----
namespace OAI

universe uι uα

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

theorem wordAverage_finset_sum {ι : Type uι} (S : System α) (n : ℕ) (s : Finset ι) (f : ι → List α → ℝ) :
    S.wordAverage n (fun W => ∑ i ∈ s, f i W)=∑ i ∈ s, S.wordAverage n (f i) := by
  simp only [wordAverage,Finset.mul_sum]
  exact Finset.sum_comm

end EntropyRateDimension.System

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.WindowGain ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs Windows
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem expected_capacity_targets (S : System α) (tag : α → β)
    {H j n : ℕ} (hH : j+n ≤ H) (A' : ℝ) (a B T : ℤ)
    (ha : 1 ≤ a)
    (hcover : ∀ W : List α, 0 ≤ ⌈S.listDepth (W.take j)⌉ ∧ B+⌈S.listDepth (W.take j)⌉ ≤ T) :
    (∑ L ∈ Finset.Icc 1 T, S.wordAverage H (fun W => retainedCapacity S tag A' n a B L W j))=
      pairBudget S tag A' a B n := by
  classical
  rw [← S.wordAverage_finset_sum]
  have hpoint (W : List α) : (∑ L ∈ Finset.Icc 1 T, retainedCapacity S tag A' n a B L W j)=
      if S.listDepth ((W.drop j).take n) ≤ A'*n then
        ∑ ℓ ∈ Finset.Icc a B, capacity (listLaw S tag ((W.drop j).take n)) ℓ else 0 := by
    simp only [retainedCapacity,Retained,S.listDepth_take_add,add_sub_cancel_left]
    by_cases h : S.listDepth ((W.drop j).take n) ≤ A'*n
    · simp only [h,true_and]
      exact sum_target_shift _ a B _ T ha (hcover W).1 (hcover W).2
    · simp only [h,false_and,ite_false,Finset.sum_const_zero]
  simp_rw [hpoint]
  rw [S.wordAverage_segment hH (fun V => if S.listDepth V ≤ A'*n then
    ∑ ℓ ∈ Finset.Icc a B, capacity (listLaw S tag V) ℓ else 0)]
  simp only [System.wordAverage,System.listDepth_ofFn,listLaw_ofFn,pairBudget,mul_ite,mul_zero]

end EntropyRateDimension.Typed

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs Windows
open scoped BigOperators ENNReal


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.Typed.expected_capacity_targets.{uα,uβ} := @_root_.OAI.EntropyRateDimension.Typed.expected_capacity_targets.{uα,uβ}
