-- Prove2me | solution 1 for OAI.EntropyRateDimension.Typed.expected_retained_gain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:01:44.325355+00:00
-- url     : https://prove2.me/submissions/638c4216-0351-4282-878a-194b74d3a88a

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/WindowGain.lean:L67-L92
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Typed.expected_retained_gain. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_Typed_conditional_gain

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

theorem wordWeight_append (S : System ι) {m n : ℕ} (u : Fin m → ι) (v : Fin n → ι) :
    S.wordWeight (Fin.append u v)=S.wordWeight u*S.wordWeight v := by
  simp only [wordWeight,Fin.prod_univ_add,Fin.append_left,Fin.append_right]

end EntropyRateDimension.System

namespace EntropyRateDimension.Typed
open MeasureTheory FairPairs FiniteCondition
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

end EntropyRateDimension.Typed

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

theorem listTail_ofFn (S : System α) (tag : α → β) (μ : Measure ℝ) {n : ℕ} (w : Fin n → α) :
    listTail S tag μ (List.ofFn w)=tail S tag μ w := by
  apply apply_word_congr (fun _ v => tail S tag μ v) (List.length_ofFn ..)
  intro i
  simp only [List.get_eq_getElem,List.getElem_ofFn]
  rfl

theorem listScaledTail_ofFn (S : System α) (tag : α → β) (μ : Measure ℝ)
    (a : ℝ) {n : ℕ} (w : Fin n → α) :
    listScaledTail S tag μ a (List.ofFn w)=scaledTail S tag μ a w := by
  simp only [listScaledTail,listTail_ofFn,scaledTail]

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

theorem wordAverage_mul (S : System α) (n : ℕ) (c : ℝ) (f : List α → ℝ) :
    S.wordAverage n (fun W => c*f W)=c*S.wordAverage n f := by
  simp only [wordAverage,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem wordAverage_append (S : System α) (m n : ℕ) (f : List α → ℝ) :
    S.wordAverage (m+n) f =
      ∑ u : Fin m → α, S.wordWeight u*∑ v : Fin n → α, S.wordWeight v*f (List.ofFn u++List.ofFn v) := by
  rw [wordAverage,sum_words_append]
  simp only [wordWeight_append,List.ofFn_fin_append,Finset.mul_sum,mul_assoc]

theorem wordAverage_future_le (S : System α) (m n : ℕ) (f g : List α → ℝ)
    (h : ∀ u : Fin m → α,
      (∑ v : Fin n → α, S.wordWeight v*f (List.ofFn u++List.ofFn v)) ≤
      ∑ v : Fin n → α, S.wordWeight v*g (List.ofFn u++List.ofFn v)) :
    S.wordAverage (m+n) f ≤ S.wordAverage (m+n) g := by
  rw [wordAverage_append,wordAverage_append]
  exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (h u) (S.wordWeight_pos u).le)

end EntropyRateDimension.System

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.WindowGain ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs Windows
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

omit [Fintype α] [DecidableEq β] in
theorem three_segment {j n t : ℕ} (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
    (((List.ofFn u++List.ofFn w)++List.ofFn z).drop j).take n=List.ofFn w := by
  have h1 : ((List.ofFn u++List.ofFn w)++List.ofFn z).drop j=List.ofFn w++List.ofFn z := by
    rw [List.append_assoc]
    simpa only [List.length_ofFn] using (List.drop_append_length (l₁ := List.ofFn u) (l₂ := List.ofFn w++List.ofFn z))
  rw [h1]
  simpa only [List.length_ofFn] using (List.take_append_length (l₁ := List.ofFn w) (l₂ := List.ofFn z))

omit [Fintype α] [DecidableEq β] in
theorem three_take {j n t : ℕ} (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
    ((List.ofFn u++List.ofFn w)++List.ofFn z).take j=List.ofFn u := by
  rw [List.append_assoc]
  simpa only [List.length_ofFn] using (List.take_append_length (l₁ := List.ofFn u) (l₂ := List.ofFn w++List.ofFn z))

theorem three_retained (S : System α) (A' : ℝ) (a B L : ℤ)
    {j n t : ℕ} (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
    Retained (fun i => S.listDepth (((List.ofFn u++List.ofFn w)++List.ofFn z).take i)) A' n a B L j ↔
      S.wordDepth w ≤ A'*n ∧ a ≤ L-⌈S.wordDepth u⌉ ∧ L-⌈S.wordDepth u⌉ ≤ B := by
  simp only [Retained,S.listDepth_take_add,add_sub_cancel_left,three_segment,three_take,S.listDepth_ofFn]

theorem suffixLaw_at_append (S : System α) (tag : α → β) (μ : Measure ℝ) (U V : List α) :
    suffixLaw S tag μ (U++V) U.length=listScaledTail S tag μ (S.wordAffine U).1 V := by
  simp only [suffixLaw,List.take_append_length,List.drop_append_length]

theorem three_suffix_start (S : System α) (tag : α → β) (μ : Measure ℝ)
    {j n t : ℕ} (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
    suffixLaw S tag μ ((List.ofFn u++List.ofFn w)++List.ofFn z) j=
      scaledTail S tag μ (S.completeMap u).1 (Fin.append w z) := by
  rw [List.append_assoc]
  have h := suffixLaw_at_append S tag μ (List.ofFn u) (List.ofFn w++List.ofFn z)
  simp only [List.length_ofFn] at h
  rw [h,← List.ofFn_fin_append,listScaledTail_ofFn]
  rfl

theorem three_suffix_end (S : System α) (tag : α → β) (μ : Measure ℝ)
    {j n t : ℕ} (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
    suffixLaw S tag μ ((List.ofFn u++List.ofFn w)++List.ofFn z) (j+n)=
      scaledTail S tag μ ((S.completeMap u).1*(S.completeMap w).1) z := by
  have h := suffixLaw_at_append S tag μ (List.ofFn u++List.ofFn w) (List.ofFn z)
  simp only [List.length_append,List.length_ofFn] at h
  rw [h,listScaledTail_ofFn,S.wordAffine_append]
  rfl

theorem expected_retained_gain (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) {δ : ℝ}
    (hδ : ∀ v, 0 < v → δ ≤ deficit μ v) {M : ℕ} (hM : 4 < M)
    (he : 5/(M : ℝ)*Real.log 2 ≤ δ/2)
    {H j n : ℕ} (hH : j+n ≤ H) (A' : ℝ) (a B L : ℤ) :
    δ/2*S.wordAverage H (fun W => retainedCapacity S tag A' n a B L W j) ≤
      S.wordAverage H (fun W => retainedDrop S tag μ M A' n a B L W j) := by
  classical
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hH
  rw [← S.wordAverage_mul]
  apply S.wordAverage_future_le (j+n) t
  intro v
  obtain ⟨⟨u,w⟩,rfl⟩ := (Fin.appendEquiv j n).surjective v
  change (∑ z : Fin t → α, S.wordWeight z*(δ/2*retainedCapacity S tag A' n a B L
    (List.ofFn (Fin.append u w)++List.ofFn z) j)) ≤
    ∑ z : Fin t → α, S.wordWeight z*retainedDrop S tag μ M A' n a B L
      (List.ofFn (Fin.append u w)++List.ofFn z) j
  simp only [List.ofFn_fin_append]
  have hgain := conditional_gain S tag hr μ hμ hc hδ hM he u w t L
  simp only [retainedCapacity,retainedDrop,three_retained,three_segment,three_take,
    S.listDepth_ofFn,listLaw_ofFn,suffixWindow,three_suffix_start,three_suffix_end]
  split_ifs
  · simpa only [← Finset.sum_mul,S.wordWeight_sum,one_mul] using hgain
  · simp only [mul_zero,Finset.sum_const_zero,le_refl]

end EntropyRateDimension.Typed

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs Windows
open scoped BigOperators ENNReal


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.Typed.expected_retained_gain.{uα,uβ} := @_root_.OAI.EntropyRateDimension.Typed.expected_retained_gain.{uα,uβ}
