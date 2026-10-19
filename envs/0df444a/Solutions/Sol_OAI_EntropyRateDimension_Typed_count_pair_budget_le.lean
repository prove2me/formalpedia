-- Prove2me | solution 1 for OAI.EntropyRateDimension.Typed.count_pair_budget_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:06:32.629777+00:00
-- url     : https://prove2.me/submissions/1b07e40c-26af-4ab2-9fbd-4a17fac1e65a

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/GlobalCount.lean:L34-L96
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Typed.count_pair_budget_le. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_map_affine
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_mixture
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_averaged_nested_bounds
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_averaged_nested_translate_mixture
import Theorems.Thm_OAI_EntropyRateDimension_Typed_expected_capacity_targets
import Theorems.Thm_OAI_EntropyRateDimension_Typed_expected_retained_gain
import Theorems.Thm_OAI_EntropyRateDimension_Typed_tail_append
import Theorems.Thm_OAI_EntropyRateDimension_Windows_retained_sum_le

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

-- ---- from OAI.MeasureTheory.SelfSimilar.Conditioning ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα uβ

namespace EntropyRateDimension.FairPairs
open MeasureTheory FiniteEntropy
open scoped BigOperators ENNReal

theorem Law.smul_sum_ofObservable {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ)
    (F : ℝ → Measure ℝ) :
    (∑ x : (Law.ofObservable s p hp hp1 f).support,
      ENNReal.ofReal ((Law.ofObservable s p hp hp1 f).prob x) • F x) =
      ∑ a ∈ s, ENNReal.ofReal (p a) • F (f a) := by
  classical
  change (∑ x : s.image f, ENNReal.ofReal (mass s p f x) • F x)=_
  rw [Finset.sum_coe_sort (s.image f) (fun x => ENNReal.ofReal (mass s p f x) • F x)]
  change (∑ x ∈ s.image f, ENNReal.ofReal (mass s p f x) • F x)=_
  simp only [mass,ENNReal.ofReal_sum_of_nonneg (fun a ha => (hp a (Finset.mem_filter.mp ha).1).le),
    Finset.sum_smul]
  calc
    _ = ∑ x ∈ s.image f, ∑ a ∈ s.filter (fun a => f a=x), ENNReal.ofReal (p a) • F (f a) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha) _

end EntropyRateDimension.FairPairs

namespace EntropyRateDimension.FiniteCondition
open FiniteEntropy FairPairs MeasureTheory
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem law_smul_sum (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a : α)
    (f : α → ℝ) (F : ℝ → Measure ℝ) :
    (∑ x : (law p hp tag a f).support, ENNReal.ofReal ((law p hp tag a f).prob x) • F x)=
      ∑ v, ENNReal.ofReal (posterior p tag a v) • F (f v) := by
  classical
  rw [law,Law.smul_sum_ofObservable]
  simp only [posterior,apply_ite ENNReal.ofReal,ENNReal.ofReal_zero,ite_smul,zero_smul,
    ← Finset.sum_filter]
  rfl

end EntropyRateDimension.FiniteCondition

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.PairGain ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory
open scoped BigOperators ENNReal

theorem finiteConv_window_mono (ν : FairPairs.Law) (a : ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    window μ s (N*s) ≤ window (finiteConv ν a μ) s (N*s) :=
  averaged_nested_translate_mixture μ hμ (fun x : ν.support => ν.prob x)
    (fun x => (ν.prob_pos x x.property).le) ν.subtype_sum (fun x => a*x) hs hN

end EntropyRateDimension.MeasureEntropy

namespace EntropyRateDimension.FairPairs
open MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal

end EntropyRateDimension.FairPairs

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory FairPairs
open scoped BigOperators ENNReal

end EntropyRateDimension.MeasureEntropy

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.TypedLaw ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uι uα uβ uγ uM

namespace EntropyRateDimension.FiniteCondition
open scoped BigOperators ENNReal
open MeasureTheory

theorem mass_pi {α : Type uα} {β : Type uβ} {γ : Type uγ} [Fintype α] [Fintype γ] [DecidableEq γ] [DecidableEq β]
    (p : α → ℝ) (tag : α → β) (w : γ → α) :
    mass (fun v : γ → α => ∏ j, p (v j)) (fun v j => tag (v j)) w =
      ∏ j, mass p tag (w j) := by
  classical
  simp only [mass,fiber,Finset.sum_filter]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : (fun j => tag (v j))=(fun j => tag (w j))
  · simp only [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro j _
    rw [ite_eq_left (congrFun h j)]
  · rw [ite_eq_right h]
    symm
    obtain ⟨j,hj⟩ : ∃ j, tag (v j)≠tag (w j) := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

theorem posterior_pi {α : Type uα} {β : Type uβ} {γ : Type uγ} [Fintype α] [Fintype γ] [DecidableEq γ] [DecidableEq β]
    (p : α → ℝ) (tag : α → β) (w v : γ → α) :
    posterior (fun u : γ → α => ∏ j, p (u j)) (fun u j => tag (u j)) w v =
      ∏ j, posterior p tag (w j) (v j) := by
  classical
  rw [posterior,mass_pi]
  by_cases h : (fun j => tag (v j))=(fun j => tag (w j))
  · rw [ite_eq_left h,← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [posterior,ite_eq_left (congrFun h j)]
  · rw [ite_eq_right h]
    symm
    obtain ⟨j,hj⟩ : ∃ j, tag (v j)≠tag (w j) := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [posterior,ite_eq_right hj])

end EntropyRateDimension.FiniteCondition

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

end EntropyRateDimension.System

namespace EntropyRateDimension.Typed
open MeasureTheory FairPairs FiniteCondition
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem prob_as_posterior (S : System α) (tag : α → β) {n : ℕ} (w v : Fin n → α) :
    prob S tag w v=posterior S.wordWeight (tagWord tag) w v :=
  (posterior_pi S.weight tag w v).symm

theorem prob_slope (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} {w v : Fin n → α} (h : prob S tag w v≠0) :
    (S.completeMap v).1=(S.completeMap w).1 := by
  rw [S.completeMap_slope,S.completeMap_slope]
  apply Finset.prod_congr rfl
  intro j hj
  apply hr
  by_contra ht
  apply h
  apply Finset.prod_eq_zero hj
  exact ite_eq_right ht

theorem tail_compact (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : MeasureEntropy.CompactlyCarried μ) {n : ℕ} (w : Fin n → α) :
    MeasureEntropy.CompactlyCarried (tail S tag μ w) := by
  apply MeasureEntropy.CompactlyCarried.mixture
  intro v
  exact hμ.map_affine _ _

end EntropyRateDimension.Typed

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.TailConvolution ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs FiniteCondition
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem scaledTail_compact (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : CompactlyCarried μ) (a : ℝ) {n : ℕ} (w : Fin n → α) :
    CompactlyCarried (scaledTail S tag μ a w) := by
  simpa only [scaledTail,add_zero] using (tail_compact S tag μ hμ w).map_affine a 0

theorem scaled_tail_convolution (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) (a : ℝ) {n : ℕ} (w : Fin n → α) :
    scaledTail S tag μ a w =
      finiteConv (law S tag w) a (μ.map (fun x => (a*(S.completeMap w).1)*x)) := by
  classical
  have he := law_smul_sum S.wordWeight (fun v : Fin n → α => S.wordWeight_pos v)
    (tagWord tag) w (fun v => (S.completeMap v).2)
    (fun x => shiftLaw (μ.map (fun y => (a*(S.completeMap w).1)*y)) (a*x))
  change finiteConv (law S tag w) a (μ.map (fun x => (a*(S.completeMap w).1)*x)) = _ at he
  rw [he]
  unfold scaledTail tail
  rw [Measure.map_finset_sum (show AEMeasurable (fun x : ℝ => a*x) _ from
    (measurable_const.mul measurable_id).aemeasurable)]
  simp only [Measure.map_smul (f := fun x : ℝ => a*x)]
  apply Finset.sum_congr rfl
  intro v _
  rw [← prob_as_posterior]
  by_cases h : prob S tag w v=0
  · simp only [h,ENNReal.ofReal_zero,zero_smul]
  · rw [shiftLaw,Measure.map_map (show Measurable (fun x : ℝ => a*x) from
        measurable_const.mul measurable_id) (S.wordMap_measurable v),
      Measure.map_map (show Measurable (fun x : ℝ => x+a*(S.completeMap v).2) from
        measurable_id.add_const _) (show Measurable
        (fun x : ℝ => (a*(S.completeMap w).1)*x) from measurable_const.mul measurable_id)]
    congr 2
    funext x
    simp only [Function.comp_apply,System.wordMap,prob_slope S tag hr h]
    ring

theorem scaledTail_append (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) (a : ℝ) {m n : ℕ} (w : Fin m → α) (z : Fin n → α) :
    scaledTail S tag μ a (Fin.append w z)=
      finiteConv (law S tag w) a (scaledTail S tag μ (a*(S.completeMap w).1) z) := by
  change (tail S tag μ (Fin.append w z)).map (fun x => a*x)=_
  rw [tail_append]
  exact scaled_tail_convolution S tag hr _ a w

end EntropyRateDimension.Typed

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteVariance ----
namespace OAI

universe uα

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

theorem letterDepth_pos (S : System α) (a : α) : 0 < S.letterDepth a :=
  div_pos (neg_pos.mpr (Real.log_neg (S.ratio_pos a) (S.ratio_lt_one a)))
    (Real.log_pos (by norm_num))

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

theorem listScaledTail_compact (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : CompactlyCarried μ) (a : ℝ) (W : List α) :
    CompactlyCarried (listScaledTail S tag μ a W) := scaledTail_compact S tag μ hμ a W.get

theorem listScaledTail_append (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) (a : ℝ) (U V : List α) :
    listScaledTail S tag μ a (U++V)=
      finiteConv (listLaw S tag U) a (listScaledTail S tag μ (a*(S.wordAffine U).1) V) := by
  have h := scaledTail_append S tag hr μ a U.get V.get
  rw [← listScaledTail_ofFn,← listScaledTail_ofFn,← listLaw_ofFn] at h
  simpa only [List.ofFn_fin_append,List.ofFn_get,System.completeMap] using h

theorem suffixLaw_compact (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : CompactlyCarried μ) (W : List α) (j : ℕ) : CompactlyCarried (suffixLaw S tag μ W j) :=
  listScaledTail_compact S tag μ hμ _ _

theorem suffixLaw_convolution (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) (W : List α) (j n : ℕ) :
    suffixLaw S tag μ W j=finiteConv (listLaw S tag ((W.drop j).take n))
      (S.wordAffine (W.take j)).1 (suffixLaw S tag μ W (j+n)) := by
  have h := listScaledTail_append S tag hr μ (S.wordAffine (W.take j)).1
    ((W.drop j).take n) ((W.drop j).drop n)
  rw [List.take_append_drop,List.drop_drop] at h
  simpa only [suffixLaw,List.take_add,System.wordAffine_append] using h

theorem suffixWindow_antitone (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (W : List α) :
    Antitone (suffixWindow S tag μ s N W) := by
  intro j k hjk
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hjk
  change window (suffixLaw S tag μ W (j+n)) s (N*s) ≤ window (suffixLaw S tag μ W j) s (N*s)
  rw [suffixLaw_convolution S tag hr μ W j n]
  exact finiteConv_window_mono _ _ _ (suffixLaw_compact S tag μ hμ W (j+n)) hs hN

theorem suffixWindow_bounds (S : System α) (tag : α → β)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (W : List α) (j : ℕ) :
    0 ≤ suffixWindow S tag μ s N W j ∧ suffixWindow S tag μ s N W j ≤ Real.log N :=
  averaged_nested_bounds _ (suffixLaw_compact S tag μ hμ W j) hs hN

end EntropyRateDimension.Typed

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

theorem listDepth_nonneg (S : System α) (W : List α) : 0 ≤ S.listDepth W :=
  List.sum_nonneg (by intro x hx; obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx; exact (S.letterDepth_pos a).le)

theorem listDepth_append (S : System α) (U V : List α) : S.listDepth (U++V)=S.listDepth U+S.listDepth V := by
  simp only [listDepth,List.map_append,List.sum_append]

theorem listDepth_take_add (S : System α) (W : List α) (j n : ℕ) :
    S.listDepth (W.take (j+n))=S.listDepth (W.take j)+S.listDepth ((W.drop j).take n) := by
  rw [List.take_add,listDepth_append]

theorem listDepth_monotone (S : System α) (W : List α) : Monotone (fun j => S.listDepth (W.take j)) := by
  intro j k hjk
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hjk
  dsimp only
  rw [listDepth_take_add]
  exact le_add_of_nonneg_right (S.listDepth_nonneg _)

theorem listDepth_le (S : System α) {D : ℝ} (hD : ∀ a, S.letterDepth a ≤ D) (W : List α) :
    S.listDepth W ≤ D*W.length := by
  induction W with
  | nil => simp [listDepth]
  | cons a W ih =>
    simp only [listDepth,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at ih ⊢
    nlinarith [hD a]

theorem listDepth_take_le (S : System α) {D : ℝ} (hD : 0 ≤ D) (hd : ∀ a, S.letterDepth a ≤ D)
    (W : List α) (j : ℕ) : S.listDepth (W.take j) ≤ D*j := by
  have hh := S.listDepth_le hd (W.take j)
  rw [List.length_take] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_left j W.length) hD)

end EntropyRateDimension.System

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.WordAverage ----
namespace OAI

universe uι uα

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

theorem wordAverage_mono (S : System α) (n : ℕ) {f g : List α → ℝ}
    (h : ∀ W, W.length=n → f W ≤ g W) : S.wordAverage n f ≤ S.wordAverage n g := by
  exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left
    (h (List.ofFn w) (List.length_ofFn ..)) (S.wordWeight_pos w).le)

theorem wordAverage_const (S : System α) (n : ℕ) (c : ℝ) : S.wordAverage n (fun _ => c)=c := by
  rw [wordAverage,← Finset.sum_mul,S.wordWeight_sum,one_mul]

theorem wordAverage_finset_sum {ι : Type uι} (S : System α) (n : ℕ) (s : Finset ι) (f : ι → List α → ℝ) :
    S.wordAverage n (fun W => ∑ i ∈ s, f i W)=∑ i ∈ s, S.wordAverage n (f i) := by
  simp only [wordAverage,Finset.mul_sum]
  exact Finset.sum_comm

end EntropyRateDimension.System

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.GlobalCount ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs Windows
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem total_expected_drop_le (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hc : CompactlyCarried μ)
    {M : ℕ} (hM : 0 < M) (H : ℕ) {q : ℕ} (n K : Fin q → ℕ) (a B : Fin q → ℤ) (A' : ℝ)
    (hsep : ∀ i h : Fin q, h < i → (B h : ℝ)<(a i : ℝ)-A'*n i-1) (L : ℤ) :
    (∑ i, ∑ k ∈ Finset.range (K i), S.wordAverage H (fun W =>
      retainedDrop S tag μ M A' (n i) (a i) (B i) L W (k*n i))) ≤ Real.log ((M*M : ℕ) : ℝ) := by
  classical
  have hs : 0 < (2 : ℝ)^(-L)/(M : ℝ) := div_pos (zpow_pos (by norm_num) _) (by exact_mod_cast hM)
  have hMM : 0 < M*M := Nat.mul_pos hM hM
  simp_rw [← S.wordAverage_finset_sum]
  calc
    _ ≤ S.wordAverage H (fun _ => Real.log ((M*M : ℕ) : ℝ)) := by
      apply S.wordAverage_mono
      intro W _
      have hh := retained_sum_le n K a B A' hsep (fun j => S.listDepth (W.take j))
        (S.listDepth_monotone W) L (suffixWindow S tag μ ((2 : ℝ)^(-L)/(M : ℝ)) (M*M) W)
        (suffixWindow_antitone S tag hr μ hc hs hMM W)
        (fun j => (suffixWindow_bounds S tag μ hc hs hMM W j).1)
      exact hh.trans (suffixWindow_bounds S tag μ hc hs hMM W 0).2
    _ = _ := S.wordAverage_const _ _

theorem count_pair_budget_le (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) {δ : ℝ}
    (hδ : ∀ v, 0 < v → δ ≤ deficit μ v) {M : ℕ} (hM : 4 < M)
    (he : 5/(M : ℝ)*Real.log 2 ≤ δ/2)
    {H D q : ℕ} (hD : 1 ≤ D) (hd : ∀ v, S.letterDepth v ≤ D)
    (n K : Fin q → ℕ) (a B : Fin q → ℤ) (A' : ℝ)
    (hkn : ∀ i, K i*n i=H) (ha : ∀ i, 1 ≤ a i) (hB : ∀ i, B i ≤ (H : ℤ))
    (hsep : ∀ i h : Fin q, h < i → (B h : ℝ)<(a i : ℝ)-A'*n i-1) :
    (δ/2)*(∑ i, (K i : ℝ)*pairBudget S tag A' (a i) (B i) (n i)) ≤
      (2*D*H : ℕ)*Real.log ((M*M : ℕ) : ℝ) := by
  classical
  let T : ℤ := (2*D*H : ℕ)
  have hkH (i : Fin q) (k : ℕ) (hk : k ∈ Finset.range (K i)) : k*n i+n i ≤ H := by
    rw [← Nat.succ_mul,← hkn i]
    exact Nat.mul_le_mul_right _ (Finset.mem_range.mp hk)
  have hcover (i : Fin q) (k : ℕ) (hk : k ∈ Finset.range (K i)) (W : List α) :
      0 ≤ ⌈S.listDepth (W.take (k*n i))⌉ ∧ B i+⌈S.listDepth (W.take (k*n i))⌉ ≤ T := by
    refine ⟨Int.ceil_nonneg (S.listDepth_nonneg _),?_⟩
    have hh : S.listDepth (W.take (k*n i)) ≤ ((D*H : ℕ) : ℝ) := by
      have h1 := S.listDepth_take_le (Nat.cast_nonneg D) hd W (k*n i)
      have h2 : k*n i ≤ H := (Nat.le_add_right _ _).trans (hkH i k hk)
      have h2R : ((k*n i : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h2
      exact h1.trans (by simpa only [Nat.cast_mul] using
        mul_le_mul_of_nonneg_left h2R (Nat.cast_nonneg D))
    have hh' : ⌈S.listDepth (W.take (k*n i))⌉ ≤ ((D*H : ℕ) : ℤ) := by
      apply Int.ceil_le.mpr
      exact_mod_cast hh
    have hDH : H ≤ D*H := by simpa only [one_mul] using Nat.mul_le_mul_right H hD
    dsimp only [T]
    have hDH' : (H : ℤ) ≤ ((D*H : ℕ) : ℤ) := by exact_mod_cast hDH
    have hmul : ((2*D*H : ℕ) : ℤ)=2*((D*H : ℕ) : ℤ) := by push_cast; ring
    rw [hmul]
    linarith [hB i]
  have hlocal (i : Fin q) (k : ℕ) (hk : k ∈ Finset.range (K i)) :
      (δ/2)*pairBudget S tag A' (a i) (B i) (n i) ≤
      ∑ L ∈ Finset.Icc 1 T, S.wordAverage H (fun W => retainedDrop S tag μ M A' (n i) (a i) (B i) L W (k*n i)) := by
    rw [← expected_capacity_targets S tag (hkH i k hk) A' (a i) (B i) T (ha i) (hcover i k hk),Finset.mul_sum]
    exact Finset.sum_le_sum (fun L _ => expected_retained_gain S tag hr μ hμ hc hδ hM he
      (hkH i k hk) A' (a i) (B i) L)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.range (K i)) (fun k hk => hlocal i k hk))
  have hup : (∑ i, ∑ k ∈ Finset.range (K i), ∑ L ∈ Finset.Icc 1 T,
      S.wordAverage H (fun W => retainedDrop S tag μ M A' (n i) (a i) (B i) L W (k*n i))) ≤
      (2*D*H : ℕ)*Real.log ((M*M : ℕ) : ℝ) := by
    calc
      _ = ∑ L ∈ Finset.Icc 1 T, ∑ i, ∑ k ∈ Finset.range (K i),
          S.wordAverage H (fun W => retainedDrop S tag μ M A' (n i) (a i) (B i) L W (k*n i)) := by
        simp_rw [Finset.sum_comm (s := Finset.range _) (t := Finset.Icc 1 T)]
        exact Finset.sum_comm
      _ ≤ ∑ L ∈ Finset.Icc 1 T, Real.log ((M*M : ℕ) : ℝ) := Finset.sum_le_sum (fun L _ =>
        total_expected_drop_le S tag hr μ hc (by omega) H n K a B A' hsep L)
      _ = _ := by
        have hcard : (Finset.Icc (1 : ℤ) T).card=2*D*H := by
          simp only [Int.card_Icc,add_sub_cancel_right,T,Int.toNat_natCast]
        rw [Finset.sum_const,hcard,nsmul_eq_mul]
  apply le_trans _ hup
  convert hsum using 1
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end EntropyRateDimension.Typed

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs Windows
open scoped BigOperators ENNReal


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.Typed.count_pair_budget_le.{uα,uβ} := @_root_.OAI.EntropyRateDimension.Typed.count_pair_budget_le.{uα,uβ}
