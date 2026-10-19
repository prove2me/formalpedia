-- Prove2me | solution 1 for OAI.EntropyRateDimension.Typed.conditional_gain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:56:44.885277+00:00
-- url     : https://prove2.me/submissions/03b3a60d-e7f1-462f-a2c0-fd9dc43095e6

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/ScaleGain.lean:L82-L113
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Typed.conditional_gain. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_map_affine
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_mixture
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_finiteConv_mean_gain
import Theorems.Thm_OAI_EntropyRateDimension_System_selfSimilar_words
import Theorems.Thm_OAI_EntropyRateDimension_Typed_tail_append

-- ---- from OAI.MeasureTheory.SelfSimilar.Conditioning ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

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

theorem mass_eq_of_tag (p : α → ℝ) (tag : α → β) {a v : α} (h : tag a=tag v) :
    mass p tag a=mass p tag v := by simp only [mass,fiber,h]

theorem posterior_uncondition (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (v : α) :
    ∑ a, p a*posterior p tag a v=p v := by
  classical
  have he : ∀ a, p a*posterior p tag a v=
      if tag a=tag v then p a*p v/mass p tag v else 0 := by
    intro a
    by_cases h : tag a=tag v
    · simp only [posterior,ite_eq_left h.symm,ite_eq_left h,mass_eq_of_tag p tag h]
      ring
    · simp [posterior,h,Ne.symm h]
  simp_rw [he]
  rw [← Finset.sum_filter,← Finset.sum_div,← Finset.sum_mul]
  change mass p tag v*p v/mass p tag v=p v
  exact mul_div_cancel_left₀ _ (mass_pos p hp tag v).ne'

theorem law_smul_sum (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a : α)
    (f : α → ℝ) (F : ℝ → Measure ℝ) :
    (∑ x : (law p hp tag a f).support, ENNReal.ofReal ((law p hp tag a f).prob x) • F x)=
      ∑ v, ENNReal.ofReal (posterior p tag a v) • F (f v) := by
  classical
  rw [law,Law.smul_sum_ofObservable]
  simp only [posterior,apply_ite ENNReal.ofReal,ENNReal.ofReal_zero,ite_smul,zero_smul,
    ← Finset.sum_filter]
  rfl

theorem posterior_smul_uncondition (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β)
    (F : α → Measure ℝ) :
    (∑ a, ENNReal.ofReal (p a) • ∑ v, ENNReal.ofReal (posterior p tag a v) • F v)=
      ∑ v, ENNReal.ofReal (p v) • F v := by
  simp only [Finset.smul_sum,smul_smul,← ENNReal.ofReal_mul (hp _).le]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_smul,← ENNReal.ofReal_sum_of_nonneg
    (fun a _ => mul_nonneg (hp a).le (posterior_nonneg p hp tag a v)),posterior_uncondition p hp tag]

end EntropyRateDimension.FiniteCondition

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.TypedLaw ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

theorem tail_mean (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : S.SelfSimilar μ) (n : ℕ) :
    (∑ w : Fin n → α, ENNReal.ofReal (S.wordWeight w) • tail S tag μ w)=μ := by
  simp only [tail,prob_as_posterior]
  rw [posterior_smul_uncondition S.wordWeight (fun v => S.wordWeight_pos v)]
  exact (S.selfSimilar_words μ hμ n).symm

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

theorem scaledTail_mean (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : S.SelfSimilar μ) (a : ℝ) (n : ℕ) :
    (∑ w : Fin n → α, ENNReal.ofReal (S.wordWeight w) • scaledTail S tag μ a w)=
      μ.map (fun x => a*x) := by
  calc
    _ = (∑ w : Fin n → α, ENNReal.ofReal (S.wordWeight w) • tail S tag μ w).map
        (fun x => a*x) := by
      rw [Measure.map_finset_sum (show AEMeasurable (fun x : ℝ => a*x) _ from
        (measurable_const.mul measurable_id).aemeasurable)]
      simp only [Measure.map_smul (f := fun x : ℝ => a*x),scaledTail]
    _ = _ := by rw [tail_mean S tag μ hμ n]

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

-- ---- from OAI.MeasureTheory.SelfSimilar.ScaleGain ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension
open scoped BigOperators ENNReal
open MeasureTheory FairPairs MeasureEntropy

theorem scaled_band_distance (ν : Law) {a : ℝ} (ha : a ≠ 0) (L : ℤ)
    (e : ν.edges (L-⌈-Real.log |a|/Real.log 2⌉)) :
    (2 : ℝ)^(-L) ≤ |a*e.val.2-a*e.val.1| ∧
      |a*e.val.2-a*e.val.1| < 4*(2 : ℝ)^(-L) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hap : 0 < |a| := abs_pos.mpr ha
  let σ := -Real.log |a|/Real.log 2
  let c := ⌈σ⌉
  have hp : 0 < |a| *(2 : ℝ)^c := mul_pos hap (zpow_pos (by norm_num) _)
  have hlog : Real.log (|a| *(2 : ℝ)^c)=Real.log |a|+(c : ℝ)*Real.log 2 := by
    rw [Real.log_mul hap.ne' (zpow_ne_zero _ (by norm_num : (2 : ℝ)≠0)),Real.log_zpow]
  have hc1 := (div_le_iff₀ hl).mp (Int.le_ceil σ)
  have hc2 := Int.ceil_lt_add_one σ
  have hid : σ*Real.log 2= -Real.log |a| := div_mul_cancel₀ _ hl.ne'
  have ha1 : 1 ≤ |a| *(2 : ℝ)^c := by
    apply (Real.log_nonneg_iff hp).mp
    rw [hlog]
    dsimp only [c]
    linarith
  have ha2 : |a| *(2 : ℝ)^c < 2 := by
    apply (Real.log_lt_log_iff hp (by norm_num : (0 : ℝ)<2)).mp
    rw [hlog]
    have hh := mul_lt_mul_of_pos_right hc2 hl
    dsimp only [c]
    nlinarith
  have he := (Finset.mem_filter.mp e.property).2
  have hxy : 0 < e.val.2-e.val.1 := sub_pos.mpr he.1
  have habs : |a*e.val.2-a*e.val.1|=|a| *(e.val.2-e.val.1) := by
    rw [← mul_sub,abs_mul,abs_of_pos hxy]
  have hz1 : (2 : ℝ)^(-(L-c))=(2 : ℝ)^c*(2 : ℝ)^(-L) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ)≠0)]
    congr 1
    ring
  have hz2 : (2 : ℝ)^(1-(L-c))=2*((2 : ℝ)^c*(2 : ℝ)^(-L)) := by
    rw [show 1-(L-c)=1+(-(L-c)) by ring,zpow_add₀ (by norm_num : (2 : ℝ)≠0),zpow_one,hz1]
  change _ ∧ (2 : ℝ)^(-(L-c)) ≤ _ ∧ _ < (2 : ℝ)^(1-(L-c)) at he
  rw [hz1,hz2] at he
  rw [habs]
  have hr : 0 < (2 : ℝ)^(-L) := zpow_pos (by norm_num) _
  have hlow := mul_le_mul_of_nonneg_left he.2.1 hap.le
  have hupp := mul_lt_mul_of_pos_left he.2.2 hap
  have hlow' := mul_le_mul_of_nonneg_right ha1 hr.le
  have hupp' := mul_lt_mul_of_pos_right ha2 (by positivity : 0 < 2*(2 : ℝ)^(-L))
  constructor <;> nlinarith

theorem distance_window_bounds {r v : ℝ} (hr : 0 < r) (hv : r ≤ v) (hv4 : v < 4*r)
    {M : ℕ} (hM : 4 < M) :
    r/M < v ∧ v < ((M*M : ℕ) : ℝ)*(r/M) ∧
      (r/M)/v+v/(((M*M : ℕ) : ℝ)*(r/M)) ≤ 5/(M : ℝ) := by
  have hMR : (4 : ℝ)<M := by exact_mod_cast hM
  have hMp : (0 : ℝ)<M := by linarith
  have hvp : 0 < v := hr.trans_le hv
  have hid : ((M*M : ℕ) : ℝ)*(r/M)=(M : ℝ)*r := by push_cast; field_simp
  rw [hid]
  refine ⟨?_,?_,?_⟩
  · apply (div_lt_iff₀ hMp).mpr
    nlinarith
  · nlinarith
  · have h1 : (r/M)/v ≤ 1/(M : ℝ) := by
      apply (div_le_div_iff₀ hvp hMp).mpr
      rw [div_mul_cancel₀ _ hMp.ne']
      simpa only [one_mul] using hv
    have h2 : v/((M : ℝ)*r) ≤ 4/(M : ℝ) := by
      apply (div_le_div_iff₀ (mul_pos hMp hr) hMp).mpr
      nlinarith
    have hh : 1/(M : ℝ)+4/(M : ℝ)=5/(M : ℝ) := by ring
    linarith

namespace Typed
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem conditional_gain (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) {δ : ℝ}
    (hδ : ∀ v, 0 < v → δ ≤ deficit μ v) {M : ℕ} (hM : 4 < M)
    (he : 5/(M : ℝ)*Real.log 2 ≤ δ/2)
    {j n : ℕ} (u : Fin j → α) (w : Fin n → α) (t : ℕ) (L : ℤ) :
    δ/2*capacity (law S tag w) (L-⌈S.wordDepth u⌉) ≤
      ∑ z : Fin t → α, S.wordWeight z*
        (window (scaledTail S tag μ (S.completeMap u).1 (Fin.append w z))
          ((2 : ℝ)^(-L)/M) (((M*M : ℕ) : ℝ)*((2 : ℝ)^(-L)/M))-
        window (scaledTail S tag μ ((S.completeMap u).1*(S.completeMap w).1) z)
          ((2 : ℝ)^(-L)/M) (((M*M : ℕ) : ℝ)*((2 : ℝ)^(-L)/M))) := by
  have ha : (S.completeMap u).1≠0 := S.completeMap_slope_ne_zero u
  have hb : (S.completeMap u).1*(S.completeMap w).1≠0 := mul_ne_zero ha (S.completeMap_slope_ne_zero w)
  have hMp : (0 : ℝ)<M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hs : 0 < (2 : ℝ)^(-L)/(M : ℝ) := div_pos (zpow_pos (by norm_num) _) hMp
  have hv (e : (law S tag w).edges (L-⌈S.wordDepth u⌉)) :=
    scaled_band_distance (law S tag w) ha L e
  have hd (e : (law S tag w).edges (L-⌈S.wordDepth u⌉)) :=
    distance_window_bounds (zpow_pos (by norm_num : (0 : ℝ)<2) (-L)) (hv e).1 (hv e).2 hM
  have hg := finiteConv_mean_gain (law S tag w) (S.completeMap u).1
    ((S.completeMap u).1*(S.completeMap w).1) hb μ hc
    (scaledTail S tag μ ((S.completeMap u).1*(S.completeMap w).1))
    (fun z : Fin t → α => scaledTail_compact S tag μ hc _ z)
    S.wordWeight (fun z => (S.wordWeight_pos z).le) (S.wordWeight_sum t)
    (scaledTail_mean S tag μ hμ _ t).symm hδ hs (by positivity : 0 < M*M)
    (L-⌈S.wordDepth u⌉) (fun e => ⟨(hd e).1,(hd e).2.1⟩)
    (fun e => (mul_le_mul_of_nonneg_right (hd e).2.2 (Real.log_pos (by norm_num : (1 : ℝ)<2)).le).trans he)
  simp only [← scaledTail_append S tag hr] at hg
  convert hg using 1
  ring

end Typed
end EntropyRateDimension

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
open scoped BigOperators ENNReal
open MeasureTheory FairPairs MeasureEntropy


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.Typed.conditional_gain.{uα,uβ} := @_root_.OAI.EntropyRateDimension.Typed.conditional_gain.{uα,uβ}
