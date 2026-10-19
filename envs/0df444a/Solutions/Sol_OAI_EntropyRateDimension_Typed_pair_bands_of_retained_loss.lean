-- Prove2me | solution 1 for OAI.EntropyRateDimension.Typed.pair_bands_of_retained_loss
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:50:27.696477+00:00
-- url     : https://prove2.me/submissions/3e682028-c2eb-46de-ae58-5875d0bd1fb1

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/PairBands.lean:L82-L115
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Typed.pair_bands_of_retained_loss. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_DigitSumset_card_sumset_le
import Theorems.Thm_OAI_EntropyRateDimension_FairPairs_pair_bound_natural
import Theorems.Thm_OAI_EntropyRateDimension_exists_nat_log_small

-- ---- from OAI.MeasureTheory.SelfSimilar.FairPairs ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FairPairs

theorem edge_mem_left {ν : Law} {ℓ : ℤ} (e : ν.edges ℓ) : e.val.1 ∈ ν.support := by
  classical
  exact (Finset.mem_product.mp (Finset.mem_filter.mp e.property).1).1

theorem edge_mem_right {ν : Law} {ℓ : ℤ} (e : ν.edges ℓ) : e.val.2 ∈ ν.support := by
  classical
  exact (Finset.mem_product.mp (Finset.mem_filter.mp e.property).1).2

theorem incident_sum {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) :
    ∑ x ∈ ν.support, incident w x = ∑ e, w e := by
  classical
  simp only [incident]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, edge_mem_left e, edge_mem_right e, ite_true]
  ring

theorem feasible_zero (ν : Law) (ℓ : ℤ) : Feasible (ν := ν) (ℓ := ℓ) (fun _ => 0) := by
  constructor
  · simp
  · intro x hx
    simpa [incident] using (ν.prob_pos x hx).le

theorem total_le_one {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w) :
    ∑ e, w e ≤ 1 := by
  rw [← incident_sum w, ← ν.prob_sum]
  exact Finset.sum_le_sum hw.2

theorem totals_bddAbove (ν : Law) (ℓ : ℤ) :
    BddAbove {t : ℝ | ∃ w : ν.edges ℓ → ℝ, Feasible w ∧ ∑ e, w e = t} := by
  refine ⟨1, ?_⟩
  rintro t ⟨w, hw, rfl⟩
  exact total_le_one hw

theorem capacity_nonneg (ν : Law) (ℓ : ℤ) : 0 ≤ capacity ν ℓ := by
  apply le_csSup (totals_bddAbove ν ℓ)
  exact ⟨(fun _ => 0), feasible_zero ν ℓ, by simp⟩

end FairPairs

end EntropyRateDimension

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.SumsetBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uβ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FairPairs

open FiniteEntropy

theorem Law.support_nonempty (ν : Law) : ν.support.Nonempty := by
  by_contra h
  have := ν.prob_sum
  rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at this
  norm_num at this

end FairPairs

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.UpperBound ----
namespace OAI

universe uι uM

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

theorem completeMap_cons (S : System ι) {n : ℕ} (i : ι) (w : Fin n → ι) :
    S.completeMap (Fin.cons i w) = (S.ratio i*(S.completeMap w).1,
      S.ratio i*(S.completeMap w).2+S.offset i) := by
  simp only [completeMap,List.ofFn_cons,wordAffine]

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

-- ---- from OAI.MeasureTheory.SelfSimilar.RetainedLoss ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory

end EntropyRateDimension.MeasureEntropy

namespace EntropyRateDimension.Typed
open FairPairs MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]

theorem fineScale_pos (A : ℝ) (n : ℕ) : 0 < fineScale A n := zpow_pos (by norm_num) _

end EntropyRateDimension.Typed

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.TypedSumset ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open FairPairs FiniteCondition
open scoped BigOperators
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

omit [DecidableEq β] in

theorem translation_coefficients (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} (w : Fin n → α) :
    ∃ R : Fin n → ℝ, ∀ v, tagWord tag v=tagWord tag w →
      (S.completeMap v).2=∑ j, R j*S.offset (v j) := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0,fun v _ => ?_⟩
    simp [System.completeMap,System.wordAffine]
  | succ n ih =>
    obtain ⟨R,hR⟩ := ih (fun j => w j.succ)
    refine ⟨Fin.cons 1 (fun j => S.ratio (w 0)*R j),fun v hv => ?_⟩
    have ht : tagWord tag (fun j => v j.succ)=tagWord tag (fun j => w j.succ) :=
      funext (fun j => congrFun hv j.succ)
    have hr0 := hr (v 0) (w 0) (congrFun hv 0)
    conv_lhs => rw [← Fin.cons_self_tail v,S.completeMap_cons]
    simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,one_mul]
    rw [hR (Fin.tail v) ht,hr0]
    simp only [Finset.mul_sum,mul_assoc,Fin.tail]
    ring

theorem support_digit_representation (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} (w : Fin n → α) :
    ∃ R : Fin n → ℝ, ∀ x ∈ (law S tag w).support,
      ∃ v : Fin n → α, x=∑ j, R j*S.offset (v j) := by
  obtain ⟨R,hR⟩ := translation_coefficients S tag hr w
  refine ⟨R,fun x hx => ?_⟩
  change x ∈ (fiber (tagWord tag) w).image (fun v => (S.completeMap v).2) at hx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  exact ⟨v,hR v (Finset.mem_filter.mp hv).2⟩

theorem sumset_card_bound (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} (w : Fin n → α) (k : ℕ) :
    ((law S tag w).sumset k).card ≤ (k+1)^(n*Fintype.card α) := by
  obtain ⟨R,hR⟩ := support_digit_representation S tag hr w
  simpa only [Fintype.card_fin, DigitSumset.sumset, Law.sumset] using
    DigitSumset.card_sumset_le (law S tag w).support (fun j a => R j*S.offset a) hR k

theorem sumset_log_bound (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} (w : Fin n → α) (k : ℕ) :
    Real.log ((law S tag w).sumset k).card ≤ (n : ℝ)*Fintype.card α*Real.log (k+1) := by
  classical
  obtain ⟨x,hx⟩ := (law S tag w).support_nonempty
  have hs : ((law S tag w).sumset k).Nonempty :=
    Finset.image_nonempty.mpr (Finset.univ_nonempty_iff.mpr ⟨fun _ : Fin k => ⟨x,hx⟩⟩)
  have hb : (((law S tag w).sumset k).card : ℝ) ≤ ((k : ℝ)+1)^(n*Fintype.card α) := by
    exact_mod_cast sumset_card_bound S tag hr w k
  have hh := Real.log_le_log (show (0 : ℝ)<((law S tag w).sumset k).card by
    exact_mod_cast Finset.card_pos.mpr hs) hb
  rw [Real.log_pow,Nat.cast_mul] at hh
  exact hh

end EntropyRateDimension.Typed

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.PairBands ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension
open scoped BigOperators Topology
open Filter

namespace Typed
open FairPairs
variable {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α] [DecidableEq β]

omit [Nonempty α] in
theorem fineScale_band_condition (A : ℝ) (n : ℕ) (ℓ : ℤ) :
    (2 : ℝ)^(-ℓ) ≤ 2*fineScale A n ↔ bandStart A n ≤ ℓ := by
  have he : 2*fineScale A n=(2 : ℝ)^(1-⌈A*n⌉) := by
    rw [sub_eq_add_neg,zpow_add₀ (by norm_num : (2 : ℝ)≠0),zpow_one]
    rfl
  rw [he,zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ)<2)]
  dsimp only [bandStart]
  omega

omit [Nonempty α] in
theorem exists_band_pair_bound (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (A : ℝ) (n k : ℕ) (hk : 1 ≤ k) :
    ∃ B : ℤ, bandStart A n ≤ B ∧ ∀ w : Fin n → α,
      (k : ℝ)*entropyLoss S tag w (fineScale A n) ≤
        (n : ℝ)*Fintype.card α*Real.log (k+1)+60000*k^4*Real.log 2*
          ∑ ℓ ∈ Finset.Icc (bandStart A n) B, capacity (law S tag w) ℓ := by
  classical
  let J := insert (bandStart A n) (Finset.univ.biUnion (fun w : Fin n → α => (law S tag w).bandSupport))
  have hJ : J.Nonempty := Finset.insert_nonempty _ _
  let B := J.max' hJ
  have hab : bandStart A n ≤ B := Finset.le_max' J _ (Finset.mem_insert_self _ _)
  refine ⟨B,hab,fun w => ?_⟩
  have hh := pair_bound_natural (law S tag w) k hk (fineScale A n) (fineScale_pos A n)
  have hs : ∑ ℓ ∈ (law S tag w).bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ 2*fineScale A n),
      capacity (law S tag w) ℓ ≤
      ∑ ℓ ∈ Finset.Icc (bandStart A n) B, capacity (law S tag w) ℓ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ℓ hℓ
      obtain ⟨hℓ,hrℓ⟩ := Finset.mem_filter.mp hℓ
      apply Finset.mem_Icc.mpr
      refine ⟨(fineScale_band_condition A n ℓ).mp hrℓ,?_⟩
      apply Finset.le_max' J ℓ
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨w,Finset.mem_univ _,hℓ⟩)
    · intro ℓ _ _
      exact capacity_nonneg _ _
  have hc : 0 ≤ 60000*(k : ℝ)^4*Real.log 2 := by positivity
  have hl := sumset_log_bound S tag hr w k
  have hid : entropyLoss S tag w (fineScale A n)=
      FiniteEntropy.entropy (law S tag w).support (law S tag w).prob-
        FiniteEntropy.observableEntropy (law S tag w).support (law S tag w).prob (fun x => ⌊x/fineScale A n⌋) := by
    dsimp only [entropyLoss,Law.shannonEntropy,Law.gridEntropy]
    field_simp
  rw [hid]
  exact hh.trans (add_le_add hl (mul_le_mul_of_nonneg_left hs hc))

omit [Nonempty α] in
theorem pair_bands_of_retained_loss (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (A A' : ℝ) {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (he : ∀ n, N ≤ n → ε*n ≤ retainedLoss S tag A A' n) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, N ≤ n → ∃ B : ℤ, bandStart A n ≤ B ∧
      c*n ≤ pairBudget S tag A' (bandStart A n) B n := by
  classical
  obtain ⟨k,hk,hl⟩ := exists_nat_log_small hε (Fintype.card α)
  let K : ℝ := Fintype.card α*Real.log (k+1)
  let C : ℝ := 60000*k^4*Real.log 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hgap : 0 < ε*k-K := sub_pos.mpr hl
  refine ⟨(ε*k-K)/C,div_pos hgap hC,fun n hn => ?_⟩
  obtain ⟨B,hB,hb⟩ := exists_band_pair_bound S tag hr A n k hk
  refine ⟨B,hB,?_⟩
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k; linarith))
  have hp : (k : ℝ)*retainedLoss S tag A A' n ≤ (n : ℝ)*K+C*pairBudget S tag A' (bandStart A n) B n := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun (w : Fin n → α) _ =>
      show (k : ℝ)*(if S.wordDepth w ≤ A'*n then S.wordWeight w*entropyLoss S tag w (fineScale A n) else 0) ≤
        S.wordWeight w*((n : ℝ)*K)+C*(if S.wordDepth w ≤ A'*n then S.wordWeight w*
          ∑ ℓ ∈ Finset.Icc (bandStart A n) B, capacity (law S tag w) ℓ else 0) from by
        split_ifs
        · have h := mul_le_mul_of_nonneg_left (hb w) (S.wordWeight_pos w).le
          dsimp only [K,C]
          nlinarith
        · simp only [mul_zero,add_zero]
          exact mul_nonneg (S.wordWeight_pos w).le (mul_nonneg (Nat.cast_nonneg _) hK))
    simpa only [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.sum_mul,
      S.wordWeight_sum,one_mul,retainedLoss,pairBudget] using hh
  have hh := mul_le_mul_of_nonneg_left (he n hn) (by positivity : (0 : ℝ)≤k)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hC).mpr
  nlinarith

end Typed
end EntropyRateDimension

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
open scoped BigOperators Topology
open Filter
open FairPairs


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.Typed.pair_bands_of_retained_loss.{uα,uβ} := @_root_.OAI.EntropyRateDimension.Typed.pair_bands_of_retained_loss.{uα,uβ}
