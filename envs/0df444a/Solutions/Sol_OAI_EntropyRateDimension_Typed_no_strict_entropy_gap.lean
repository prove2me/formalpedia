-- Prove2me | solution 1 for OAI.EntropyRateDimension.Typed.no_strict_entropy_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:15:04.445035+00:00
-- url     : https://prove2.me/submissions/b238847f-c1a0-4b4e-a87c-aedfa744a529

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/EntropyGap.lean:L12-L63
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Typed.no_strict_entropy_gap. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_System_selfSimilar_compact
import Theorems.Thm_OAI_EntropyRateDimension_System_uniform_nonsaturation_of_entropy_bound
import Theorems.Thm_OAI_EntropyRateDimension_Typed_count_pair_budget_le
import Theorems.Thm_OAI_EntropyRateDimension_Typed_exists_common_horizon
import Theorems.Thm_OAI_EntropyRateDimension_Typed_pair_bands_of_retained_loss
import Theorems.Thm_OAI_EntropyRateDimension_Typed_retained_loss_linear
import Theorems.Thm_OAI_EntropyRateDimension_Typed_select_separated_bands

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

end EntropyRateDimension.Typed

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

theorem exists_depth_bound (S : System α) : ∃ D : ℝ, 0 < D ∧ ∀ a, S.letterDepth a ≤ D := by
  let D := 1+∑ a, S.letterDepth a
  have hn : 0 ≤ ∑ a, S.letterDepth a := Finset.sum_nonneg (fun a _ => (S.letterDepth_pos a).le)
  refine ⟨D,by dsimp [D]; linarith,fun a => ?_⟩
  have hh := Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) => (S.letterDepth_pos a).le) (Finset.mem_univ a)
  dsimp [D]
  linarith

end EntropyRateDimension.System

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.EntropyGap ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy
open scoped BigOperators
variable {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]

theorem no_strict_entropy_gap (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    {d C A A' : ℝ} (hd : 0 ≤ d) (hd1 : d < 1) (hA : 0 < A)
    (hA' : S.lyapunov < A') (hAA : A' < A)
    (hb : ∀ s, 0 < s → s < 1 → averaged μ s ≤ d*Real.log (1/s)+C)
    (hgap : d*A*Real.log 2 < S.entropyRate*Real.log 2-Real.log (Fintype.card β)) : False := by
  classical
  obtain ⟨δ,hδ,hdef⟩ := S.uniform_nonsaturation_of_entropy_bound μ hμ hd1 hb
  obtain ⟨M,hM'⟩ := exists_nat_gt (max 4 (10*Real.log 2/δ))
  have hM : 4 < M := by exact_mod_cast (le_max_left _ _).trans_lt hM'
  have hMr : (0 : ℝ)<M := by exact_mod_cast (show 0 < M by omega)
  have he : 5/(M : ℝ)*Real.log 2 ≤ δ/2 := by
    have hh := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hM')
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    apply (mul_le_mul_iff_right₀ hMr).mp
    have heq : (5/(M : ℝ)*Real.log 2*2)*(M : ℝ)=10*Real.log 2 := by field_simp; ring
    nlinarith [heq]
  obtain ⟨ε,hε,N,_,hloss⟩ := retained_loss_linear S tag hr μ hμ hd hA hA' hb hgap
  obtain ⟨c,hc,hbands⟩ := pair_bands_of_retained_loss S tag hr A A' hε hloss
  obtain ⟨dmax,_,hdmax⟩ := S.exists_depth_bound
  obtain ⟨D,hD'⟩ := exists_nat_gt (max 1 dmax)
  have hD : 1 ≤ D := by exact_mod_cast ((le_max_left _ _).trans_lt hD').le
  have hdD : ∀ v, S.letterDepth v ≤ (D : ℝ) := fun v => (hdmax v).trans ((le_max_right _ _).trans_lt hD').le
  have hcoef : 0 < δ/2*c := mul_pos (div_pos hδ (by norm_num)) hc
  obtain ⟨q,hq⟩ := exists_nat_gt ((2*(D : ℝ)*Real.log ((M*M : ℕ) : ℝ))/(δ/2*c))
  obtain ⟨n,B,hn,ha,hbudget,hsep⟩ := select_separated_bands S tag hA hAA hbands q
  obtain ⟨H,hH,hdvd,hBH⟩ := exists_common_horizon n hn B
  let K : Fin q → ℕ := fun i => H/n i
  have hkn (i : Fin q) : K i*n i=H := Nat.div_mul_cancel (hdvd i)
  obtain ⟨R,hR,hcompact⟩ := S.selfSimilar_compact μ hμ
  have hcomp : CompactlyCarried μ := ⟨R,hR.le,hcompact⟩
  have hcount := count_pair_budget_le S tag hr μ hμ hcomp hdef hM he hD hdD n K
    (fun i => bandStart A (n i)) B A' hkn ha hBH hsep
  have hsum : (q : ℝ)*(c*H) ≤ ∑ i, (K i : ℝ)*pairBudget S tag A' (bandStart A (n i)) (B i) (n i) := by
    calc
      _ = ∑ _i : Fin q, c*(H : ℝ) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        have hi := mul_le_mul_of_nonneg_left (hbudget i) (Nat.cast_nonneg (K i))
        have hnH : (K i : ℝ)*(n i : ℝ)=(H : ℝ) := by exact_mod_cast hkn i
        nlinarith
  have hlim : (δ/2*c)*(q : ℝ) ≤ 2*(D : ℝ)*Real.log ((M*M : ℕ) : ℝ) := by
    apply (mul_le_mul_iff_right₀ (by exact_mod_cast hH : (0 : ℝ)<H)).mp
    calc
      _ = δ/2*((q : ℝ)*(c*H)) := by ring
      _ ≤ δ/2*(∑ i, (K i : ℝ)*pairBudget S tag A' (bandStart A (n i)) (B i) (n i)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ _ := by simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_assoc,mul_comm,mul_left_comm] using hcount
  have hq' := (div_lt_iff₀ hcoef).mp hq
  nlinarith

end EntropyRateDimension.Typed

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy
open scoped BigOperators


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.Typed.no_strict_entropy_gap.{uα,uβ} := @_root_.OAI.EntropyRateDimension.Typed.no_strict_entropy_gap.{uα,uβ}
