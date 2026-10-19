-- Prove2me | solution 2 for OAI.EntropyRateDimension.System.wordAverage_segment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:33:16.561988+00:00
-- url     : https://prove2.me/submissions/d4bf8eeb-de4f-419e-981d-15e8f6fae379

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/WordAverage.lean:L48-L65
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.System.wordAverage_segment. The node keeps its source
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

-- ---- from OAI.MeasureTheory.SelfSimilar.WordAverage ----
namespace OAI

universe uι uα

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

theorem wordAverage_append (S : System α) (m n : ℕ) (f : List α → ℝ) :
    S.wordAverage (m+n) f =
      ∑ u : Fin m → α, S.wordWeight u*∑ v : Fin n → α, S.wordWeight v*f (List.ofFn u++List.ofFn v) := by
  rw [wordAverage,sum_words_append]
  simp only [wordWeight_append,List.ofFn_fin_append,Finset.mul_sum,mul_assoc]

theorem wordAverage_segment (S : System α) {H j n : ℕ} (hH : j+n ≤ H) (f : List α → ℝ) :
    S.wordAverage H (fun W => f ((W.drop j).take n))=S.wordAverage n f := by
  classical
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hH
  rw [wordAverage_append]
  rw [sum_words_append j n]
  simp only [wordWeight_append,List.ofFn_fin_append]
  have he (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
      (((List.ofFn u++List.ofFn w)++List.ofFn z).drop j).take n=List.ofFn w := by
    have h1 : ((List.ofFn u++List.ofFn w)++List.ofFn z).drop j=List.ofFn w++List.ofFn z := by
      rw [List.append_assoc]
      simpa only [List.length_ofFn] using (List.drop_append_length (l₁ := List.ofFn u) (l₂ := List.ofFn w++List.ofFn z))
    rw [h1]
    simpa only [List.length_ofFn] using (List.take_append_length (l₁ := List.ofFn w) (l₂ := List.ofFn z))
  simp_rw [he,← Finset.sum_mul,S.wordWeight_sum,one_mul]
  simp only [mul_assoc,← Finset.mul_sum]
  rw [← Finset.sum_mul,S.wordWeight_sum,one_mul]
  rfl

end EntropyRateDimension.System

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
open scoped BigOperators


theorem solution.{uα} : type_of% @_root_.OAI.EntropyRateDimension.System.wordAverage_segment.{uα} := @_root_.OAI.EntropyRateDimension.System.wordAverage_segment.{uα}
