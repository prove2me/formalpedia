-- Prove2me | solution 1 for OAI.EntropyRateDimension.Extensions.word_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T15:37:21.366+00:00
-- url     : https://prove2.me/submissions/c4f8cc5c-db8c-42b5-9a22-11edf5a22d73

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/NoOverlaps.lean:L150-L168
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Extensions.word_entropy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Model
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RetainedLoss__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairBands__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowCount__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowGain__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Main__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_NoOverlaps

-- ---- from OAI.MeasureTheory.SelfSimilar.UpperBound ----
namespace OAI

universe uι uM

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

theorem sum_words_cons {M : Type uM} [AddCommMonoid M] {n : ℕ}
    (f : (Fin (n+1) → ι) → M) :
    (∑ w, f w) = ∑ i, ∑ w : Fin n → ι, f (Fin.cons i w) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => ι)).sum_comp f,Fintype.sum_prod_type]
  rfl

theorem wordWeight_cons (S : System ι) {n : ℕ} (i : ι) (w : Fin n → ι) :
    S.wordWeight (Fin.cons i w) = S.weight i*S.wordWeight w := by
  simp only [wordWeight,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem wordWeight_expect_sum (S : System ι) (f : ι → ℝ) (n : ℕ) :
    (∑ w : Fin n → ι, S.wordWeight w * ∑ j, f (w j)) =
      (n : ℝ)*∑ i, S.weight i*f i := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_words_cons]
    simp only [wordWeight_cons,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,
      mul_add,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,
      S.wordWeight_sum,one_mul,ih,S.weight_sum]
    push_cast
    ring

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

-- ---- from OAI.MeasureTheory.SelfSimilar.NoOverlaps ----
namespace OAI

universe uι uα

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension.Extensions

variable {ι : Type uι} [Fintype ι]

/-- Native product entropy of the symbol word; no random-walk entropy hypothesis. -/
theorem word_entropy (S : System ι) (n : ℕ) :
    FiniteEntropy.entropy Finset.univ (S.wordWeight (n := n)) =
      (n : ℝ) * symbolEntropy S := by
  classical
  have hlog (w : Fin n → ι) :
      Real.log (S.wordWeight w) = ∑ j, Real.log (S.weight (w j)) := by
    unfold System.wordWeight
    exact Real.log_prod (fun j _ => (S.weight_pos (w j)).ne')
  calc
    FiniteEntropy.entropy Finset.univ (S.wordWeight (n := n)) =
        -(∑ w : Fin n → ι, S.wordWeight w * ∑ j, Real.log (S.weight (w j))) := by
      simp only [FiniteEntropy.entropy, Real.negMulLog, hlog,
        neg_mul, Finset.sum_neg_distrib]
    _ = -((n : ℝ) * ∑ i, S.weight i * Real.log (S.weight i)) := by
      exact congrArg (fun x : ℝ => -x)
        (S.wordWeight_expect_sum (fun i => Real.log (S.weight i)) n)
    _ = (n : ℝ) * symbolEntropy S := by
      simp only [symbolEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, mul_neg]

end EntropyRateDimension.Extensions

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Extensions
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.Extensions.word_entropy.{uι} := @_root_.OAI.EntropyRateDimension.Extensions.word_entropy.{uι}
