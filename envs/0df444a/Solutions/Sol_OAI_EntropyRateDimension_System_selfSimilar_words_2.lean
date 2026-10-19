-- Prove2me | solution 2 for OAI.EntropyRateDimension.System.selfSimilar_words
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:20:47.406561+00:00
-- url     : https://prove2.me/submissions/521d41d0-3551-4a35-a34e-1bb29365336b

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/UpperBound.lean:L40-L63
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.System.selfSimilar_words. The node keeps its source
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

-- ---- from OAI.MeasureTheory.SelfSimilar.Basic ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace System
variable {ι : Type uι} [Fintype ι]

theorem affine_continuous (S : System ι) (i : ι) : Continuous (S.affine i) := by
  unfold affine
  fun_prop

end System

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

end System

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

theorem sum_words_cons {M : Type uM} [AddCommMonoid M] {n : ℕ}
    (f : (Fin (n+1) → ι) → M) :
    (∑ w, f w) = ∑ i, ∑ w : Fin n → ι, f (Fin.cons i w) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => ι)).sum_comp f,Fintype.sum_prod_type]
  rfl

theorem completeMap_cons (S : System ι) {n : ℕ} (i : ι) (w : Fin n → ι) :
    S.completeMap (Fin.cons i w) = (S.ratio i*(S.completeMap w).1,
      S.ratio i*(S.completeMap w).2+S.offset i) := by
  simp only [completeMap,List.ofFn_cons,wordAffine]

theorem wordWeight_cons (S : System ι) {n : ℕ} (i : ι) (w : Fin n → ι) :
    S.wordWeight (Fin.cons i w) = S.weight i*S.wordWeight w := by
  simp only [wordWeight,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem wordMap_cons (S : System ι) {n : ℕ} (i : ι) (w : Fin n → ι) :
    S.wordMap (Fin.cons i w) = S.affine i ∘ S.wordMap w := by
  funext x
  simp only [wordMap,completeMap_cons,affine,Function.comp_apply]
  ring

theorem selfSimilar_words (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ) (n : ℕ) :
    μ = ∑ w : Fin n → ι, ENNReal.ofReal (S.wordWeight w) • μ.map (S.wordMap w) := by
  classical
  induction n with
  | zero =>
    have hm : S.wordMap (default : Fin 0 → ι) = id := by
      funext x
      simp [wordMap,completeMap,wordAffine]
    simp [wordWeight,hm]
  | succ n ih =>
    rw [sum_words_cons]
    calc
      μ = ∑ i, ENNReal.ofReal (S.weight i) • μ.map (S.affine i) := hμ
      _ = ∑ i, ∑ w : Fin n → ι,
          ENNReal.ofReal (S.wordWeight (Fin.cons i w)) • μ.map (S.wordMap (Fin.cons i w)) := by
        apply Finset.sum_congr rfl
        intro i _
        conv_lhs => rw [ih]
        rw [Measure.map_finset_sum (S.affine_continuous i).measurable.aemeasurable,Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro w _
        rw [Measure.map_smul _ _ (S.affine i),
          smul_smul,wordWeight_cons,ENNReal.ofReal_mul (S.weight_nonneg i),
          Measure.map_map (S.affine_continuous i).measurable (S.wordMap_measurable w),wordMap_cons]

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

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.System.selfSimilar_words.{uι} := @_root_.OAI.EntropyRateDimension.System.selfSimilar_words.{uι}
