-- Prove2me | solution 1 for OAI.EntropyRateDimension.Extensions.cylinderRatio_power_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T15:55:03.59045+00:00
-- url     : https://prove2.me/submissions/c76af37a-e57e-4813-8dab-272bc8a2b8b2

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/Attractor.lean:L83-L103
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Extensions.cylinderRatio_power_sum. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Attractor

-- ---- from OAI.MeasureTheory.SelfSimilar.Attractor ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

universe uι

open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory Set Filter

namespace EntropyRateDimension.Extensions

variable {ι : Type uι} [Fintype ι]

/-- Exact finite-word partition function, valid whether or not cylinders overlap. -/
theorem cylinderRatio_power_sum [Nonempty ι] (S : System ι) {s : ℝ} (hs : 0 ≤ s)
    (hroot : ∑ i, |S.ratio i| ^ s = 1) (n : ℕ) :
    ∑ w : Fin n → ι, (cylinderRatio S w : ℝ≥0∞) ^ s = 1 := by
  classical
  have hletters : ∑ i, (‖S.ratio i‖₊ : ℝ≥0∞) ^ s = 1 := by
    have he : ∀ i, (‖S.ratio i‖₊ : ℝ≥0∞) ^ s =
        ENNReal.ofReal (|S.ratio i| ^ s) := by
      intro i
      rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hs]
      simp only [ENNReal.coe_nnreal_eq, coe_nnnorm, Real.norm_eq_abs]
    simp_rw [he]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _), hroot]
    simp
  have he : ∀ w : Fin n → ι, (cylinderRatio S w : ℝ≥0∞) ^ s =
      ∏ j, (‖S.ratio (w j)‖₊ : ℝ≥0∞) ^ s := by
    intro w
    simp only [cylinderRatio, ENNReal.ofNNReal_finsetProd, ENNReal.prod_rpow_of_nonneg hs]
  simp_rw [he]
  simpa [hletters] using
    (Fintype.prod_sum (fun (_ : Fin n) (i : ι) => (‖S.ratio i‖₊ : ℝ≥0∞) ^ s)).symm

end EntropyRateDimension.Extensions

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Extensions
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory Set Filter


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.Extensions.cylinderRatio_power_sum.{uι} := @_root_.OAI.EntropyRateDimension.Extensions.cylinderRatio_power_sum.{uι}
