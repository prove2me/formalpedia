-- Prove2me | solution 1 for OAI.EntropyRateDimension.Coding.exponent_symbol_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T15:28:37.380764+00:00
-- url     : https://prove2.me/submissions/a33ae1e6-27c5-4b1d-b581-a15357b07a97

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/UpperBound.lean:L167-L183
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Coding.exponent_symbol_entropy_bound. The node keeps its source
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

-- ---- from OAI.MeasureTheory.SelfSimilar.Basic ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace System
variable {ι : Type uι} [Fintype ι]

theorem lyapunov_pos [Nonempty ι] (S : System ι) : 0 < S.lyapunov := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [lyapunov, neg_pos]
  apply Finset.sum_neg
  · intro i _
    exact mul_neg_of_pos_of_neg (S.weight_pos i)
      (div_neg_of_neg_of_pos (Real.log_neg (S.ratio_pos i) (S.ratio_lt_one i)) hlog)
  · exact Finset.univ_nonempty

end System

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

end System

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.BallLimits ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter
open EntropyRateDimension.Bernoulli EntropyRateDimension.ErgodicAux
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_1
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_1
omit [Nonempty ι] in
theorem head_integral (S : System ι) (f : ι → ℝ) :
    (∫ ω, f (ω 0) ∂addressMeasure S) = ∑ i, S.weight i * f i := by
  have he : (addressMeasure S).map (fun ω => ω 0) = symbolMeasure S :=
    Measure.infinitePi_map_eval _ _
  have hm := measurable_of_finite f
  rw [← integral_map (measurable_pi_apply 0).aemeasurable hm.aestronglyMeasurable,he]
  unfold symbolMeasure
  rw [integral_finsetSum_measure (fun i _ =>
    (show Integrable f (Measure.dirac i) from Integrable.of_finite).smul_measure (by simp))]
  simp only [integral_smul_measure,integral_dirac,smul_eq_mul,
    ENNReal.toReal_ofReal (S.weight_nonneg _)]

end EntropyRateDimension.Coding

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.UpperBound ----
namespace OAI

universe uι uM

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

end EntropyRateDimension.System

namespace EntropyRateDimension.Coding
open MeasureTheory
open scoped BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_5
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_5
theorem exponent_symbol_entropy_bound (S : System ι) :
    exponent S * S.lyapunov * Real.log 2 ≤ ∑ i, Real.negMulLog (S.weight i) := by
  have hc : 0 ≤ ∫ ω, clippedLimit S ω ∂addressMeasure S :=
    integral_nonneg (fun ω => le_max_left 0 _)
  have hw : (∫ ω, weightObs S ω ∂addressMeasure S) =
      ∑ i, Real.negMulLog (S.weight i) := by
    change (∫ ω, -Real.log (S.weight (ω 0)) ∂addressMeasure S) = _
    rw [head_integral S (fun i => -Real.log (S.weight i))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Real.negMulLog]
    ring
  have he : exponent S*S.lyapunov*Real.log 2=infoRate S := by
    unfold exponent
    field_simp [S.lyapunov_pos.ne', (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne']
  rw [he,infoRate,hw]
  linarith

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
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Coding
open MeasureTheory
open scoped BigOperators
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_5
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_5


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.Coding.exponent_symbol_entropy_bound.{uι} := @_root_.OAI.EntropyRateDimension.Coding.exponent_symbol_entropy_bound.{uι}
