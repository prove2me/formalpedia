-- Prove2me | solution 1 for OAI.EntropyRateDimension.Extensions.attractor_subset_cylinders
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T15:57:55.759012+00:00
-- url     : https://prove2.me/submissions/7685beed-1043-4bad-90c0-785ff4cf58db

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/Attractor.lean:L105-L123
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Extensions.attractor_subset_cylinders. The node keeps its source
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

-- ---- from OAI.MeasureTheory.SelfSimilar.Coding ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
namespace EntropyRateDimension
namespace Coding
open Filter Set
open scoped Topology

variable {ι : Type uι} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem slope_shift (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    slope S ω (n+1) = S.ratio (ω 0) * slope S (shift ω) n := by
  simp only [slope, Finset.prod_range_succ', shift]
  ring

theorem point_shift (S : System ι) (ω : ℕ → ι) :
    point S ω = S.affine (ω 0) (point S (shift ω)) := by
  rw [point, (term_summable S ω).tsum_eq_zero_add]
  have he : (fun n => term S ω (n+1)) = fun n => S.ratio (ω 0)*term S (shift ω) n := by
    funext n
    simp only [term, slope_shift, shift]
    ring
  rw [he, tsum_mul_left]
  simp only [term, slope_zero, one_mul, System.affine, point]
  ring

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

end Coding
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

theorem wordMap_cons (S : System ι) {n : ℕ} (i : ι) (w : Fin n → ι) :
    S.wordMap (Fin.cons i w) = S.affine i ∘ S.wordMap w := by
  funext x
  simp only [wordMap,completeMap_cons,affine,Function.comp_apply]
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

-- ---- from OAI.MeasureTheory.SelfSimilar.Attractor ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

universe uι

open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory Set Filter

namespace EntropyRateDimension.Extensions

variable {ι : Type uι} [Fintype ι]

/-- At every depth the genuine finite-word cylinders cover every coding limit. -/
theorem attractor_subset_cylinders [Nonempty ι] (S : System ι) (n : ℕ) :
    attractor S ⊆ ⋃ w : Fin n → ι, S.wordMap w '' attractor S := by
  rintro x ⟨ω, rfl⟩
  suffices ∀ n (ω : ℕ → ι), ∃ w : Fin n → ι,
      Coding.point S ω ∈ S.wordMap w '' attractor S by
    obtain ⟨w, hw⟩ := this n ω
    exact Set.mem_iUnion.mpr ⟨w, hw⟩
  intro n
  induction n with
  | zero =>
    intro ω
    refine ⟨Fin.elim0, Coding.point S ω, ⟨ω, rfl⟩, ?_⟩
    simp [System.wordMap, System.completeMap, System.wordAffine]
  | succ n ih =>
    intro ω
    obtain ⟨w, y, hy, he⟩ := ih (Coding.shift ω)
    refine ⟨Fin.cons (ω 0) w, y, hy, ?_⟩
    rw [System.wordMap_cons, Function.comp_apply, he, ← Coding.point_shift]

end EntropyRateDimension.Extensions

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Extensions
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory Set Filter


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.Extensions.attractor_subset_cylinders.{uι} := @_root_.OAI.EntropyRateDimension.Extensions.attractor_subset_cylinders.{uι}
