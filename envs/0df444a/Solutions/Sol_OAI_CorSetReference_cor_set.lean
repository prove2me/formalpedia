-- Prove2me | solution 1 for OAI.CorSetReference.cor_set
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:13:18.026988+00:00
-- url     : https://prove2.me/submissions/75cbcbc3-bf27-4451-80d4-d5cd6eb8e706

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/AttractorFormula.lean:L31-L59
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.CorSetReference.cor_set.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_CorSetReference_cor_set) verbatim and is proved by it.
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_AttractorDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UnweightedAttractor
import Theorems.Thm_OAI_EntropyRateDimension_Extensions_existsUnique_similarityDimension
import Theorems.Thm_OAI_EntropyRateDimension_Extensions_noExactOverlaps_iff_nonempty
import Theorems.Thm_OAI_EntropyRateDimension_Extensions_no_exact_overlaps_attractor_dimension_of_root
import Definitions.Def_SelfSimilarCorollaries_002

-- ---- from OAI.MeasureTheory.SelfSimilar.Attractor ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

universe uι

open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory Set Filter

namespace EntropyRateDimension.Extensions

variable {ι : Type uι} [Fintype ι]

theorem point_continuous [Nonempty ι] [TopologicalSpace ι] [DiscreteTopology ι] (S : System ι) :
    Continuous (Coding.point S) := by
  obtain ⟨c,T,hc,hc1,hT,hr,ht⟩ := S.exists_uniform_bounds
  change Continuous (fun ω : ℕ → ι => ∑' n, Coding.term S ω n)
  apply continuous_tsum (u := fun n => c ^ n * T)
  · intro n
    change Continuous (fun ω : ℕ → ι => (∏ j ∈ Finset.range n, S.ratio (ω j)) * S.offset (ω n))
    apply Continuous.mul
    · apply continuous_finsetProd
      intro j hj
      exact (continuous_of_discreteTopology : Continuous S.ratio).comp (continuous_apply j)
    · exact (continuous_of_discreteTopology : Continuous S.offset).comp (continuous_apply n)
  · exact (summable_geometric_of_lt_one hc.le hc1).mul_right T
  · intro n ω
    simpa only [Real.norm_eq_abs] using Coding.abs_term_le S ω hc.le hT hr ht n

theorem attractor_compact [Nonempty ι] (S : System ι) : IsCompact (attractor S) := by
  let : TopologicalSpace ι := ⊥
  let : DiscreteTopology ι := ⟨rfl⟩
  exact isCompact_range (point_continuous S)

end EntropyRateDimension.Extensions

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.UnweightedAttractor ----
namespace OAI

universe uι

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension.Extensions

variable {ι : Type uι} [Fintype ι] [Nonempty ι]

theorem unweightedAttractor_compact (r t : ι → ℝ)
    (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1) :
    IsCompact (unweightedAttractor r t hr0 hr1) :=
  attractor_compact (uniformSystem r t hr0 hr1)

/-- The similarity exponent exists uniquely even for a one-symbol family. -/
theorem unweighted_existsUnique_similarityDimension (r t : ι → ℝ)
    (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1) :
    ∃! s : ℝ, 0 ≤ s ∧ ∑ i, |r i| ^ s = 1 := by
  simpa only [similaritySum, uniformSystem] using
    existsUnique_similarityDimension (uniformSystem r t hr0 hr1)

/-- Source `cor:set` for arbitrary unweighted finite similarities. The overlap
hypothesis uses the manuscript's distinct nonempty finite-word convention, and
the exponent is characterized by its literal normalization equation. -/
theorem unweighted_no_exact_overlaps_attractor_dimension_of_root
    (r t : ι → ℝ) (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1)
    (s : ℝ) (hs : 0 ≤ s) (hroot : ∑ i, |r i| ^ s = 1)
    (hno : ∀ u v : List ι, u ≠ [] → v ≠ [] →
      (uniformSystem r t hr0 hr1).wordAffine u =
        (uniformSystem r t hr0 hr1).wordAffine v → u = v) :
    dimH (unweightedAttractor r t hr0 hr1) = ENNReal.ofReal (min 1 s) := by
  exact no_exact_overlaps_attractor_dimension_of_root (uniformSystem r t hr0 hr1)
    hs hroot ((noExactOverlaps_iff_nonempty (uniformSystem r t hr0 hr1)).mpr hno)

end EntropyRateDimension.Extensions

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.AttractorFormula ----
namespace OAI

universe uι

open scoped BigOperators ENNReal

namespace CorSetReference

section
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

end

open EntropyRateDimension EntropyRateDimension.Extensions

/-- The compact coding attractor and its similarity and Hausdorff dimensions. -/
theorem cor_set {ι : Type uι} [Fintype ι] [Nonempty ι]
    (r t : ι → ℝ) (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1)
    (hno : ∀ u v : List ι, u ≠ [] → v ≠ [] →
      word r t u = word r t v → u = v) :
    IsCompact (attractor r t) ∧ (attractor r t).Nonempty ∧
    (∃! s : ℝ, 0 ≤ s ∧ ∑ i, |r i| ^ s = 1) ∧
    (∀ s : ℝ, 0 ≤ s → (∑ i, |r i| ^ s = 1) →
      dimH (attractor r t) = ENNReal.ofReal (min 1 s)) := by
  have hword (w : List ι) :
      (uniformSystem r t hr0 hr1).wordAffine w = word r t w := by
    induction w with
    | nil => rfl
    | cons i w ih =>
      change (r i * ((uniformSystem r t hr0 hr1).wordAffine w).1,
        r i * ((uniformSystem r t hr0 hr1).wordAffine w).2 + t i) =
        (r i * (word r t w).1, r i * (word r t w).2 + t i)
      rw [ih]
  have hno' : ∀ u v : List ι, u ≠ [] → v ≠ [] →
      (uniformSystem r t hr0 hr1).wordAffine u =
        (uniformSystem r t hr0 hr1).wordAffine v → u = v := by
    intro u v hu hv he
    apply hno u v hu hv
    simpa only [hword] using he
  refine ⟨?_, ?_, unweighted_existsUnique_similarityDimension r t hr0 hr1, ?_⟩
  · exact unweightedAttractor_compact r t hr0 hr1
  · exact Set.range_nonempty _
  · intro a ha he
    exact unweighted_no_exact_overlaps_attractor_dimension_of_root r t hr0 hr1 a ha he hno'

end CorSetReference

end OAI

-- ---- mission target ----
open OAI OAI.CorSetReference
universe uι
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
open EntropyRateDimension EntropyRateDimension.Extensions

namespace OAI
namespace CorSetReference
theorem _root_.solution {ι : Type uι} [Fintype ι] [Nonempty ι]
    (r t : ι → ℝ) (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1)
    (hno : ∀ u v : List ι, u ≠ [] → v ≠ [] →
      word r t u = word r t v → u = v) :
    IsCompact (attractor r t) ∧ (attractor r t).Nonempty ∧
    (∃! s : ℝ, 0 ≤ s ∧ ∑ i, |r i| ^ s = 1) ∧
    (∀ s : ℝ, 0 ≤ s → (∑ i, |r i| ^ s = 1) →
      dimH (attractor r t) = ENNReal.ofReal (min 1 s)) := by
  first
    | exact OAI.CorSetReference.cor_set r t hr0 hr1 hno
    | exact OAI.CorSetReference.cor_set
    | (apply OAI.CorSetReference.cor_set <;> assumption)
    | (intros; apply OAI.CorSetReference.cor_set <;> assumption)
end CorSetReference
end OAI
