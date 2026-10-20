-- Prove2me | solution 1 for OAI.EntropyRateDimension.Extensions.attractor_hausdorffMeasure_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T15:59:21.675081+00:00
-- url     : https://prove2.me/submissions/2d9b7648-2119-4b2e-b385-9c416afc248f

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/Attractor.lean:L125-L165
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Extensions.attractor_hausdorffMeasure_le. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_Extensions_attractor_subset_cylinders
import Theorems.Thm_OAI_EntropyRateDimension_Extensions_cylinderRatio_power_sum

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
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

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

theorem affine_lipschitz [Nonempty ι] (S : System ι) (i : ι) :
    LipschitzWith ‖S.ratio i‖₊ (S.affine i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [System.affine, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs]
  rw [show S.ratio i * x + S.offset i - (S.ratio i * y + S.offset i) =
    S.ratio i * (x-y) by ring, abs_mul]

theorem wordMap_lipschitz [Nonempty ι] (S : System ι) {n : ℕ} (w : Fin n → ι) :
    LipschitzWith (cylinderRatio S w) (S.wordMap w) := by
  induction n with
  | zero =>
    have he : S.wordMap w = (id : ℝ → ℝ) := by
      funext x
      simp [System.wordMap, System.completeMap, System.wordAffine]
    rw [he]
    simpa [cylinderRatio]
      using (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ))
  | succ n ih =>
    have hw : w = Fin.cons (w 0) (fun j => w j.succ) := by
      ext j
      exact Fin.cases rfl (fun _ => rfl) j
    rw [hw, System.wordMap_cons]
    simpa only [cylinderRatio, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      using (affine_lipschitz S (w 0)).comp (ih (fun j => w j.succ))

theorem cylinderRatio_le [Nonempty ι] (S : System ι) {c : ℝ} (hc : 0 ≤ c)
    (hr : ∀ i, |S.ratio i| ≤ c) {n : ℕ} (w : Fin n → ι) :
    (cylinderRatio S w : ℝ) ≤ c ^ n := by
  simp only [cylinderRatio, NNReal.coe_prod, coe_nnnorm, Real.norm_eq_abs]
  calc
    (∏ index : Fin n, |S.ratio (w index)|) ≤ ∏ _index : Fin n, |c| :=
      Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        (fun index _ => (hr (w index)).trans (le_abs_self c))
    _ = c ^ n := by simp [abs_of_nonneg hc]

/-- The cylinder cover proves finite Hausdorff measure at the similarity exponent.
No separation hypothesis and no assumed covering estimate enter this theorem. -/
theorem attractor_hausdorffMeasure_le [Nonempty ι] (S : System ι) {s : ℝ} (hs : 0 ≤ s)
    (hroot : ∑ i, |S.ratio i| ^ s = 1) :
    Measure.hausdorffMeasure s (attractor S) ≤ Metric.ediam (attractor S) ^ s := by
  classical
  let D := Metric.ediam (attractor S)
  have hD : D ≠ ∞ := (attractor_compact S).isBounded.ediam_ne_top
  obtain ⟨c,T,hc,hc1,hT,hr,ht⟩ := S.exists_uniform_bounds
  let mesh : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (c ^ n * D.toReal)
  have hmesh : Tendsto mesh atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1).mul_const D.toReal
    simpa only [mesh, Function.comp_def, zero_mul, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp h
  have hdiam (n : ℕ) (w : Fin n → ι) :
      Metric.ediam (S.wordMap w '' attractor S) ≤ (cylinderRatio S w : ℝ≥0∞) * D :=
    (wordMap_lipschitz S w).ediam_image_le _
  have hbound (n : ℕ) (w : Fin n → ι) :
      Metric.ediam (S.wordMap w '' attractor S) ≤ mesh n := by
    apply (hdiam n w).trans
    have hf : (cylinderRatio S w : ℝ≥0∞) ≤ ENNReal.ofReal (c ^ n) := by
      rw [ENNReal.coe_nnreal_eq]
      exact ENNReal.ofReal_le_ofReal (cylinderRatio_le S hc.le hr w)
    have hh := mul_le_mul' hf (le_refl D)
    simpa only [mesh, ENNReal.ofReal_mul (pow_nonneg hc.le n), ENNReal.ofReal_toReal hD] using hh
  have hsum (n : ℕ) :
      (∑ w : Fin n → ι, Metric.ediam (S.wordMap w '' attractor S) ^ s) ≤ D ^ s := by
    calc
      _ ≤ ∑ w : Fin n → ι, ((cylinderRatio S w : ℝ≥0∞) * D) ^ s :=
        Finset.sum_le_sum (fun w _ => ENNReal.rpow_le_rpow (hdiam n w) hs)
      _ = (∑ w : Fin n → ι, (cylinderRatio S w : ℝ≥0∞) ^ s) * D ^ s := by
        simp only [ENNReal.mul_rpow_of_nonneg _ _ hs, Finset.sum_mul]
      _ = D ^ s := by rw [cylinderRatio_power_sum S hs hroot, one_mul]
  apply (Measure.hausdorffMeasure_le_liminf_sum s (attractor S) mesh hmesh
    (fun n w => S.wordMap w '' attractor S)
    (Eventually.of_forall hbound)
    (Eventually.of_forall (attractor_subset_cylinders S))).trans
  calc
    _ ≤ liminf (fun _n : ℕ => D ^ s) atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall hsum)
    _ = D ^ s := by simp

end EntropyRateDimension.Extensions

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Extensions
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory Set Filter


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.Extensions.attractor_hausdorffMeasure_le.{uι} := @_root_.OAI.EntropyRateDimension.Extensions.attractor_hausdorffMeasure_le.{uι}
