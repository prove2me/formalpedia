-- Prove2me | solution 1 for OAI.EntropyRateDimension.Extensions.no_exact_overlaps_attractor_dimension_of_root
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:03:49.825987+00:00
-- url     : https://prove2.me/submissions/c1879fb8-ace1-4b78-80d5-aa53702a516a

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/AttractorDimension.lean:L126-L141
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Extensions.no_exact_overlaps_attractor_dimension_of_root. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_AttractorDimension
import Theorems.Thm_OAI_EntropyRateDimension_Extensions_attractor_hausdorffMeasure_le
import Theorems.Thm_OAI_EntropyRateDimension_Extensions_no_exact_overlaps_dimension

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

-- ---- from OAI.MeasureTheory.SelfSimilar.Bernoulli ----
namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology

namespace EntropyRateDimension
namespace Bernoulli

variable {α : Type uα} [MeasurableSpace α]

theorem shift_measurable : Measurable (shift (α := α)) :=
  measurable_pi_iff.mpr fun n => measurable_pi_apply (n+1)

theorem shift_preserving (p : Measure α) [IsProbabilityMeasure p] :
    MeasurePreserving shift (Measure.infinitePi (fun _ : ℕ => p))
      (Measure.infinitePi (fun _ : ℕ => p)) where
  measurable := shift_measurable
  map_eq := by
    have hi : iIndepFun (fun n : ℕ => (@Function.eval ℕ (fun _ => α) n))
        (Measure.infinitePi fun _ : ℕ => p) :=
      iIndepFun_infinitePi (fun _ : ℕ => measurable_id)
    have hh := (hi.precomp Nat.succ_injective).map_fun_eq_infinitePi_map
      (fun n => measurable_pi_apply (n+1))
    change Measure.map (fun ω : ℕ → α => fun n => ω (n+1))
      (Measure.infinitePi fun _ : ℕ => p) = _
    simpa only [Measure.infinitePi_map_eval, Function.eval] using hh

theorem head_indep_tail (p : Measure α) [IsProbabilityMeasure p] :
    IndepFun (fun ω : ℕ → α => ω 0) shift (Measure.infinitePi fun _ : ℕ => p) := by
  let m : ℕ → MeasurableSpace (ℕ → α) := fun n =>
    MeasurableSpace.comap (fun ω : ℕ → α => ω n) inferInstance
  have hi : iIndep m (Measure.infinitePi fun _ : ℕ => p) :=
    iIndepFun_infinitePi (fun _ : ℕ => measurable_id)
  have h := indep_iSup_of_disjoint (fun n => (measurable_pi_apply n).comap_le) hi
    (S := {0}) (T := Set.range Nat.succ) (by
      apply Set.disjoint_left.mpr
      rintro n (hn : n = 0) ⟨k,hk⟩
      omega)
  apply indep_of_indep_of_le h
  · exact le_iSup_of_le 0 (le_iSup_of_le rfl le_rfl)
  · change MeasurableSpace.comap shift
      (⨆ k : ℕ, MeasurableSpace.comap (Function.eval k) (inferInstance : MeasurableSpace α)) ≤ _
    rw [MeasurableSpace.comap_iSup]
    apply iSup_le
    intro k
    rw [MeasurableSpace.comap_comp]
    exact le_iSup_of_le (k+1) (le_iSup_of_le ⟨k,rfl⟩ le_rfl)

theorem head_tail_law (p : Measure α) [IsProbabilityMeasure p] :
    (Measure.infinitePi fun _ : ℕ => p).map (fun ω => (ω 0,shift ω)) =
      p.prod (Measure.infinitePi fun _ : ℕ => p) := by
  rw [(head_indep_tail p).map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable shift_measurable.aemeasurable,
    Measure.infinitePi_map_eval, (shift_preserving p).map_eq]

end Bernoulli
end EntropyRateDimension
end

end OAI

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

theorem head_tail_point_law (S : System ι) :
    (addressMeasure S).map (fun ω => (ω 0,point S (shift ω))) =
      (symbolMeasure S).prod (law S) := by
  have h := congrArg (Measure.map (Prod.map id (point S)))
    (Bernoulli.head_tail_law (symbolMeasure S))
  rw [Measure.map_map (measurable_id.prodMap (point_measurable S))
      ((measurable_pi_apply 0).prodMk Bernoulli.shift_measurable)] at h
  rw [← Measure.map_prod_map _ _ measurable_id (point_measurable S), Measure.map_id] at h
  exact h

theorem law_selfSimilar (S : System ι) : S.SelfSimilar (law S) := by
  classical
  let f : ι × ℝ → ℝ := fun z => S.affine z.1 z.2
  have hf : Measurable f := by
    exact ((measurable_of_finite S.ratio).comp measurable_fst).mul measurable_snd |>.add
      ((measurable_of_finite S.offset).comp measurable_fst)
  have hh := congrArg (Measure.map f) (head_tail_point_law S)
  have hp : Measurable (fun ω : ℕ → ι => (ω 0,point S (shift ω))) :=
    (measurable_pi_apply 0).prodMk ((point_measurable S).comp Bernoulli.shift_measurable)
  rw [Measure.map_map hf hp] at hh
  have he : f ∘ (fun ω => (ω 0,point S (shift ω))) = point S :=
    funext fun ω => (point_shift S ω).symm
  rw [he] at hh
  change law S = _ at hh
  change law S = _
  conv_lhs => rw [hh]
  change ((∑ i, ENNReal.ofReal (S.weight i) • Measure.dirac i).prod (law S)).map f = _
  rw [← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_fintype,
    Measure.map_finset_sum hf.aemeasurable]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Measure.prod_smul_left, Measure.map_smul _ _ f, Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left]
  rfl

end Coding
end EntropyRateDimension

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.NoOverlaps ----
namespace OAI

universe uι uα

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension.Extensions

variable {ι : Type uι} [Fintype ι]

theorem lyapunov_eq_naturalLyapunov (S : System ι) :
    S.lyapunov = naturalLyapunov S / Real.log 2 := by
  simp only [System.lyapunov, naturalLyapunov, ← mul_div_assoc,
    ← Finset.sum_div, neg_div]

end EntropyRateDimension.Extensions

end OAI

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

theorem attractor_dim_le_similarity [Nonempty ι] (S : System ι) {s : ℝ} (hs : 0 ≤ s)
    (hroot : ∑ i, |S.ratio i| ^ s = 1) :
    dimH (attractor S) ≤ ENNReal.ofReal s := by
  have hfinite : Measure.hausdorffMeasure s (attractor S) ≠ ∞ :=
    ne_top_of_le_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hs (attractor_compact S).isBounded.ediam_ne_top)
      (attractor_hausdorffMeasure_le S hs hroot)
  rw [ENNReal.ofReal_eq_coe_nnreal hs]
  exact dimH_le_of_hausdorffMeasure_ne_top (d := ⟨s, hs⟩) hfinite

theorem attractor_dim_le_one [Nonempty ι] (S : System ι) : dimH (attractor S) ≤ 1 := by
  exact (dimH_mono (Set.subset_univ _)).trans_eq Real.dimH_univ

end EntropyRateDimension.Extensions

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.AttractorDimension ----
namespace OAI

universe uι

open scoped BigOperators ENNReal Topology
open MeasureTheory Set Filter

namespace EntropyRateDimension.Extensions

variable {ι : Type uι} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem similaritySystem_noExactOverlaps (S : System ι) {s : ℝ}
    (hroot : ∑ i, |S.ratio i| ^ s = 1) (h : NoExactOverlaps S) :
    NoExactOverlaps (similaritySystem S hroot) := by
  have heq : ∀ u : List ι, (similaritySystem S hroot).wordAffine u = S.wordAffine u := by
    intro u
    induction u with
    | nil => rfl
    | cons i u ih =>
      exact congrArg (fun z : ℝ × ℝ =>
        (S.ratio i * z.1, S.ratio i * z.2 + S.offset i)) ih
  intro u v huv
  apply h
  rw [← heq u, ← heq v]
  exact huv

omit [Nonempty ι] in
theorem similaritySystem_entropy (S : System ι) {s : ℝ}
    (hroot : ∑ i, |S.ratio i| ^ s = 1) :
    symbolEntropy (similaritySystem S hroot) =
      s * naturalLyapunov (similaritySystem S hroot) := by
  simp only [symbolEntropy, naturalLyapunov, similaritySystem, Real.negMulLog,
    Real.log_rpow (S.ratio_pos _), mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem naturalLyapunov_pos (S : System ι) : 0 < naturalLyapunov S := by
  have h := S.lyapunov_pos
  rw [lyapunov_eq_naturalLyapunov] at h
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact ((div_pos_iff.mp h).resolve_right (fun hh => (not_lt_of_ge h2.le) hh.2)).1

theorem coding_law_attractor_mass [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι) : Coding.law S (attractor S) = 1 := by
  rw [Coding.law, Measure.map_apply (Coding.point_measurable S)
    (attractor_compact S).measurableSet]
  have he : Coding.point S ⁻¹' attractor S = Set.univ := by
    ext ω
    simp [attractor]
  rw [he, measure_univ]

theorem coding_law_dimension_le_attractor [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (S : System ι) : lowerHausdorffDimension (Coding.law S) ≤ dimH (attractor S) := by
  exact iInf_le_of_le (attractor S) (iInf_le_of_le (attractor_compact S).measurableSet
    (iInf_le_of_le (by rw [coding_law_attractor_mass]; exact zero_lt_one) le_rfl))

/-- The set-dimension corollary for an arbitrary normalized similarity exponent. -/
theorem no_exact_overlaps_attractor_dimension_of_root (S : System ι) {s : ℝ}
    (hs : 0 ≤ s) (hroot : ∑ i, |S.ratio i| ^ s = 1) (h : NoExactOverlaps S) :
    dimH (attractor S) = ENNReal.ofReal (min 1 s) := by
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  let T := similaritySystem S hroot
  apply le_antisymm
  · rw [ENNReal.ofReal_min]
    exact le_min (by simpa using attractor_dim_le_one S) (attractor_dim_le_similarity S hs hroot)
  · have hd := no_exact_overlaps_dimension T (Coding.law T) (Coding.law_selfSimilar T)
      (similaritySystem_noExactOverlaps S hroot h)
    rw [similaritySystem_entropy S hroot,
      mul_div_cancel_right₀ _ (naturalLyapunov_pos T).ne'] at hd
    rw [← hd]
    exact coding_law_dimension_le_attractor T

end EntropyRateDimension.Extensions

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Extensions
open scoped BigOperators ENNReal Topology
open MeasureTheory Set Filter


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.Extensions.no_exact_overlaps_attractor_dimension_of_root.{uι} := @_root_.OAI.EntropyRateDimension.Extensions.no_exact_overlaps_attractor_dimension_of_root.{uι}
