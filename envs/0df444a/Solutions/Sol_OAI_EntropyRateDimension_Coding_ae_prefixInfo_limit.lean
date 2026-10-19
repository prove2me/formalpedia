-- Prove2me | solution 1 for OAI.EntropyRateDimension.Coding.ae_prefixInfo_limit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:14:46.928102+00:00
-- url     : https://prove2.me/submissions/5a0c864c-8b7c-4943-9a12-bc0dfbc421a7

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/BallLimits.lean:L158-L177
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Coding.ae_prefixInfo_limit. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_BallRatios_ae_logRatio_limit
import Theorems.Thm_OAI_EntropyRateDimension_BallRatios_information_component
import Theorems.Thm_OAI_EntropyRateDimension_BallRatios_information_one_bound
import Theorems.Thm_OAI_EntropyRateDimension_BallRatios_logEnvelope_integrable
import Theorems.Thm_OAI_EntropyRateDimension_BallRatios_logRatio_bounds
import Theorems.Thm_OAI_EntropyRateDimension_Coding_head_point_law
import Theorems.Thm_OAI_EntropyRateDimension_Coding_law_selfSimilar
import Theorems.Thm_OAI_EntropyRateDimension_ErgodicAux_ae_tendsto_average
import Theorems.Thm_OAI_EntropyRateDimension_ErgodicAux_ae_tendsto_triangle
import Theorems.Thm_OAI_EntropyRateDimension_System_selfSimilar_compact

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

end Coding
end EntropyRateDimension

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.BallRatios ----
namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace EntropyRateDimension
namespace BallRatios

theorem measurable_ball_mass (μ : Measure ℝ) [SFinite μ] (r : ℝ) :
    Measurable (fun x : ℝ => μ (closedBall x r)) := by
  have hs : MeasurableSet {p : ℝ × ℝ | dist p.2 p.1 ≤ r} :=
    measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
  exact measurable_measure_prodMk_left hs

theorem maximal_measurable (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    Measurable (maximal μ ν) := by
  apply Measurable.iSup
  intro q
  exact (measurable_ball_mass μ _).div (measurable_ball_mass ν _)

theorem logEnvelope_nonneg (μ ν : Measure ℝ) (x : ℝ) : 0 ≤ logEnvelope μ ν x :=
  le_max_left _ _

theorem logEnvelope_measurable (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    Measurable (logEnvelope μ ν) :=
  measurable_const.max (maximal_measurable μ ν).ennreal_toReal.log

theorem logRatio_measurable (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    Measurable (fun p : ℝ × ℝ => logRatio μ ν p.1 p.2) := by
  have hm (κ : Measure ℝ) [SFinite κ] :
      Measurable (fun p : ℝ × ℝ => κ (closedBall p.1 p.2)) := by
    have hs : MeasurableSet {z : (ℝ × ℝ) × ℝ | dist z.2 z.1.1 ≤ z.1.2} :=
      measurableSet_le (measurable_snd.dist (measurable_fst.fst)) (measurable_fst.snd)
    exact measurable_measure_prodMk_left hs
  exact ((hm μ).div (hm ν)).ennreal_toReal.log

end BallRatios
end EntropyRateDimension

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.BallIntegrability ----
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
namespace EntropyRateDimension
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators
namespace System
variable {ι : Type uι} [Fintype ι]

theorem component_le (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ) (i : ι) :
    S.component μ i ≤ μ := by
  calc
    S.component μ i ≤ ∑ j, S.component μ j :=
      Finset.single_le_sum (fun j _ => Measure.zero_le _) (Finset.mem_univ i)
    _ = μ := hμ.symm

end System

namespace BallRatios
end BallRatios

namespace Coding
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem slope_ne_zero (S : System ι) (ω : ℕ → ι) (n : ℕ) : slope S ω n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact abs_pos.mp (S.ratio_pos (ω j))

omit [Nonempty ι] in
theorem abs_slope_pos (S : System ι) (ω : ℕ → ι) (n : ℕ) : 0 < |slope S ω n| :=
  abs_pos.mpr (slope_ne_zero S ω n)

theorem abs_slope_lt_one (S : System ι) (ω : ℕ → ι) {n : ℕ} (hn : 0 < n) :
    |slope S ω n| < 1 := by
  obtain ⟨c,T,hc,hc1,_,hr,_⟩ := S.exists_uniform_bounds
  exact (abs_slope_le S ω hc.le hr n).trans_lt (pow_lt_one₀ hc.le hc1 hn.ne')

theorem slope_tendsto_zero (S : System ι) (ω : ℕ → ι) :
    Tendsto (fun n => |slope S ω n|) atTop (𝓝 0) := by
  obtain ⟨c,T,hc,hc1,_,hr,_⟩ := S.exists_uniform_bounds
  exact squeeze_zero (fun n => abs_nonneg _) (abs_slope_le S ω hc.le hr)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1)

end Coding
end EntropyRateDimension

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.CodingIntegrals ----
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
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter EntropyRateDimension.Bernoulli
open scoped Topology BigOperators ENNReal
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI
theorem head_point_measurable (S : System ι) :
    Measurable (fun ω : ℕ → ι => (ω 0,point S ω)) :=
  (measurable_pi_apply 0).prodMk (point_measurable S)

theorem ae_head_point (S : System ι) {P : ι → ℝ → Prop}
    (hP : ∀ i, ∀ᵐ x ∂S.component (law S) i, P i x) :
    ∀ᵐ ω ∂addressMeasure S, P (ω 0) (point S ω) := by
  have hh : ∀ᵐ z ∂(addressMeasure S).map (fun ω => (ω 0,point S ω)), P z.1 z.2 := by
    rw [head_point_law,ae_finsetSum_measure_iff]
    intro i _
    rw [Measure.dirac_prod,(measurableEmbedding_prodMk_left i).ae_map_iff]
    exact hP i
  exact ae_of_ae_map (head_point_measurable S).aemeasurable hh

theorem integrable_head_point (S : System ι) {f : ι → ℝ → ℝ}
    (hfm : ∀ i, Measurable (f i)) (hf : ∀ i, Integrable (f i) (S.component (law S) i)) :
    Integrable (fun ω => f (ω 0) (point S ω)) (addressMeasure S) := by
  have hm : Measurable (fun z : ι × ℝ => f z.1 z.2) :=
    measurable_from_prod_countable_right hfm
  have hi : Integrable (fun z : ι × ℝ => f z.1 z.2)
      ((addressMeasure S).map (fun ω => (ω 0,point S ω))) := by
    rw [head_point_law,integrable_finsetSum_measure]
    intro i _
    rw [Measure.dirac_prod,integrable_map_measure hm.aestronglyMeasurable
      measurable_prodMk_left.aemeasurable]
    exact hf i
  exact hi.comp_measurable (head_point_measurable S)

theorem envelope_joint_measurable (S : System ι) : Measurable (fun z : ι × ℝ =>
    BallRatios.logEnvelope (law S) (S.component (law S) z.1) z.2) := by
  apply measurable_from_prod_countable_right
  intro i
  exact BallRatios.logEnvelope_measurable (law S) (S.component (law S) i)

theorem envelope_measurable (S : System ι) : Measurable (envelope S) := by
  unfold envelope
  have hh := (envelope_joint_measurable S).comp (head_point_measurable S)
  exact hh

omit [Nonempty ι] in
theorem envelope_nonneg (S : System ι) (ω : ℕ → ι) : 0 ≤ envelope S ω :=
  BallRatios.logEnvelope_nonneg _ _ _

theorem envelope_integrable (S : System ι) : Integrable (envelope S) (addressMeasure S) :=
  integrable_head_point S (fun i => BallRatios.logEnvelope_measurable _ (S.component (law S) i))
    (fun i => BallRatios.logEnvelope_integrable _ (S.component (law S) i))

theorem corr_joint_measurable (S : System ι) : Measurable (fun z : ι × (ℝ × ℝ) =>
    BallRatios.logRatio (law S) (S.component (law S) z.1) z.2.1 z.2.2) := by
  apply measurable_from_prod_countable_right
  intro i
  exact BallRatios.logRatio_measurable (law S) (S.component (law S) i)

theorem corr_measurable (S : System ι) (n : ℕ) : Measurable (corr S n) := by
  unfold corr
  have hh := (corr_joint_measurable S).comp ((measurable_pi_apply 0).prodMk
    ((point_measurable S).prodMk (slope_measurable S n).abs))
  exact hh

theorem corrLimit_measurable (S : System ι) : Measurable (corrLimit S) := by
  have hm : Measurable (fun z : ι × ℝ =>
      Real.log ((law S).rnDeriv (S.component (law S) z.1) z.2).toReal) := by
    apply measurable_from_prod_countable_right
    intro i
    exact ((law S).measurable_rnDeriv (S.component (law S) i)).ennreal_toReal.log
  exact hm.comp (head_point_measurable S)

theorem ae_corr_bounds (S : System ι) : ∀ᵐ ω ∂addressMeasure S, ∀ n : ℕ, 0 < n →
    0 ≤ corr S n ω ∧ corr S n ω ≤ envelope S ω := by
  filter_upwards [ae_head_point S (fun i => BallRatios.logRatio_bounds _ _
    (S.component_le _ (law_selfSimilar S) i))] with ω hω
  intro n hn
  exact hω _ (abs_slope_pos S ω n) (abs_slope_lt_one S ω hn)

theorem ae_corr_limit (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => corr S n ω) atTop (𝓝 (corrLimit S ω)) := by
  filter_upwards [ae_head_point S (fun i => BallRatios.ae_logRatio_limit _ _
    (S.component_le _ (law_selfSimilar S) i))] with ω hω
  apply hω.2.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨slope_tendsto_zero S ω,
    Eventually.of_forall (abs_slope_pos S ω)⟩

end EntropyRateDimension.Coding

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.Clipping ----
namespace OAI

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
namespace EntropyRateDimension.BallRatios
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators

theorem information_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (x r : ℝ) :
    0 ≤ information μ x r := by
  unfold information
  exact neg_nonneg.mpr (Real.log_nonpos ENNReal.toReal_nonneg (measureReal_le_one))

end EntropyRateDimension.BallRatios

end

end OAI

-- ---- inlined from the OAI_EntropyRateDimension_Bernoulli_shift_ergodic solution (the platform cannot check that node's statement) ----
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


omit [MeasurableSpace α] in
theorem shift_iterate (n : ℕ) (ω : ℕ → α) (k : ℕ) :
    shift^[n] ω k = ω (k+n) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', shift, ih]
    congr 1
    omega


theorem invariant_tail_measurable {s : Set (ℕ → α)} (hs : MeasurableSet s)
    (hinv : shift ⁻¹' s = s) :
    MeasurableSet[Filter.limsup (fun n : ℕ =>
      MeasurableSpace.comap (Function.eval n) (inferInstance : MeasurableSpace α)) atTop] s := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat']
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  have hm : @Measurable (ℕ → α) (ℕ → α)
      (⨆ i : ℕ, MeasurableSpace.comap (fun ω : ℕ → α => ω (i+n)) (inferInstance : MeasurableSpace α))
      inferInstance (fun ω k => ω (k+n)) := by
    apply Measurable.of_comap_le
    change MeasurableSpace.comap (fun ω : ℕ → α => fun k => ω (k+n))
      (⨆ k : ℕ, MeasurableSpace.comap (Function.eval k) (inferInstance : MeasurableSpace α)) ≤ _
    rw [MeasurableSpace.comap_iSup]
    apply iSup_le
    intro k
    rw [MeasurableSpace.comap_comp]
    exact le_iSup (fun i : ℕ => MeasurableSpace.comap (fun ω : ℕ → α => ω (i+n))
      (inferInstance : MeasurableSpace α)) k
  have he : (fun ω : ℕ → α => fun k => ω (k+n)) = shift^[n] := by
    funext ω k
    exact (shift_iterate n ω k).symm
  rw [he] at hm
  have hi : (shift^[n]) ⁻¹' s = s := Function.IsFixedPt.preimage_iterate hinv n
  rw [← hi]
  exact hm hs

theorem shift_ergodic (p : Measure α) [IsProbabilityMeasure p] :
    Ergodic shift (Measure.infinitePi (fun _ : ℕ => p)) where
  toMeasurePreserving := shift_preserving p
  aeconst_set := by
    intro s hs hi
    have hind : iIndepFun (fun n : ℕ => (@Function.eval ℕ (fun _ => α) n))
        (Measure.infinitePi fun _ : ℕ => p) :=
      iIndepFun_infinitePi (fun _ : ℕ => measurable_id)
    have hz := measure_zero_or_one_of_measurableSet_limsup_atTop
      (fun n => (measurable_pi_apply n).comap_le) hind
      (invariant_tail_measurable hs hi)
    apply Filter.eventuallyConst_set.mpr
    rcases hz with h0 | h1
    · right
      exact measure_eq_zero_iff_ae_notMem.mp h0
    · left
      have hc : (Measure.infinitePi fun _ : ℕ => p) sᶜ = 0 := by
        rw [measure_compl hs (measure_ne_top _ _), h1]
        simp
      simpa only [mem_compl_iff, not_not] using measure_eq_zero_iff_ae_notMem.mp hc

end Bernoulli
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
theorem clippedCorr_measurable (S : System ι) (n : ℕ) : Measurable (clippedCorr S n) :=
  measurable_const.max ((envelope_measurable S).min (corr_measurable S n))
theorem clippedLimit_measurable (S : System ι) : Measurable (clippedLimit S) :=
  measurable_const.max ((envelope_measurable S).min (corrLimit_measurable S))

omit [Nonempty ι] in
theorem clip_bound {E x : ℝ} (hE : 0 ≤ E) : |max 0 (min E x)| ≤ E := by
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le hE (min_le_left _ _)

omit [Nonempty ι] in
theorem clippedCorr_bound (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    |clippedCorr S n ω| ≤ envelope S ω := clip_bound (envelope_nonneg S ω)
omit [Nonempty ι] in
theorem clippedLimit_bound (S : System ι) (ω : ℕ → ι) :
    |clippedLimit S ω| ≤ envelope S ω := clip_bound (envelope_nonneg S ω)

theorem ae_clipped_limit (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => clippedCorr S n ω) atTop (𝓝 (clippedLimit S ω)) := by
  filter_upwards [ae_corr_limit S] with ω hω
  exact tendsto_const_nhds.max (tendsto_const_nhds.min hω)

theorem ae_corr_triangle (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => (∑ j ∈ Finset.range n, corr S (n-j) (shift^[j] ω)) / (n : ℝ))
      atTop (𝓝 (∫ ω, clippedLimit S ω ∂addressMeasure S)) := by
  have hT : Ergodic shift (addressMeasure S) := shift_ergodic (symbolMeasure S)
  have ht := ae_tendsto_triangle hT (clippedCorr_measurable S) (clippedLimit_measurable S)
    (envelope_measurable S) (clippedCorr_bound S) (clippedLimit_bound S)
    (envelope_integrable S) (ae_clipped_limit S)
  have ha : ∀ᵐ ω ∂addressMeasure S, ∀ j : ℕ, ∀ n : ℕ, 0 < n →
      0 ≤ corr S n (shift^[j] ω) ∧ corr S n (shift^[j] ω) ≤ envelope S (shift^[j] ω) := by
    apply ae_all_iff.mpr
    intro j
    exact ((show MeasurePreserving shift (addressMeasure S) (addressMeasure S) from
      shift_preserving (symbolMeasure S)).iterate j).quasiMeasurePreserving.ae (ae_corr_bounds S)
  filter_upwards [ht,ha] with ω hω hbound
  convert hω using 1
  funext n
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : 0 < n-j := by have := Finset.mem_range.mp hj; omega
  obtain ⟨h0,h1⟩ := hbound j (n-j) hjn
  simp only [clippedCorr,min_eq_right h1,max_eq_right h0]

theorem prefixInfo_succ (S : System ι) (n : ℕ) (ω : ℕ → ι)
    (hω : point S (shift ω) ∈ (law S).support) :
    prefixInfo S (n+1) ω = prefixInfo S n (shift ω) + weightObs S ω - corr S (n+1) ω := by
  have he := BallRatios.information_component S (law S) (law_selfSimilar S) (ω 0)
    hω (abs_slope_pos S (shift ω) n)
  have hs : |slope S ω (n+1)| = |S.ratio (ω 0)| * |slope S (shift ω) n| := by
    rw [slope_shift,abs_mul]
  unfold prefixInfo weightObs corr
  rw [point_shift S ω,hs]
  exact he

omit [Nonempty ι] in
theorem triangle_succ (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    (∑ j ∈ Finset.range (n+1), corr S (n+1-j) (shift^[j] ω)) =
      corr S (n+1) ω + ∑ j ∈ Finset.range n, corr S (n-j) (shift^[j] (shift ω)) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.add_sub_add_right,Function.iterate_succ_apply,Function.iterate_zero_apply,
    Nat.sub_zero]
  ring

theorem prefixInfo_telescope (S : System ι) (ω : ℕ → ι)
    (hω : ∀ j : ℕ, point S (shift^[j] ω) ∈ (law S).support) (n : ℕ) :
    prefixInfo S n ω = birkhoffSum shift (weightObs S) n ω -
      (∑ j ∈ Finset.range n, corr S (n-j) (shift^[j] ω)) +
      BallRatios.information (law S) (point S (shift^[n] ω)) 1 := by
  induction n generalizing ω with
  | zero => simp [prefixInfo,slope_zero,birkhoffSum]
  | succ n ih =>
    have htail : ∀ j : ℕ, point S (shift^[j] (shift ω)) ∈ (law S).support := by
      intro j
      simpa only [Function.iterate_succ_apply] using hω (j+1)
    rw [prefixInfo_succ S n ω (by simpa using hω 1),ih (shift ω) htail,
      triangle_succ,birkhoffSum_succ']
    simp only [Function.iterate_succ_apply]
    ring

omit [Nonempty ι] in
theorem head_integrable (S : System ι) (f : ι → ℝ) :
    Integrable (fun ω : ℕ → ι => f (ω 0)) (addressMeasure S) := by
  classical
  apply Integrable.of_bound ((measurable_of_finite f).comp (measurable_pi_apply 0)).aestronglyMeasurable
    (∑ i, |f i|)
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_univ (ω 0))

theorem ae_point_support (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    ∀ j : ℕ, point S (shift^[j] ω) ∈ (law S).support := by
  apply ae_all_iff.mpr
  intro j
  have ha : ∀ᵐ ω ∂addressMeasure S, point S ω ∈ (law S).support :=
    ae_of_ae_map (point_measurable S).aemeasurable (law S).support_mem_ae
  exact ((show MeasurePreserving shift (addressMeasure S) (addressMeasure S) from
      shift_preserving (symbolMeasure S)).iterate j).quasiMeasurePreserving.ae ha

theorem law_support_compact (S : System ι) : IsCompact (law S).support := by
  obtain ⟨B,_,hB⟩ := S.selfSimilar_compact (law S) (law_selfSimilar S)
  exact isCompact_Icc.of_isClosed_subset (law S).isClosed_support
    (Measure.support_subset_of_isClosed isClosed_Icc hB)

theorem ae_prefixInfo_limit (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => prefixInfo S n ω / (n : ℝ)) atTop (𝓝 (infoRate S)) := by
  obtain ⟨C,hC,hCb⟩ := BallRatios.information_one_bound (law S) (law_support_compact S)
  have hT : Ergodic shift (addressMeasure S) := shift_ergodic (symbolMeasure S)
  have hb := ae_tendsto_average hT
    ((measurable_of_finite (fun i => -Real.log (S.weight i))).comp (measurable_pi_apply 0))
    (head_integrable S (fun i => -Real.log (S.weight i)))
  filter_upwards [hb,ae_corr_triangle S,ae_point_support S] with ω hweight hcorr hsupp
  have hend : Tendsto (fun n => BallRatios.information (law S)
      (point S (shift^[n] ω)) 1 / (n : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun n => div_nonneg (BallRatios.information_nonneg _ _ _) (Nat.cast_nonneg n))
      (fun n => div_le_div_of_nonneg_right (hCb _ (hsupp n)) (Nat.cast_nonneg n))
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := (hweight.sub hcorr).add hend
  convert hh using 1
  · funext n
    rw [prefixInfo_telescope S ω hsupp,add_div,sub_div]
    rfl
  · simp only [infoRate,weightObs,add_zero,Function.comp_def]

end EntropyRateDimension.Coding

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Coding
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
open MeasureTheory Metric Set Filter
open EntropyRateDimension.Bernoulli EntropyRateDimension.ErgodicAux
open scoped Topology BigOperators
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_1
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_1


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.Coding.ae_prefixInfo_limit.{uι} := @_root_.OAI.EntropyRateDimension.Coding.ae_prefixInfo_limit.{uι}
