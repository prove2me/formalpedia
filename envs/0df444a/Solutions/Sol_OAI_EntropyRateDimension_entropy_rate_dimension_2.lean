-- Prove2me | solution 2 for OAI.EntropyRateDimension.entropy_rate_dimension
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:17:11.055684+00:00
-- url     : https://prove2.me/submissions/44ff2370-9673-488b-abf6-45c76551e760

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/Main.lean:L59-L65
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.EntropyRateDimension.entropy_rate_dimension.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_EntropyRateDimension_entropy_rate_dimension) verbatim and is proved by it.
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RetainedLoss
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairBands
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowCount
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Main
import Theorems.Thm_OAI_EntropyRateDimension_Coding_ae_prefixInfo_limit
import Theorems.Thm_OAI_EntropyRateDimension_Coding_ae_radial_sequence
import Theorems.Thm_OAI_EntropyRateDimension_Coding_law_selfSimilar
import Theorems.Thm_OAI_EntropyRateDimension_Interpolation_tendsto_div_of_bounded_gaps
import Theorems.Thm_OAI_EntropyRateDimension_LocalMass_lower_dim_eq_of_limit
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_entropy_bound_of_radial_limit
import Theorems.Thm_OAI_EntropyRateDimension_System_average_bound
import Theorems.Thm_OAI_EntropyRateDimension_System_blocks_entropyRate_lower
import Theorems.Thm_OAI_EntropyRateDimension_System_ratio_wordType
import Theorems.Thm_OAI_EntropyRateDimension_System_selfSimilar_compact
import Theorems.Thm_OAI_EntropyRateDimension_System_selfSimilar_words
import Theorems.Thm_OAI_EntropyRateDimension_Typed_no_strict_entropy_gap
import Theorems.Thm_OAI_EntropyRateDimension_exists_nat_log_small

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

theorem lyapunov_pos [Nonempty ι] (S : System ι) : 0 < S.lyapunov := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [lyapunov, neg_pos]
  apply Finset.sum_neg
  · intro i _
    exact mul_neg_of_pos_of_neg (S.weight_pos i)
      (div_neg_of_neg_of_pos (Real.log_neg (S.ratio_pos i) (S.ratio_lt_one i)) hlog)
  · exact Finset.univ_nonempty

end System

theorem lowerHausdorffDimension_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    lowerHausdorffDimension μ ≤ 1 := by
  calc
    lowerHausdorffDimension μ ≤ dimH (Set.univ : Set ℝ) :=
      iInf_le_of_le Set.univ (iInf_le_of_le MeasurableSet.univ
        (iInf_le_of_le (by simp : 0 < μ Set.univ) le_rfl))
    _ = 1 := Real.dimH_univ

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

end System

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.InvariantLaw ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
namespace EntropyRateDimension.System
open MeasureTheory Filter Set
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι]

theorem average_continuous (S : System ι) {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    Continuous (S.average f n) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (ih.comp (S.affine_continuous i))

theorem average_integrable (S : System ι) {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hb : ∀ x, |f x| ≤ C) (n : ℕ) (μ : Measure ℝ)
    [IsFiniteMeasure μ] : Integrable (S.average f n) μ := by
  apply Integrable.of_bound (S.average_continuous hf n).aestronglyMeasurable C
  exact ae_of_all μ fun x => by simpa only [Real.norm_eq_abs] using S.average_bound hb n x

theorem selfSimilar_integral (S : System ι) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : S.SelfSimilar μ) {f : ℝ → ℝ} {C : ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ C) :
    (∫ x, f x ∂μ) = ∑ i, S.weight i * ∫ x, f (S.affine i x) ∂μ := by
  have hi : ∀ i, Integrable f (μ.map (S.affine i)) := fun i =>
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs] using hb x)
  conv_lhs => rw [hμ]
  rw [integral_finsetSum_measure (fun i _ => (hi i).smul_measure (by simp))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure,integral_map (S.affine_continuous i).measurable.aemeasurable
    hf.aestronglyMeasurable,ENNReal.toReal_ofReal (S.weight_nonneg i)]
  rfl

theorem integral_average (S : System ι) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : S.SelfSimilar μ) {f : ℝ → ℝ} {C : ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ C)
    (n : ℕ) : (∫ x, S.average f n x ∂μ) = ∫ x, f x ∂μ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∫ x, ∑ i, S.weight i * S.average f n (S.affine i x) ∂μ) = _
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
      rw [← S.selfSimilar_integral μ hμ (S.average_continuous hf n) (S.average_bound hb n),ih]
    · intro i _
      apply Integrable.const_mul
      apply Integrable.of_bound ((S.average_continuous hf n).comp
        (S.affine_continuous i)).aestronglyMeasurable C
      exact ae_of_all μ fun x => by
        simpa only [Real.norm_eq_abs,Function.comp_def] using S.average_bound hb n (S.affine i x)

theorem average_difference (S : System ι) {f : ℝ → ℝ} {c ε δ : ℝ}
    (hc : 0 ≤ c) (hr : ∀ i, |S.ratio i| ≤ c)
    (hf : ∀ x y, |x-y| < δ → |f x-f y| ≤ ε) (n : ℕ) {x y : ℝ}
    (hxy : |x-y| *c^n < δ) : |S.average f n x-S.average f n y| ≤ ε := by
  induction n generalizing x y with
  | zero => simpa only [average,pow_zero,mul_one] using hf x y (by simpa using hxy)
  | succ n ih =>
    simp only [average,← Finset.sum_sub_distrib,← mul_sub]
    calc
      _ ≤ ∑ i, |S.weight i * (S.average f n (S.affine i x)-S.average f n (S.affine i y))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, S.weight i * ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul,abs_of_nonneg (S.weight_nonneg i)]
        apply mul_le_mul_of_nonneg_left _ (S.weight_nonneg i)
        apply ih
        have he : S.affine i x-S.affine i y = S.ratio i*(x-y) := by simp only [affine]; ring
        rw [he,abs_mul]
        calc
          _ ≤ (c*|x-y|)*c^n := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hr i) (abs_nonneg _)) (pow_nonneg hc n)
          _ = |x-y| *c^(n+1) := by rw [pow_succ]; ring
          _ < δ := hxy
      _ = ε := by rw [← Finset.sum_mul,S.weight_sum,one_mul]

variable [Nonempty ι]

theorem tendsto_average_at_zero (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) {f : ℝ → ℝ} {C : ℝ}
    (hf : UniformContinuous f) (hb : ∀ x, |f x| ≤ C) :
    Tendsto (fun n => S.average f n 0) atTop (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨c,T,hc,hc1,_,hr,_⟩ := S.exists_uniform_bounds
  obtain ⟨B,hB,hBc⟩ := S.selfSimilar_compact μ hμ
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp hf (ε/2) (by linarith)
  have hlim : Tendsto (fun n : ℕ => B*c^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1).const_mul B
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).2 δ hδ)
  refine ⟨N,fun n hn => ?_⟩
  have hai := S.average_integrable hf.continuous hb n μ
  have he : (∫ x, (S.average f n x-S.average f n 0) ∂μ) =
      (∫ x, f x ∂μ) - S.average f n 0 := by
    rw [integral_sub hai (integrable_const _),S.integral_average μ hμ hf.continuous hb]
    simp
  have hbound : ∀ᵐ x ∂μ, ‖S.average f n x-S.average f n 0‖ ≤ ε/2 := by
    filter_upwards [show ∀ᵐ x ∂μ, x ∈ Icc (-B) B from ae_iff.mpr hBc] with x hx
    rw [Real.norm_eq_abs]
    apply S.average_difference hc.le hr (fun x y h => (hd (by simpa [Real.dist_eq] using h)).le)
    calc
      |x-0| *c^n ≤ B*c^n := mul_le_mul_of_nonneg_right (by simpa using abs_le.mpr hx)
        (pow_nonneg hc.le n)
      _ < δ := hN n hn
  have hnorm := norm_integral_le_of_norm_le_const hbound
  rw [he] at hnorm
  have hh : |(∫ x, f x ∂μ)-S.average f n 0| ≤ ε/2 := by simpa using hnorm
  rw [Real.dist_eq,abs_sub_comm]
  linarith

theorem selfSimilar_unique (S : System ι) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : S.SelfSimilar μ) (hν : S.SelfSimilar ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hf := f.hasCompactSupport.uniformContinuous_of_continuous f.continuous
  have hb : ∀ x, |f x| ≤ ‖f.toBoundedContinuousFunction‖ := fun x => by
    have hh := f.toBoundedContinuousFunction.norm_coe_le_norm x
    have he : f.toBoundedContinuousFunction x = f x := rfl
    rw [he,Real.norm_eq_abs] at hh
    exact hh
  exact tendsto_nhds_unique (S.tendsto_average_at_zero μ hμ hf hb)
    (S.tendsto_average_at_zero ν hν hf hb)

end EntropyRateDimension.System

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

end System

namespace BallRatios
theorem massReal_pos (μ : Measure ℝ) [IsFiniteMeasure μ] {x r : ℝ}
    (hx : x ∈ μ.support) (hr : 0 < r) : 0 < μ.real (closedBall x r) := by
  exact ENNReal.toReal_pos (ne_of_gt ((Measure.mem_support_iff_forall x).mp hx _
    (closedBall_mem_nhds x hr))) (measure_ne_top μ _)

end BallRatios

namespace Coding
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

end Coding
end EntropyRateDimension

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

theorem information_antitone (μ : Measure ℝ) [IsProbabilityMeasure μ] {x r s : ℝ}
    (hx : x ∈ μ.support) (hr : 0 < r) (hrs : r ≤ s) :
    information μ x s ≤ information μ x r := by
  apply neg_le_neg
  apply Real.log_le_log (massReal_pos μ hx hr)
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (closedBall_subset_closedBall hrs))

end EntropyRateDimension.BallRatios

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

-- ---- from OAI.MeasureTheory.SelfSimilar.RadiusGrowth ----
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
open EntropyRateDimension.ErgodicAux
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_2
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_2
theorem infoRate_nonneg (S : System ι) : 0 ≤ infoRate S := by
  obtain ⟨ω,hω⟩ := (ae_prefixInfo_limit S).exists
  exact ge_of_tendsto' hω (fun n => div_nonneg
    (BallRatios.information_nonneg _ _ _) (Nat.cast_nonneg n))

theorem exponent_nonneg (S : System ι) : 0 ≤ exponent S :=
  div_nonneg (infoRate_nonneg S) (mul_pos S.lyapunov_pos (Real.log_pos (by norm_num))).le

end EntropyRateDimension.Coding

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.ExactDimension ----
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
open Set Filter
open scoped Topology
namespace EntropyRateDimension.BallRatios
open MeasureTheory Metric Set Filter
open scoped Topology

theorem radial_limit_of_integer (μ : Measure ℝ) [IsProbabilityMeasure μ] {x d : ℝ}
    (hx : x ∈ μ.support)
    (hlim : Tendsto (fun n : ℕ => information μ x (Real.exp (-(n : ℝ))) / (n : ℝ))
      atTop (𝓝 d)) :
    Tendsto (fun r => information μ x r / -Real.log r) (𝓝[>] 0) (𝓝 d) := by
  let F : ℝ → ℝ := fun s => information μ x (Real.exp (-s))
  have hF : Monotone F := fun a b hab => information_antitone μ hx (Real.exp_pos _)
    (Real.exp_le_exp.mpr (neg_le_neg hab))
  have hfull := Interpolation.tendsto_div_of_bounded_gaps hF Nat.mono_cast (by simp)
    (C := 1) (fun n => by push_cast; exact le_rfl) tendsto_natCast_atTop_atTop hlim
  apply (hfull.comp (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)).congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  simp only [Function.comp_def,F,neg_neg,Real.exp_log hr]

end EntropyRateDimension.BallRatios

namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter
open scoped Topology
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_4
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_4
theorem ae_radial_limit (S : System ι) : ∀ᵐ x ∂law S,
    Tendsto (fun r => BallRatios.information (law S) x r / -Real.log r)
      (𝓝[>] 0) (𝓝 (exponent S)) := by
  filter_upwards [ae_radial_sequence S,(law S).support_mem_ae] with x hlim hx
  exact BallRatios.radial_limit_of_integer _ hx hlim

end EntropyRateDimension.Coding

namespace EntropyRateDimension.System
open MeasureEntropy
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.System.instMeasurableSpace
attribute [local instance] OAI.EntropyRateDimension.System.instMeasurableSingletonClass
theorem selfSimilar_radial (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => -Real.log (μ.real (Metric.closedBall x r)) / -Real.log r)
      (𝓝[>] 0) (𝓝 (Coding.exponent S)) := by
  have he := S.selfSimilar_unique μ (Coding.law S) hμ (Coding.law_selfSimilar S)
  subst μ
  exact Coding.ae_radial_limit S

theorem selfSimilar_dimension (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) :
    lowerHausdorffDimension μ = ENNReal.ofReal (Coding.exponent S) :=
  LocalMass.lower_dim_eq_of_limit μ (by obtain ⟨B,hB,hc⟩ := S.selfSimilar_compact μ hμ; exact ⟨B,hB.le,hc⟩)
    (Coding.exponent_nonneg S) (S.selfSimilar_radial μ hμ)

theorem selfSimilar_entropy_bound (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) {D : ℝ} (hD : Coding.exponent S < D) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s → s < 1 → averaged μ s ≤ D*Real.log (1/s)+C :=
  entropy_bound_of_radial_limit μ (by obtain ⟨B,hB,hc⟩ := S.selfSimilar_compact μ hμ; exact ⟨B,hB.le,hc⟩)
    (Coding.exponent_nonneg S) hD (S.selfSimilar_radial μ hμ)

end EntropyRateDimension.System

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

theorem wordWeight_cons (S : System ι) {n : ℕ} (i : ι) (w : Fin n → ι) :
    S.wordWeight (Fin.cons i w) = S.weight i*S.wordWeight w := by
  simp only [wordWeight,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem mapMass_dot (S : System ι) (n : ℕ) (f : ℝ × ℝ → ℝ) :
    (∑ g ∈ S.mapSupport n, S.mapMass n g*f g) = ∑ w : Fin n → ι, S.wordWeight w*f (S.completeMap w) := by
  classical
  exact FiniteEntropy.sum_mass_mul _ _ _ _ _ (fun w hw => Finset.mem_image_of_mem _ hw)

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

theorem completeMap_log_slope (S : System ι) {n : ℕ} (w : Fin n → ι) :
    Real.log |(S.completeMap w).1| = ∑ j, Real.log |S.ratio (w j)| := by
  rw [completeMap_slope,Finset.abs_prod,Real.log_prod]
  exact fun j _ => (S.ratio_pos (w j)).ne'

theorem selfSimilar_compressed (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ)
    {n : ℕ} (hn : 0 < n) : (S.compressed hn).SelfSimilar μ := by
  classical
  change μ = ∑ g : S.mapSupport n, ENNReal.ofReal (S.mapMass n g.val) •
    μ.map (fun x => g.val.1*x+g.val.2)
  rw [Finset.sum_coe_sort (S.mapSupport n) (fun g => ENNReal.ofReal (S.mapMass n g) •
    μ.map (fun x => g.1*x+g.2))]
  simp only [mapMass,ENNReal.ofReal_sum_of_nonneg (fun w _ => (S.wordWeight_pos w).le),Finset.sum_smul]
  have he : ∀ g ∈ S.mapSupport n,
      (∑ w ∈ (Finset.univ : Finset (Fin n → ι)).filter (S.completeMap · = g),
        ENNReal.ofReal (S.wordWeight w) • μ.map (fun x => g.1*x+g.2)) =
      ∑ w ∈ (Finset.univ : Finset (Fin n → ι)).filter (S.completeMap · = g),
        ENNReal.ofReal (S.wordWeight w) • μ.map (S.wordMap w) := by
    intro g _
    apply Finset.sum_congr rfl
    intro w hw
    rw [← (Finset.mem_filter.mp hw).2]
    rfl
  simp_rw [Finset.sum_congr rfl he]
  rw [Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S.mapSupport n)
    (g := S.completeMap (n := n)) (fun w hw => Finset.mem_image_of_mem _ hw)]
  exact S.selfSimilar_words μ hμ n

theorem compressed_lyapunov (S : System ι) {n : ℕ} (hn : 0 < n) :
    (S.compressed hn).lyapunov = (n : ℝ)*S.lyapunov := by
  classical
  change -(∑ g : S.mapSupport n, S.mapMass n g.val*(Real.log |g.val.1|/Real.log 2)) = _
  rw [Finset.sum_coe_sort (S.mapSupport n) (fun g => S.mapMass n g*(Real.log |g.1|/Real.log 2)),
    S.mapMass_dot]
  simp_rw [completeMap_log_slope,Finset.sum_div]
  rw [S.wordWeight_expect_sum (fun i => Real.log |S.ratio i|/Real.log 2)]
  simp only [lyapunov]
  ring

theorem compressed_symbol_entropy (S : System ι) {n : ℕ} (hn : 0 < n) :
    (∑ g : S.mapSupport n, Real.negMulLog ((S.compressed hn).weight g)) =
      S.walkEntropy n*Real.log 2 := by
  classical
  change (∑ g : S.mapSupport n, Real.negMulLog (S.mapMass n g.val)) = _
  rw [Finset.sum_coe_sort (S.mapSupport n) (fun g => Real.negMulLog (S.mapMass n g)),walkEntropy,
    div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne']

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
theorem mapSupport_nonempty (S : System ι) (n : ℕ) : (S.mapSupport n).Nonempty := by
  classical
  exact Finset.image_nonempty.mpr Finset.univ_nonempty

theorem exponent_le_walkEntropy (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) {n : ℕ} (hn : 0 < n) :
    Coding.exponent S*S.lyapunov ≤ S.walkEntropy n/(n : ℝ) := by
  classical
  have : Nonempty (S.mapSupport n) := (S.mapSupport_nonempty n).to_subtype
  have he : Coding.exponent S = Coding.exponent (S.compressed hn) := by
    apply (ENNReal.ofReal_eq_ofReal_iff (Coding.exponent_nonneg S) (Coding.exponent_nonneg _)).mp
    rw [← S.selfSimilar_dimension μ hμ, ← (S.compressed hn).selfSimilar_dimension μ
      (S.selfSimilar_compressed μ hμ hn)]
  have hb := Coding.exponent_symbol_entropy_bound (S.compressed hn)
  rw [compressed_lyapunov,compressed_symbol_entropy,← he] at hb
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul : Coding.exponent S*S.lyapunov*(n : ℝ) ≤ S.walkEntropy n := by
    apply (mul_le_mul_iff_left₀ hlog).mp
    nlinarith [hb]
  exact (le_div_iff₀ (by exact_mod_cast hn)).mpr hmul

theorem exponent_le_rate (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) : Coding.exponent S ≤ S.entropyRate/S.lyapunov := by
  apply (le_div_iff₀ S.lyapunov_pos).mpr
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨n,rfl⟩
  exact S.exponent_le_walkEntropy μ hμ (Nat.succ_pos n)

theorem exponent_le_one (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) : Coding.exponent S ≤ 1 := by
  have hh := lowerHausdorffDimension_le_one μ
  rw [S.selfSimilar_dimension μ hμ] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp
    (by simpa only [ENNReal.ofReal_one] using hh)

end EntropyRateDimension.System

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.BlockWords ----
namespace OAI

universe uι uα uβ uγ

namespace EntropyRateDimension.FiniteEntropy
open scoped BigOperators

end EntropyRateDimension.FiniteEntropy

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

theorem selfSimilar_blocks (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ)
    {b : ℕ} (hb : 0 < b) : (S.blocks hb).SelfSimilar μ := S.selfSimilar_words μ hμ b

theorem blocks_lyapunov (S : System ι) {b : ℕ} (hb : 0 < b) :
    (S.blocks hb).lyapunov=(b : ℝ)*S.lyapunov := by
  simp only [lyapunov,blocks,S.completeMap_log_slope,Finset.sum_div]
  rw [S.wordWeight_expect_sum (fun i => Real.log |S.ratio i|/Real.log 2)]
  ring

end EntropyRateDimension.System

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.Main ----
namespace OAI

universe uι

namespace EntropyRateDimension
open MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal

theorem exists_slightly_larger_depth {d χ h : ℝ} (hd : 0 ≤ d) (hgap : d*χ < h) :
    ∃ a : ℝ, χ < a ∧ d*a < h := by
  let t := (h-d*χ)/(2*(d+1))
  have hp : 0 < 2*(d+1) := by linarith
  have ht : 0 < t := div_pos (sub_pos.mpr hgap) hp
  have he : t*(2*(d+1))=h-d*χ := div_mul_cancel₀ _ hp.ne'
  refine ⟨χ+t,by linarith,?_⟩
  nlinarith

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.System.instMeasurableSpace_2
attribute [local instance] OAI.EntropyRateDimension.System.instMeasurableSingletonClass_2
theorem exponent_lower_bound (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) : min 1 (S.entropyRate/S.lyapunov) ≤ Coding.exponent S := by
  classical
  by_contra! hstrict
  obtain ⟨d,hed,hdm⟩ := exists_between hstrict
  have hd : 0 ≤ d := (Coding.exponent_nonneg S).trans hed.le
  have hd1 : d < 1 := hdm.trans_le (min_le_left _ _)
  have hdr : d < S.entropyRate/S.lyapunov := hdm.trans_le (min_le_right _ _)
  have hdh : d*S.lyapunov < S.entropyRate := (lt_div_iff₀ S.lyapunov_pos).mp hdr
  obtain ⟨a,hχa,hda⟩ := exists_slightly_larger_depth hd hdh
  have hap : 0 < a := S.lyapunov_pos.trans hχa
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hε : 0 < (S.entropyRate-d*a)*Real.log 2 := mul_pos (sub_pos.mpr hda) hl
  obtain ⟨b,hb,hbtype⟩ := exists_nat_log_small hε (Fintype.card ι)
  have hbR : (0 : ℝ)<b := by exact_mod_cast hb
  have htype : Real.log (Fintype.card (ι → Fin (b+1)))=
      (Fintype.card ι : ℝ)*Real.log ((b : ℝ)+1) := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Real.log_pow,Nat.cast_add,Nat.cast_one]
  have hblock : (b : ℝ)*S.entropyRate ≤ (S.blocks hb).entropyRate := S.blocks_entropyRate_lower hb
  have hgap : d*((b : ℝ)*a)*Real.log 2 < (S.blocks hb).entropyRate*Real.log 2-
      Real.log (Fintype.card (ι → Fin (b+1))) := by
    rw [htype]
    have hh := mul_le_mul_of_nonneg_right hblock hl.le
    nlinarith
  obtain ⟨C,hC⟩ := S.selfSimilar_entropy_bound μ hμ hed
  apply Typed.no_strict_entropy_gap (S.blocks hb) (wordType (ι := ι)) (S.ratio_wordType hb)
    μ (S.selfSimilar_blocks μ hμ hb) hd hd1 (mul_pos hbR hap)
    (A' := (b : ℝ)*((S.lyapunov+a)/2)) _ _ hC hgap
  · rw [S.blocks_lyapunov]
    exact mul_lt_mul_of_pos_left (by linarith) hbR
  · exact mul_lt_mul_of_pos_left (by linarith) hbR

end System

theorem entropy_rate_dimension {ι : Type uι} [Fintype ι] [Nonempty ι]
    (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) :
    lowerHausdorffDimension μ = ENNReal.ofReal (min 1 (S.entropyRate / S.lyapunov)) := by
  rw [S.selfSimilar_dimension μ hμ]
  congr 1
  exact le_antisymm (le_min (S.exponent_le_one μ hμ) (S.exponent_le_rate μ hμ)) (S.exponent_lower_bound μ hμ)

end EntropyRateDimension

end OAI

-- ---- mission target ----
open OAI OAI.EntropyRateDimension
universe uι
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory
open MeasureTheory MeasureEntropy

namespace OAI
namespace EntropyRateDimension
theorem _root_.solution {ι : Type uι} [Fintype ι] [Nonempty ι]
    (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) :
    lowerHausdorffDimension μ = ENNReal.ofReal (min 1 (S.entropyRate / S.lyapunov)) := by
  first
    | exact OAI.EntropyRateDimension.entropy_rate_dimension S μ hμ
    | exact OAI.EntropyRateDimension.entropy_rate_dimension
    | (apply OAI.EntropyRateDimension.entropy_rate_dimension <;> assumption)
    | (intros; apply OAI.EntropyRateDimension.entropy_rate_dimension <;> assumption)
end EntropyRateDimension
end OAI
