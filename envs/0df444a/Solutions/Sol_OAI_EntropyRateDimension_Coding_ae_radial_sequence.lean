-- Prove2me | solution 1 for OAI.EntropyRateDimension.Coding.ae_radial_sequence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:18:46.524452+00:00
-- url     : https://prove2.me/submissions/d9a3e562-236b-41f0-b469-b2b9dbcf4549

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/RadialLimit.lean:L73-L88
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Coding.ae_radial_sequence. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_Coding_ae_prefixInfo_limit
import Theorems.Thm_OAI_EntropyRateDimension_ErgodicAux_ae_tendsto_average
import Theorems.Thm_OAI_EntropyRateDimension_Interpolation_tendsto_div_of_bounded_gaps

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

omit [MeasurableSpace α] in
theorem shift_iterate (n : ℕ) (ω : ℕ → α) (k : ℕ) :
    shift^[n] ω k = ω (k+n) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', shift, ih]
    congr 1
    omega

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

omit [Nonempty ι] in
theorem slope_ne_zero (S : System ι) (ω : ℕ → ι) (n : ℕ) : slope S ω n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact abs_pos.mp (S.ratio_pos (ω j))

omit [Nonempty ι] in
theorem abs_slope_pos (S : System ι) (ω : ℕ → ι) (n : ℕ) : 0 < |slope S ω n| :=
  abs_pos.mpr (slope_ne_zero S ω n)

theorem slope_tendsto_zero (S : System ι) (ω : ℕ → ι) :
    Tendsto (fun n => |slope S ω n|) atTop (𝓝 0) := by
  obtain ⟨c,T,hc,hc1,_,hr,_⟩ := S.exists_uniform_bounds
  exact squeeze_zero (fun n => abs_nonneg _) (abs_slope_le S ω hc.le hr)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1)

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
theorem head_integrable (S : System ι) (f : ι → ℝ) :
    Integrable (fun ω : ℕ → ι => f (ω 0)) (addressMeasure S) := by
  classical
  apply Integrable.of_bound ((measurable_of_finite f).comp (measurable_pi_apply 0)).aestronglyMeasurable
    (∑ i, |f i|)
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_univ (ω 0))

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

theorem ae_point_support (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    ∀ j : ℕ, point S (shift^[j] ω) ∈ (law S).support := by
  apply ae_all_iff.mpr
  intro j
  have ha : ∀ᵐ ω ∂addressMeasure S, point S ω ∈ (law S).support :=
    ae_of_ae_map (point_measurable S).aemeasurable (law S).support_mem_ae
  exact ((show MeasurePreserving shift (addressMeasure S) (addressMeasure S) from
      shift_preserving (symbolMeasure S)).iterate j).quasiMeasurePreserving.ae ha

end EntropyRateDimension.Coding

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
omit [Fintype ι] [Nonempty ι] in
theorem shift_iterate (n : ℕ) (ω : ℕ → ι) (k : ℕ) : shift^[n] ω k = ω (k+n) :=
  Bernoulli.shift_iterate n ω k

omit [Nonempty ι] in
theorem contraction_integral (S : System ι) :
    (∫ ω, contractionObs S ω ∂addressMeasure S) = S.lyapunov * Real.log 2 := by
  change (∫ ω, -Real.log |S.ratio (ω 0)| ∂addressMeasure S) = _
  rw [head_integral S (fun i => -Real.log |S.ratio i|)]
  unfold System.lyapunov
  rw [neg_mul,Finset.sum_mul]
  simp only [mul_assoc,div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne',
    mul_neg,Finset.sum_neg_distrib]

omit [Nonempty ι] in
theorem slope_log_sum (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    -Real.log |slope S ω n| = birkhoffSum shift (contractionObs S) n ω := by
  induction n with
  | zero => simp [slope_zero,birkhoffSum]
  | succ n ih =>
    rw [slope_succ,abs_mul,Real.log_mul (abs_slope_pos S ω n).ne' (S.ratio_pos _).ne',
      neg_add,ih,birkhoffSum_succ]
    simp only [contractionObs,shift_iterate,zero_add]

omit [Nonempty ι] in
theorem ae_slope_log_limit (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => -Real.log |slope S ω n| / (n : ℝ)) atTop
      (𝓝 (S.lyapunov * Real.log 2)) := by
  have hT : Ergodic shift (addressMeasure S) := Bernoulli.shift_ergodic (symbolMeasure S)
  have hm : Measurable (contractionObs S) :=
    (measurable_of_finite (fun i => -Real.log |S.ratio i|)).comp (measurable_pi_apply 0)
  have hi : Integrable (contractionObs S) (addressMeasure S) := head_integrable S (fun i => -Real.log |S.ratio i|)
  have hh := ae_tendsto_average hT hm hi
  rw [contraction_integral] at hh
  simpa only [slope_log_sum] using hh

theorem ae_prefix_exponent (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => prefixInfo S n ω / -Real.log |slope S ω n|) atTop (𝓝 (exponent S)) := by
  filter_upwards [ae_prefixInfo_limit S,ae_slope_log_limit S] with ω hI hR
  have hh := hI.div hR (mul_pos S.lyapunov_pos (Real.log_pos (by norm_num))).ne'
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp only [Pi.div_apply]
  field_simp

end EntropyRateDimension.Coding

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.RadialLimit ----
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
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_3
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_3
omit [Nonempty ι] in
theorem slope_log_succ (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    -Real.log |slope S ω (n+1)| = -Real.log |slope S ω n| + -Real.log |S.ratio (ω n)| := by
  rw [slope_succ,abs_mul,Real.log_mul (abs_slope_pos S ω n).ne' (S.ratio_pos _).ne',neg_add]

omit [Nonempty ι] in
theorem ratio_log_pos (S : System ι) (i : ι) : 0 < -Real.log |S.ratio i| :=
  neg_pos.mpr (Real.log_neg (S.ratio_pos i) (S.ratio_lt_one i))

theorem radial_limit_of_prefix (S : System ι) (ω : ℕ → ι)
    (hx : point S ω ∈ (law S).support)
    (hlim : Tendsto (fun n => prefixInfo S n ω / -Real.log |slope S ω n|)
      atTop (𝓝 (exponent S))) :
    Tendsto (fun r => BallRatios.information (law S) (point S ω) r / -Real.log r)
      (𝓝[>] 0) (𝓝 (exponent S)) := by
  let F : ℝ → ℝ := fun t => BallRatios.information (law S) (point S ω) (Real.exp (-t))
  let t : ℕ → ℝ := fun n => -Real.log |slope S ω n|
  have hF : Monotone F := by
    intro a b hab
    exact BallRatios.information_antitone _ hx (Real.exp_pos _)
      (Real.exp_le_exp.mpr (neg_le_neg hab))
  have ht : Monotone t := monotone_nat_of_le_succ fun n => by
    dsimp only [t]
    rw [slope_log_succ]
    exact le_add_of_nonneg_right (ratio_log_pos S _).le
  have ht0 : t 0=0 := by simp [t,slope_zero]
  have hstep : ∀ n, t (n+1) ≤ t n + ∑ i, -Real.log |S.ratio i| := by
    intro n
    dsimp only [t]
    rw [slope_log_succ]
    exact add_le_add_right (Finset.single_le_sum (fun i _ => (ratio_log_pos S i).le)
      (Finset.mem_univ (ω n))) _
  have hrtop : Tendsto (fun n => |slope S ω n|) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨slope_tendsto_zero S ω,
      Eventually.of_forall (fun n => abs_slope_pos S ω n)⟩
  have htop : Tendsto t atTop atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hrtop)
  have hlim' : Tendsto (fun n => F (t n)/t n) atTop (𝓝 (exponent S)) := by
    simpa only [F,t,neg_neg,Real.exp_log (abs_slope_pos S ω _),prefixInfo] using hlim
  have hfull := Interpolation.tendsto_div_of_bounded_gaps hF ht ht0 hstep htop hlim'
  have hlog : Tendsto (fun r : ℝ => -Real.log r) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  apply (hfull.comp hlog).congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  simp only [Function.comp_def,F,neg_neg,Real.exp_log hr]

theorem ae_radial_sequence (S : System ι) : ∀ᵐ x ∂law S,
    Tendsto (fun n : ℕ => BallRatios.information (law S) x (Real.exp (-(n : ℝ))) / (n : ℝ))
      atTop (𝓝 (exponent S)) := by
  have hseq : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝[>] 0) :=
    Real.tendsto_exp_atBot_nhdsGT.comp
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hm (n : ℕ) : Measurable (fun x : ℝ =>
      BallRatios.information (law S) x (Real.exp (-(n : ℝ))) / (n : ℝ)) := by
    have hs : MeasurableSet {z : ℝ × ℝ | dist z.2 z.1 ≤ Real.exp (-(n : ℝ))} :=
      measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
    have hmass := measurable_measure_prodMk_left (ν := law S) hs
    exact hmass.ennreal_toReal.log.neg.div_const _
  apply (ae_map_iff (point_measurable S).aemeasurable (measurableSet_tendsto _ hm)).mpr
  filter_upwards [ae_prefix_exponent S,ae_point_support S] with ω hlim hs
  have hr := (radial_limit_of_prefix S ω (by simpa using hs 0) hlim).comp hseq
  simpa only [Function.comp_def,Real.log_exp,neg_neg] using hr

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
open Set Filter
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_3
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_3


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.Coding.ae_radial_sequence.{uι} := @_root_.OAI.EntropyRateDimension.Coding.ae_radial_sequence.{uι}
