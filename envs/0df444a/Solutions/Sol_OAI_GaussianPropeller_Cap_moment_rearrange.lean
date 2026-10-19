-- Prove2me | solution 1 for OAI.GaussianPropeller.Cap.moment_rearrange
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:11:17.756817+00:00
-- url     : https://prove2.me/submissions/c7ec0562-6c02-4093-a0d6-033b1b12f3f0

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/CapBounds.lean:L145-L178
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Cap.moment_rearrange. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_ResidualBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Polar
import Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_Coordinates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapBounds
import Theorems.Thm_OAI_GaussianPropeller_Cap_integral_cone_norm

-- ---- from OAI.Probability.GaussianPropeller.OneCell ----
namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace GaussianPropeller.OneCell

lemma mul_density_integrable : Integrable (fun x : ℝ => x*density x) := by
  simpa only [density, show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring]
    using integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)

lemma hasDerivAt_density (x : ℝ) : HasDerivAt density (-x*density x) x := by
  unfold density
  convert (((hasDerivAt_pow 2 x).neg.div_const 2).exp) using 1 <;>
  first | rfl | (solve | ring) | (dsimp; ring)

lemma tendsto_density : Tendsto density atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  convert (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num : (-(1/2:ℝ)) < 0) using 1
  ext x
  ring

lemma tail_first_moment (a : ℝ) : ∫ x in Ioi a, x*density x = density a := by
  have hd (x : ℝ) : HasDerivAt (fun x => -density x) (x*density x) x := by
    convert (hasDerivAt_density x).neg using 1 <;> first | rfl | ring
  have ht : Tendsto (fun x => -density x) atTop (𝓝 (-0)) := tendsto_density.neg
  simpa only [neg_zero, zero_sub, neg_neg] using
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
      mul_density_integrable.integrableOn ht

lemma integral_gaussianReal_std (f : ℝ → ℝ) :
    ∫ x, f x ∂gaussianReal 0 1 = gaussianConst * ∫ x, f x*density x := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, smul_eq_mul, gaussianConst, density]
  ring

section GeneralCell
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GeneralCell
end GaussianPropeller.OneCell

end OAI

-- ---- from OAI.Probability.GaussianPropeller.CapIntegral ----
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

lemma p_eq_integral_indicator (a : ℝ) :
    p a = ∫ x : ℝ, (Ioi a).indicator (fun _ => (1:ℝ)) x ∂gaussianReal 0 1 := by
  rw [integral_gaussianReal_std]
  have he : (fun x : ℝ => (Ioi a).indicator (fun _ => (1:ℝ)) x*density x) =
      (Ioi a).indicator density := by
    funext x
    by_cases hx : x∈Ioi a <;> simp [hx]
  rw [he,integral_indicator measurableSet_Ioi]
  rfl

variable {n : ℕ}
end GaussianPropeller.Cap

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Coordinates ----
namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Coords
lemma split_measure (n : ℕ) :
    (stdGaussian (CS (n+1))).map (split n) = (gaussianReal 0 1).prod (stdGaussian (CS n)) := by
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) 0).map_eq
  have he : (split n) ∘ WithLp.toLp 2 =
      (Prod.map (id : ℝ → ℝ) (WithLp.toLp 2)) ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0) := by
    funext x
    rfl
  rw [← map_pi_eq_stdGaussian, Measure.map_map (continuous_split n).measurable
    (PiLp.continuous_toLp 2 _).measurable, he,
    ← Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _),hm,
    ← Measure.map_prod_map _ _ measurable_id (PiLp.continuous_toLp 2 _).measurable,
    Measure.map_id,map_pi_eq_stdGaussian]

lemma measurePreserving_split (n : ℕ) : MeasurePreserving (splitEquiv n)
    (stdGaussian (CS (n+1))) ((gaussianReal 0 1).prod (stdGaussian (CS n))) :=
  ⟨(continuous_split n).measurable,split_measure n⟩

lemma integral_split (n : ℕ) (f : CS (n+1) → ℝ) :
    (∫ x, f x ∂stdGaussian (CS (n+1))) =
      ∫ y, f (join n y) ∂(gaussianReal 0 1).prod (stdGaussian (CS n)) := by
  exact ((measurePreserving_split n).symm.integral_comp (splitEquiv n).symm.measurableEmbedding f).symm

lemma norm_join_sq (n : ℕ) (y : ℝ × CS n) : ‖join n y‖^2 = y.1^2+‖y.2‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,join,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ]

end GaussianPropeller.Coords

end OAI

-- ---- from OAI.Probability.GaussianPropeller.CapBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Cap
open Coords OneCell ProbabilityBounds Polar
open scoped Topology
variable {n : ℕ}

lemma measurableSet_coneCap (n : ℕ) (a : ℝ) : MeasurableSet (coneCap n a) := by
  apply isOpen_lt (by exact continuous_const.mul ((continuous_split n).snd.norm)) (by fun_prop) |>.measurableSet

lemma coneCap_smul (a : ℝ) {r : ℝ} (hr : 0<r) (x : CE (n+1)) :
    r•x∈coneCap n a ↔ x∈coneCap n a := by
  have he : (split n (r•x)).2 = r•(split n x).2 := by ext i; rfl
  simp only [coneCap,mem_ofPred_eq,he,norm_smul,Real.norm_eq_abs,abs_of_pos hr,PiLp.smul_apply,smul_eq_mul]
  rw [← mul_assoc, mul_comm a r, mul_assoc, mul_lt_mul_iff_right₀ hr]

lemma integrable_coord : Integrable (fun x : CE (n+1) => x 0) (stdGaussian (CE (n+1))) := by
  apply Integrable.mono' IsGaussian.integrable_id.norm (by fun_prop)
  filter_upwards [] with x
  exact PiLp.norm_apply_le x 0

lemma tail_first_gaussian (a : ℝ) : ∫ x in Ioi a, x ∂gaussianReal 0 1 = gaussianConst*density a := by
  rw [← integral_indicator measurableSet_Ioi,integral_gaussianReal_std]
  have he : (fun x : ℝ => (Ioi a).indicator (fun x=>x) x*density x) =
      (Ioi a).indicator (fun x => x*density x) := by
    funext x
    by_cases hx : x∈Ioi a <;> simp [hx]
  rw [he,integral_indicator measurableSet_Ioi,tail_first_moment]

lemma integral_cap (n : ℕ) (a : ℝ) :
    ∫ x : CE (n+1), (coneCap n a).indicator (fun _ => (1:ℝ)) x ∂stdGaussian (CE (n+1)) = capP n a := by
  rw [integral_split]
  have hi : Integrable (fun y => (coneCap n a).indicator (fun _ => (1:ℝ)) (join n y))
      ((gaussianReal 0 1).prod (stdGaussian (CE n))) :=
    ((measurePreserving_split n).symm.integrable_comp
      (((integrable_const (1:ℝ)).indicator (measurableSet_coneCap n a)).aestronglyMeasurable)).mpr
      ((integrable_const (1:ℝ)).indicator (measurableSet_coneCap n a))
  rw [integral_prod_symm _ hi]
  unfold capP
  apply integral_congr_ae
  filter_upwards [] with y
  rw [p_eq_integral_indicator]
  rfl

lemma moment_cap (n : ℕ) (a : ℝ) :
    ∫ x : CE (n+1), (coneCap n a).indicator (fun x => x 0) x ∂stdGaussian (CE (n+1)) = capM n a := by
  rw [integral_split]
  have hi : Integrable (fun y => (coneCap n a).indicator (fun x => x 0) (join n y))
      ((gaussianReal 0 1).prod (stdGaussian (CE n))) :=
    ((measurePreserving_split n).symm.integrable_comp
      ((integrable_coord.indicator (measurableSet_coneCap n a)).aestronglyMeasurable)).mpr
      (integrable_coord.indicator (measurableSet_coneCap n a))
  rw [integral_prod_symm _ hi]
  unfold capM
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← tail_first_gaussian,← integral_indicator measurableSet_Ioi]
  rfl

lemma coneCap_criterion {a : ℝ} (ha : 0≤a) (x : CE (n+1)) :
    x∈coneCap n a ↔ a/Real.sqrt (1+a^2)*‖x‖ < x 0 := by
  have hp : 0 < Real.sqrt (1+a^2) := by positivity
  have hs := Real.sq_sqrt (show 0≤1+a^2 by positivity)
  have hn := norm_join_sq n (split n x)
  rw [join_split] at hn
  change ‖x‖^2 = (x 0)^2+‖(split n x).2‖^2 at hn
  change a*‖(split n x).2‖ < x 0 ↔ _
  rw [div_mul_eq_mul_div, div_lt_iff₀ hp]
  constructor
  · intro h
    have hx : 0 < x 0 := lt_of_le_of_lt (by positivity) h
    have hs1 : (a*‖(split n x).2‖)^2 < (x 0)^2 := sq_lt_sq₀ (by positivity) hx.le |>.mpr h
    have hs2 : (a*‖x‖)^2 < (x 0*Real.sqrt (1+a^2))^2 := by nlinarith only [hs1,hn,hs]
    exact (sq_lt_sq₀ (by positivity) (by positivity)).mp hs2
  · intro h
    have hx : 0 < x 0 := (mul_pos_iff_of_pos_right hp).mp (lt_of_le_of_lt (by positivity) h)
    have hs1 : (a*‖x‖)^2 < (x 0*Real.sqrt (1+a^2))^2 := (sq_lt_sq₀ (by positivity) (by positivity)).mpr h
    have hs2 : (a*‖(split n x).2‖)^2 < (x 0)^2 := by nlinarith only [hs1,hn,hs]
    exact (sq_lt_sq₀ (by positivity) hx.le).mp hs2

lemma moment_rearrange (K : Set (CE (n+1))) (hK : MeasurableSet K)
    (hcone : ∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K) {a : ℝ} (ha : 0≤a) :
    (∫ x : CE (n+1), K.indicator (fun x=>x 0) x ∂stdGaussian (CE (n+1))) ≤
      capM n a + a/Real.sqrt (1+a^2) * (radial (n+1) (1/2)/radial n (1/2)) *
        ((stdGaussian (CE (n+1))).real K-capP n a) := by
  let b := a/Real.sqrt (1+a^2)
  let C := coneCap n a
  have hn : Integrable (fun x : CE (n+1)=>‖x‖) (stdGaussian (CE (n+1))) := IsGaussian.integrable_id.norm
  have hf : Integrable (fun x : CE (n+1)=> x 0-b*‖x‖) (stdGaussian (CE (n+1))) :=
    integrable_coord.sub (hn.const_mul b)
  have hi := integral_mono (hf.indicator hK) (hf.indicator (measurableSet_coneCap n a)) (fun x => show
      K.indicator (fun x=>x 0-b*‖x‖) x ≤ C.indicator (fun x=>x 0-b*‖x‖) x from by
    by_cases hk : x∈K <;> by_cases hc : x∈C
    · simp [hk,hc]
    · simp only [indicator_of_mem hk,indicator_of_notMem hc]
      exact sub_nonpos.mpr (not_lt.mp (mt (coneCap_criterion ha x).mpr hc))
    · simp only [indicator_of_notMem hk,indicator_of_mem hc]
      exact sub_nonneg.mpr ((coneCap_criterion ha x).mp hc).le
    · simp [hk,hc])
  simp_rw [indicator_sub,indicator_const_mul] at hi
  rw [integral_sub (integrable_coord.indicator hK) ((hn.indicator hK).const_mul b),
    integral_const_mul,
    integral_sub (integrable_coord.indicator (measurableSet_coneCap n a))
      ((hn.indicator (measurableSet_coneCap n a)).const_mul b),integral_const_mul,
    integral_cone_norm (by omega) K hK hcone,
    integral_cone_norm (by omega) C (measurableSet_coneCap n a) (fun r hr x=>coneCap_smul a hr x),
    moment_cap,show n+1-1=n by omega] at hi
  have hp : (stdGaussian (CE (n+1))).real C = capP n a := by
    rw [← integral_cap,integral_indicator (measurableSet_coneCap n a),setIntegral_const]
    simp only [smul_eq_mul,mul_one]
    rfl
  rw [hp] at hi
  dsimp [b] at hi
  linarith only [hi]

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

end GaussianPropeller.Cap

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Cap
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open Coords OneCell ProbabilityBounds Polar
open scoped Topology


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Cap.moment_rearrange := @_root_.OAI.GaussianPropeller.Cap.moment_rearrange
