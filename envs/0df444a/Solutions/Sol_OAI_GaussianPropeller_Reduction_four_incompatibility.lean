-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.four_incompatibility
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:59:00.362986+00:00
-- url     : https://prove2.me/submissions/53241041-b238-4f0d-88a4-dc773cfb8ec3

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/FourCells.lean:L65-L157
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.four_incompatibility. The node keeps its source
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
import Definitions.Def_OAI_Probability_GaussianPropeller_CapNumeric
import Definitions.Def_OAI_Probability_GaussianPropeller_Geometry
import Definitions.Def_OAI_Probability_GaussianPropeller_QuarticCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_Scalar
import Theorems.Thm_OAI_GaussianPropeller_FourAlgebra_small_exclusion
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_affine_from_cap
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_0
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_1
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_10
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_11
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_12
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_13
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_14
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_15
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_16
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_17
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_18
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_19
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_2
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_20
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_21
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_22
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_23
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_24
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_3
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_4
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_5
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_6
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_7
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_8
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_large_9
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_quartic_of_loss
import Theorems.Thm_OAI_GaussianPropeller_FourCertificates_loss_row
import Theorems.Thm_OAI_GaussianPropeller_ProbabilityBounds_lambda_taylor_upper
import Theorems.Thm_OAI_GaussianPropeller_Taylor_integral_exp_bounds

-- ---- from OAI.Probability.GaussianPropeller.ResidualBounds ----
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

namespace GaussianPropeller.Reduction

open scoped RealInnerProductSpace

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
theorem residualCoefficient_pos {z y : Space d} (h : ⟪z,y⟫ < 0) :
    0 < residualCoefficient z y := by
  have hz : z ≠ 0 := by intro hz; simp [hz] at h
  exact div_pos (neg_pos.mpr h) (sq_pos_of_pos (norm_pos_iff.mpr hz))

end GaussianPropeller.Reduction

end OAI

-- ---- from OAI.Probability.GaussianPropeller.FourReduction ----
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

namespace GaussianPropeller.Reduction
variable {d k : ℕ}

lemma residual_inner_base {z y:Space d} (hz:z≠0) :
    ⟪z,y⟫ = -residualCoefficient z y*‖z‖^2 := by
  unfold residualCoefficient
  field_simp

lemma residual_norm_sq {z y:Space d} (hz:z≠0) :
    ‖residualVector z y‖^2=‖y‖^2-(residualCoefficient z y)^2*‖z‖^2 := by
  rw [residualVector,norm_add_sq_real,real_inner_smul_right,norm_smul]
  rw [real_inner_comm z y,residual_inner_base hz]
  simp only [mul_pow,Real.norm_eq_abs,sq_abs]
  ring

lemma residual_coefficient_sum (z:Fin k→Space d) (hsum:∑ j,z j=0) (i:Fin k) (hi:z i≠0) :
    ∑ j ∈ Finset.univ.erase i,residualCoefficient (z i) (z j)=1 := by
  have hh : ∑ j ∈ Finset.univ.erase i,⟪z i,z j⟫ = -‖z i‖^2 := by
    have he := congrArg (fun y=>⟪z i,y⟫) hsum
    rw [inner_sum,inner_zero_right,← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      real_inner_self_eq_norm_sq] at he
    linarith only [he]
  simp only [residualCoefficient,←Finset.sum_div,Finset.sum_neg_distrib,hh,neg_neg]
  exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hi))

lemma residual_sum (z:Fin k→Space d) (hsum:∑ j,z j=0) (i:Fin k) (hi:z i≠0) :
    ∑ j ∈ Finset.univ.erase i,residualVector (z i) (z j)=0 := by
  have hh : ∑ j ∈ Finset.univ.erase i,z j = -(z i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  simp only [residualVector,Finset.sum_add_distrib,←Finset.sum_smul,
    residual_coefficient_sum z hsum i hi,one_smul,hh,neg_add_cancel]

end GaussianPropeller.Reduction

namespace GaussianPropeller.Reduction
variable {d k:ℕ}

end GaussianPropeller.Reduction

end OAI

-- ---- from OAI.Probability.GaussianPropeller.CapCertificates ----
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

namespace GaussianPropeller.FourCertificates
lemma cap_envelope {r P F:ℝ} (_hP:P≤1/2) (hF:F≤1/2)
    (hcap:r≤(8/3:ℝ)*P*(1-P)) (hpoly:(8/3:ℝ)*F*(1-F)≤r) : F≤P := by
  by_contra hn
  have hd : 0<F-P := sub_pos.mpr (lt_of_not_ge hn)
  have he : 0<(F-P)*(1-P-F) := mul_pos hd (by linarith only [hd,hF])
  nlinarith only [he,hcap,hpoly]

lemma quartic_cap_poly_0 {r:ℝ} (hr:r∈Icc (79/200:ℝ) (637/1200:ℝ)) :
    (8/3:ℝ)*quartic r*(1-quartic r)≤r := by
  have hl : 0≤r-(79/200:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(637/1200:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) =
    (52024221825751854618624/12457785357953028025:ℝ)*(r-(79/200:ℝ))^0*((637/1200:ℝ)-r)^8 + (2022092731453728987242496/12457785357953028025:ℝ)*(r-(79/200:ℝ))^1*((637/1200:ℝ)-r)^7 + (10641317401425423011309568/12457785357953028025:ℝ)*(r-(79/200:ℝ))^2*((637/1200:ℝ)-r)^6 + (24639517032378527009875968/12457785357953028025:ℝ)*(r-(79/200:ℝ))^3*((637/1200:ℝ)-r)^5 + (6174657923095921459389696/2491557071590605605:ℝ)*(r-(79/200:ℝ))^4*((637/1200:ℝ)-r)^4 + (22098785106243529719470592/12457785357953028025:ℝ)*(r-(79/200:ℝ))^5*((637/1200:ℝ)-r)^3 + (8843151939179947854507648/12457785357953028025:ℝ)*(r-(79/200:ℝ))^6*((637/1200:ℝ)-r)^2 + (1795249145491503220347264/12457785357953028025:ℝ)*(r-(79/200:ℝ))^7*((637/1200:ℝ)-r)^1 + (145872797130502554458904/12457785357953028025:ℝ)*(r-(79/200:ℝ))^8*((637/1200:ℝ)-r)^0 := by unfold quartic; ring
  have hp : 0≤r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma quartic_cap_poly_1 {r:ℝ} (hr:r∈Icc (637/1200:ℝ) (479/800:ℝ)) :
    (8/3:ℝ)*quartic r*(1-quartic r)≤r := by
  have hl : 0≤r-(637/1200:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(479/800:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) =
    (37343436065408653941479424/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^0*((479/800:ℝ)-r)^8 + (218329342161991435093303296/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^1*((479/800:ℝ)-r)^7 + (505783344687681532854970368/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^2*((479/800:ℝ)-r)^6 + (586736977997481131452704768/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^3*((479/800:ℝ)-r)^5 + (76177094565115399735178496/2491557071590605605:ℝ)*(r-(637/1200:ℝ))^4*((479/800:ℝ)-r)^4 + (222056334656784469020436992/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^5*((479/800:ℝ)-r)^3 + (200800305393913204441746048/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^6*((479/800:ℝ)-r)^2 + (130431517445084725503713664/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^7*((479/800:ℝ)-r)^1 + (32741625248235314790977304/12457785357953028025:ℝ)*(r-(637/1200:ℝ))^8*((479/800:ℝ)-r)^0 := by unfold quartic; ring
  have hp : 0≤r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma quartic_cap_poly_2 {r:ℝ} (hr:r∈Icc (479/800:ℝ) (2/3:ℝ)) :
    (8/3:ℝ)*quartic r*(1-quartic r)≤r := by
  have hl : 0≤r-(479/800:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(2/3:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) =
    (32741625248235314790977304/12457785357953028025:ℝ)*(r-(479/800:ℝ))^0*((2/3:ℝ)-r)^8 + (15737379461067212446076928/498311414318121121:ℝ)*(r-(479/800:ℝ))^1*((2/3:ℝ)-r)^7 + (81672843558603292159168512/498311414318121121:ℝ)*(r-(479/800:ℝ))^2*((2/3:ℝ)-r)^6 + (235981919035699122733056000/498311414318121121:ℝ)*(r-(479/800:ℝ))^3*((2/3:ℝ)-r)^5 + (414325433731694159993241600/498311414318121121:ℝ)*(r-(479/800:ℝ))^4*((2/3:ℝ)-r)^4 + (453499398278084265246720000/498311414318121121:ℝ)*(r-(479/800:ℝ))^5*((2/3:ℝ)-r)^3 + (303087682730152112947200000/498311414318121121:ℝ)*(r-(479/800:ℝ))^6*((2/3:ℝ)-r)^2 + (113422069316840325120000000/498311414318121121:ℝ)*(r-(479/800:ℝ))^7*((2/3:ℝ)-r)^1 + (18245141539690905600000000/498311414318121121:ℝ)*(r-(479/800:ℝ))^8*((2/3:ℝ)-r)^0 := by unfold quartic; ring
  have hp : 0≤r-(8/3:ℝ)*quartic r*(1-quartic r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma quartic_from_cap {r P:ℝ} (hr:r∈Icc (79/200:ℝ) (2/3:ℝ)) (hP:P≤1/2)
    (hcap:r≤(8/3:ℝ)*P*(1-P)) : quartic r≤P := by
  have hr0 : 0≤r := by linarith only [hr.1]
  have h2 : r^2≤(2/3:ℝ)^2 := (sq_le_sq₀ hr0 (by norm_num)).mpr hr.2
  have h4 : r^4≤(2/3:ℝ)^4 := pow_le_pow_left₀ hr0 hr.2 4
  apply cap_envelope hP (by unfold quartic; nlinarith only [h2,h4]) hcap

  by_cases h0 : r≤(637/1200:ℝ)
  · exact quartic_cap_poly_0 ⟨by linarith only [hr.1],h0⟩
  by_cases h1 : r≤(479/800:ℝ)
  · exact quartic_cap_poly_1 ⟨by linarith only [h0],h1⟩
  exact quartic_cap_poly_2 ⟨by linarith only [h1],hr.2⟩

lemma large_cap_poly_0 {r:ℝ} (hr:r∈Icc (21/40:ℝ) (2/3:ℝ)) :
    (8/3:ℝ)*large r*(1-large r)≤r := by
  have hl : 0≤r-(21/40:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(2/3:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*large r*(1-large r)-(1/10000000:ℝ) =
    (22643631/20880250:ℝ)*(r-(21/40:ℝ))^0*((2/3:ℝ)-r)^4 + (631811232/10440125:ℝ)*(r-(21/40:ℝ))^1*((2/3:ℝ)-r)^3 + (2057374848/10440125:ℝ)*(r-(21/40:ℝ))^2*((2/3:ℝ)-r)^2 + (2438965632/10440125:ℝ)*(r-(21/40:ℝ))^3*((2/3:ℝ)-r)^1 + (3041528224/31320375:ℝ)*(r-(21/40:ℝ))^4*((2/3:ℝ)-r)^0 := by unfold large; ring
  have hp : 0≤r-(8/3:ℝ)*large r*(1-large r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma large_from_cap {r P:ℝ} (hr:r∈Icc (21/40:ℝ) (2/3:ℝ)) (hP:P≤1/2)
    (hcap:r≤(8/3:ℝ)*P*(1-P)) : large r≤P := by
  have hr0 : 0≤r := by linarith only [hr.1]
  have h2 : r^2≤(2/3:ℝ)^2 := (sq_le_sq₀ hr0 (by norm_num)).mpr hr.2
  have h4 : r^4≤(2/3:ℝ)^4 := pow_le_pow_left₀ hr0 hr.2 4
  apply cap_envelope hP (by unfold large; nlinarith only [h2,h4]) hcap

  exact large_cap_poly_0 ⟨by linarith only [hr.1],hr.2⟩

end GaussianPropeller.FourCertificates

end OAI

-- ---- inlined from the OAI_GaussianPropeller_FourCertificates_small_of_loss solution (the platform cannot check that node's statement) ----
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

lemma density_integrable : Integrable density := by
  change Integrable (fun x : ℝ => Real.exp (-x^2/2))
  simpa only [ show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring]
    using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)

lemma hasDerivAt_density (x : ℝ) : HasDerivAt density (-x*density x) x := by
  unfold density
  convert (((hasDerivAt_pow 2 x).neg.div_const 2).exp) using 1 <;>
  first | rfl | (solve | ring) | (dsimp; ring)

lemma tendsto_density : Tendsto density atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  convert (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num : (-(1/2:ℝ)) < 0) using 1
  ext x
  ring

lemma tail_zero : gaussianConst*tail 0 = 1/2 := by
  have h : tail 0 = Real.sqrt (2*Real.pi)/2 := by
    simpa only [tail, density, show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring,
      show Real.pi/(1/2:ℝ) = 2*Real.pi by ring] using integral_gaussian_Ioi (1/2)
  rw [h, gaussianConst]
  field_simp

lemma tail_sub {a : ℝ} (ha : 0 ≤ a) : tail a = tail 0 - ∫ x in (0:ℝ)..a, density x := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi density_integrable.integrableOn ha
  change tail 0-tail a = _ at h
  linarith

lemma gaussianConst_bounds : (39/100:ℝ) ≤ gaussianConst ∧ gaussianConst ≤ 398943/1000000 := by
  have hp := Real.pi_pos
  have hs := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have hspos : 0 < Real.sqrt (2*Real.pi) := by positivity
  constructor
  · rw [gaussianConst, inv_eq_one_div, le_div_iff₀ hspos]
    have hh := Real.pi_lt_d2
    nlinarith
  · rw [gaussianConst, inv_eq_one_div, div_le_iff₀ hspos]
    have hh := Real.pi_gt_d6
    nlinarith

section GeneralCell
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GeneralCell
end GaussianPropeller.OneCell

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Mills ----
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

namespace GaussianPropeller.Mills
open OneCell

lemma tail_pos (x : ℝ) : 0 < tail x := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun x => (Real.exp_pos _).le)) density_integrable.integrableOn).mpr
  simp [Function.support, Real.exp_ne_zero]

lemma hasDerivAt_tail (x : ℝ) : HasDerivAt tail (-density x) x := by
  have heq : tail = fun a => tail 0 - ∫ t in (0:ℝ)..a, density t := by
    funext a
    have hi := intervalIntegral.integral_Ioi_sub_Ioi'
      (a := 0) (b := a) density_integrable.integrableOn density_integrable.integrableOn
    change tail 0-tail a = _ at hi
    linarith only [hi]
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right
    (density_integrable.intervalIntegrable)
    (by exact (show StronglyMeasurable density by unfold density; fun_prop).stronglyMeasurableAtFilter) (hasDerivAt_density x).continuousAt).const_sub _

lemma hasDerivAt_barrier (x : ℝ) : HasDerivAt barrier (barrier' x) x := by
  unfold barrier barrier'
  convert (((hasDerivAt_id x).const_mul 3).add
    (((hasDerivAt_pow 2 x).add_const 8).sqrt (by positivity))).div_const 4 using 1 <;>
    first | rfl | (dsimp; ring)

lemma barrier_pos {x : ℝ} (hx : 0 ≤ x) : 0 < barrier x := by
  unfold barrier
  have : 0 < Real.sqrt (x^2+8) := Real.sqrt_pos.mpr (by positivity)
  positivity

lemma barrier_ge_half {x : ℝ} (hx : 0 ≤ x) : 1/2 ≤ barrier x := by
  have hs := Real.sq_sqrt (show 0 ≤ x^2+8 by positivity)
  have hn := Real.sqrt_nonneg (x^2+8)
  unfold barrier
  nlinarith only [hs,hn,hx,sq_nonneg x]

lemma barrier_differential {x : ℝ} (hx : 0 ≤ x) :
    barrier x ^ 2 - x*barrier x - barrier' x ≤ 0 := by
  let s := Real.sqrt (x^2+8)
  have hs : s^2=x^2+8 := Real.sq_sqrt (by positivity)
  have hp : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hid : (x^2+2)^2*s^2-(x^3+6*x)^2=32 := by rw [hs]; ring
  have hh : x^3+6*x ≤ (x^2+2)*s := by
    have hnon : 0 ≤ x^3+6*x := by positivity
    have hnon' : 0 ≤ (x^2+2)*s := by positivity
    apply (sq_le_sq₀ hnon hnon').mp
    nlinarith only [hid]
  have heq : barrier x^2-x*barrier x-barrier' x =
      (x^3+6*x-(x^2+2)*s)/(8*s) := by
    dsimp [barrier,barrier']
    change ((3*x+s)/4)^2-x*((3*x+s)/4)-(3+x/s)/4 = _
    field_simp [hp.ne']
    have hsm := congrArg (fun t : ℝ => x*t) hs
    have hss := congrArg (fun t : ℝ => s*t) hs
    nlinarith only [hs,hsm,hss]
  rw [heq]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hh) (by positivity)

lemma tail_le_barrier {x : ℝ} (hx : 0 ≤ x) : tail x ≤ density x / barrier x := by
  let f : ℝ → ℝ := fun y => density y/barrier y-tail y
  let f' : ℝ → ℝ := fun y => density y*(barrier y^2-y*barrier y-barrier' y)/barrier y^2
  have hd (y : ℝ) (hy : 0 ≤ y) : HasDerivAt f (f' y) y := by
    convert ((hasDerivAt_density y).div (hasDerivAt_barrier y) (barrier_pos hy).ne').sub
      (hasDerivAt_tail y) using 1 <;>
    first | rfl | (dsimp [f']; field_simp [(barrier_pos hy).ne']; ring)
  have hm : AntitoneOn f (Ici 0) := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (barrier_differential (interior_subset hy))) (sq_nonneg _))
  have ht : Tendsto (fun y => density y/barrier y) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (by simpa using tendsto_density.const_mul 2)
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
      exact div_nonneg (Real.exp_pos _).le (barrier_pos hy).le
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
      apply (div_le_iff₀ (barrier_pos hy)).mpr
      have hh := mul_le_mul_of_nonneg_left (barrier_ge_half hy) (Real.exp_pos (-y^2/2)).le
      change density y * (1/2) ≤ density y*barrier y at hh
      nlinarith only [hh]
  have ht' : Tendsto f atTop (𝓝 0) := by
    simpa only [sub_zero, f, tail, id_eq] using ht.sub (tendsto_integral_Ioi_zero (f := density) tendsto_id)
  have hnon : 0 ≤ f x := le_of_tendsto ht' (by
    filter_upwards [eventually_ge_atTop x] with y hy
    exact hm hx (hx.trans hy) hy)
  dsimp [f] at hnon
  linarith only [hnon]

lemma lambda_ge_barrier {x : ℝ} (hx : 0 ≤ x) : barrier x ≤ lambda x := by
  rw [lambda, le_div_iff₀ (tail_pos x)]
  have hh := (le_div_iff₀ (barrier_pos hx)).mp (tail_le_barrier hx)
  linarith only [hh]

lemma lambda_pos (x : ℝ) : 0 < lambda x := div_pos (Real.exp_pos _) (tail_pos x)

lemma G_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ G x := by
  apply mul_nonneg (lambda_pos x).le
  have hb := lambda_ge_barrier hx
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ x^2+8 by positivity)
  have hp := Real.sqrt_nonneg (x^2+8)
  have hh : x ≤ Real.sqrt (x^2+8) := by nlinarith only [hs,hp,hx]
  dsimp [barrier] at hb
  linarith only [hb,hh]

end GaussianPropeller.Mills

end OAI

-- ---- from OAI.Probability.GaussianPropeller.ProbabilityBounds ----
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

namespace GaussianPropeller.ProbabilityBounds
open OneCell Mills Taylor
lemma gaussianConst_tight : (398942/1000000:ℝ) ≤ gaussianConst ∧ gaussianConst ≤ 398943/1000000 := by
  refine ⟨?_, gaussianConst_bounds.2⟩
  have hs := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have hspos : 0 < Real.sqrt (2*Real.pi) := by positivity
  rw [gaussianConst, inv_eq_one_div, le_div_iff₀ hspos]
  have hh := Real.pi_lt_d6
  nlinarith

lemma p_pos (x : ℝ) : 0 < p x :=
  mul_pos (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1) (tail_pos x)

lemma p_taylor_lower {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hJ : 0 ≤ J (2*n) x) :
    1/2-(398943/1000000:ℝ)*J (2*n) x ≤ p x := by
  have hh := (integral_exp_bounds n hx).2
  change (∫ t in (0:ℝ)..x, density t) ≤ J (2*n) x at hh
  have hmul := mul_le_mul_of_nonneg_left hh
    (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1).le
  have hmul' := mul_le_mul_of_nonneg_right gaussianConst_tight.2 hJ
  unfold p
  rw [tail_sub hx, mul_sub, tail_zero]
  linarith only [hmul,hmul']

lemma p_taylor_upper {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hJ : 0 ≤ J (2*n+1) x) :
    p x ≤ 1/2-(398942/1000000:ℝ)*J (2*n+1) x := by
  have hh := (integral_exp_bounds n hx).1
  change J (2*n+1) x ≤ ∫ t in (0:ℝ)..x, density t at hh
  have hmul := mul_le_mul_of_nonneg_left hh
    (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1).le
  have hmul' := mul_le_mul_of_nonneg_right gaussianConst_tight.1 hJ
  unfold p
  rw [tail_sub hx, mul_sub, tail_zero]
  linarith only [hmul,hmul']

lemma G_upper_of_lambda {x L U : ℝ} (hx : 0 ≤ x) (h : lambda x ≤ L)
    (hLU : L*(L-x) ≤ U) : G x ≤ U := by
  have hl : 0 ≤ lambda x-x := (mul_nonneg_iff_of_pos_left (lambda_pos x)).mp (G_nonneg hx)
  have hh := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ L+lambda x-x by linarith [lambda_pos x])
  unfold G
  nlinarith only [hh,hLU]

end GaussianPropeller.ProbabilityBounds

end OAI

-- ---- from OAI.Probability.GaussianPropeller.QuarticCertificates ----
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

namespace GaussianPropeller.FourCertificates
open OneCell ProbabilityBounds Mills Taylor

lemma loss_bound {x pu gu : ℝ} (hx:0≤x) (hp:p x≤pu) (hg:G x≤gu) : loss x≤pu^2*gu := by
  have hp0 := p_pos x
  have hg0 := G_nonneg hx
  have hsq : (p x)^2≤pu^2 := sq_le_sq₀ hp0.le (hp0.le.trans hp) |>.mpr hp
  exact (mul_le_mul_of_nonneg_right hsq hg0).trans (mul_le_mul_of_nonneg_left hg (sq_nonneg pu))

lemma small_mono : MonotoneOn small (Ici 0) := by
  intro a ha b hb hab
  have h2:=pow_le_pow_left₀ ha hab 2
  unfold small; linarith only [h2,hab]
end GaussianPropeller.FourCertificates

end OAI

-- ---- from OAI.Probability.GaussianPropeller.SmallCertificates ----
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
namespace GaussianPropeller.FourCertificates
open OneCell ProbabilityBounds Mills Taylor

lemma small_0 {r x:ℝ} (hr:r∈Icc (39/250:ℝ) (157/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (157/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (9139/6250:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (9139/6250:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (157/1000:ℝ) ≤ p (9139/6250:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (9139/6250:ℝ)≤(449/6250:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (9139/6250:ℝ)≤(953337/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (9139/6250:ℝ)≤(847391/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(39/250:ℝ)) (q:=(9139/6250:ℝ)) (v:=(983643/1000000:ℝ))
    (u:=(449/6250:ℝ)^2*(847391/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_1 {r x:ℝ} (hr:r∈Icc (157/1000:ℝ) (79/500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (79/500:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (72937/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (72937/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (79/500:ℝ) ≤ p (72937/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (72937/50000:ℝ)≤(72321/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (72937/50000:ℝ)≤(1903709/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (72937/50000:ℝ)≤(211773/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(157/1000:ℝ)) (q:=(72937/50000:ℝ)) (v:=(983431/1000000:ℝ))
    (u:=(72321/1000000:ℝ)^2*(211773/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_2 {r x:ℝ} (hr:r∈Icc (79/500:ℝ) (159/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (159/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (5821/4000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (5821/4000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (159/1000:ℝ) ≤ p (5821/4000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (5821/4000:ℝ)≤(72803/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (5821/4000:ℝ)≤(950377/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (5821/4000:ℝ)≤(423397/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(79/500:ℝ)) (q:=(5821/4000:ℝ)) (v:=(983217/1000000:ℝ))
    (u:=(72803/1000000:ℝ)^2*(423397/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_3 {r x:ℝ} (hr:r∈Icc (159/1000:ℝ) (4/25:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (4/25:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (72589/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (72589/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (4/25:ℝ) ≤ p (72589/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (72589/50000:ℝ)≤(18321/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (72589/50000:ℝ)≤(1897817/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (72589/50000:ℝ)≤(846497/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(159/1000:ℝ)) (q:=(72589/50000:ℝ)) (v:=(491501/500000:ℝ))
    (u:=(18321/250000:ℝ)^2*(846497/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_4 {r x:ℝ} (hr:r∈Icc (4/25:ℝ) (161/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (161/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (4526/3125:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (4526/3125:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (161/1000:ℝ) ≤ p (4526/3125:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (4526/3125:ℝ)≤(36883/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (4526/3125:ℝ)≤(1894889/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (4526/3125:ℝ)≤(846199/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(4/25:ℝ)) (q:=(4526/3125:ℝ)) (v:=(491393/500000:ℝ))
    (u:=(36883/500000:ℝ)^2*(846199/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_5 {r x:ℝ} (hr:r∈Icc (161/1000:ℝ) (81/500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (81/500:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (144487/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (144487/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (81/500:ℝ) ≤ p (144487/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (144487/100000:ℝ)≤(297/4000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (144487/100000:ℝ)≤(189197/100000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (144487/100000:ℝ)≤(8459/10000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(161/1000:ℝ)) (q:=(144487/100000:ℝ)) (v:=(122821/125000:ℝ))
    (u:=(297/4000:ℝ)^2*(8459/10000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_6 {r x:ℝ} (hr:r∈Icc (81/500:ℝ) (163/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (163/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (28829/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (28829/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (163/1000:ℝ) ≤ p (28829/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (28829/20000:ℝ)≤(74731/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (28829/20000:ℝ)≤(944539/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (28829/20000:ℝ)≤(169121/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(81/500:ℝ)) (q:=(28829/20000:ℝ)) (v:=(982349/1000000:ℝ))
    (u:=(74731/1000000:ℝ)^2*(169121/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_7 {r x:ℝ} (hr:r∈Icc (163/1000:ℝ) (41/250:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (41/250:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (143803/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (143803/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (41/250:ℝ) ≤ p (143803/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (143803/100000:ℝ)≤(15043/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (143803/100000:ℝ)≤(1886187/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (143803/100000:ℝ)≤(211327/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(163/1000:ℝ)) (q:=(143803/100000:ℝ)) (v:=(61383/62500:ℝ))
    (u:=(15043/200000:ℝ)^2*(211327/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_8 {r x:ℝ} (hr:r∈Icc (41/250:ℝ) (33/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (33/200:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (143463/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (143463/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (33/200:ℝ) ≤ p (143463/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (143463/100000:ℝ)≤(75699/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (143463/100000:ℝ)≤(941657/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (143463/100000:ℝ)≤(845013/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(41/250:ℝ)) (q:=(143463/100000:ℝ)) (v:=(490953/500000:ℝ))
    (u:=(75699/1000000:ℝ)^2*(845013/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_9 {r x:ℝ} (hr:r∈Icc (33/200:ℝ) (83/500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (83/500:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (229/160:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (229/160:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (83/500:ℝ) ≤ p (229/160:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (229/160:ℝ)≤(38091/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (229/160:ℝ)≤(1880459/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (229/160:ℝ)≤(10559/12500:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(33/200:ℝ)) (q:=(229/160:ℝ)) (v:=(981683/1000000:ℝ))
    (u:=(38091/500000:ℝ)^2*(10559/12500:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_10 {r x:ℝ} (hr:r∈Icc (83/500:ℝ) (167/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (167/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (35697/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (35697/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (167/1000:ℝ) ≤ p (35697/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (35697/25000:ℝ)≤(38333/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (35697/25000:ℝ)≤(1877613/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (35697/25000:ℝ)≤(33777/40000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(83/500:ℝ)) (q:=(35697/25000:ℝ)) (v:=(490729/500000:ℝ))
    (u:=(38333/500000:ℝ)^2*(33777/40000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_11 {r x:ℝ} (hr:r∈Icc (167/1000:ℝ) (21/125:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (21/125:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (35613/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (35613/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (21/125:ℝ) ≤ p (35613/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (35613/25000:ℝ)≤(1543/20000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (35613/25000:ℝ)≤(234347/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (35613/25000:ℝ)≤(84413/100000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(167/1000:ℝ)) (q:=(35613/25000:ℝ)) (v:=(61327/62500:ℝ))
    (u:=(1543/20000:ℝ)^2*(84413/100000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_12 {r x:ℝ} (hr:r∈Icc (21/125:ℝ) (169/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (169/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (71059/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (71059/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (169/1000:ℝ) ≤ p (71059/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (71059/50000:ℝ)≤(15527/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (71059/50000:ℝ)≤(935979/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (71059/50000:ℝ)≤(421919/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(21/125:ℝ)) (q:=(71059/50000:ℝ)) (v:=(245251/250000:ℝ))
    (u:=(15527/200000:ℝ)^2*(421919/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_13 {r x:ℝ} (hr:r∈Icc (169/1000:ℝ) (17/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (17/100:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (28357/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (28357/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (17/100:ℝ) ≤ p (28357/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (28357/20000:ℝ)≤(1953/25000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (28357/20000:ℝ)≤(1869149/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (28357/20000:ℝ)≤(421773/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(169/1000:ℝ)) (q:=(28357/20000:ℝ)) (v:=(39231/40000:ℝ))
    (u:=(1953/25000:ℝ)^2*(421773/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_14 {r x:ℝ} (hr:r∈Icc (17/100:ℝ) (171/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (171/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (70727/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (70727/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (171/1000:ℝ) ≤ p (70727/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (70727/50000:ℝ)≤(19651/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (70727/50000:ℝ)≤(933179/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (70727/50000:ℝ)≤(168651/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(17/100:ℝ)) (q:=(70727/50000:ℝ)) (v:=(196109/200000:ℝ))
    (u:=(19651/250000:ℝ)^2*(168651/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_15 {r x:ℝ} (hr:r∈Icc (171/1000:ℝ) (43/250:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (43/250:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (141123/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (141123/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (43/250:ℝ) ≤ p (141123/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (141123/100000:ℝ)≤(79091/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (141123/100000:ℝ)≤(1863567/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (141123/100000:ℝ)≤(842961/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(171/1000:ℝ)) (q:=(141123/100000:ℝ)) (v:=(980313/1000000:ℝ))
    (u:=(79091/1000000:ℝ)^2*(842961/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_16 {r x:ℝ} (hr:r∈Icc (43/250:ℝ) (173/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (173/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (28159/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (28159/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (173/1000:ℝ) ≤ p (28159/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (28159/20000:ℝ)≤(3183/40000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (28159/20000:ℝ)≤(1860803/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (28159/20000:ℝ)≤(842671/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(43/250:ℝ)) (q:=(28159/20000:ℝ)) (v:=(980079/1000000:ℝ))
    (u:=(3183/40000:ℝ)^2*(842671/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_17 {r x:ℝ} (hr:r∈Icc (173/1000:ℝ) (87/500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (87/500:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (140467/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (140467/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (87/500:ℝ) ≤ p (140467/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (140467/100000:ℝ)≤(40031/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (140467/100000:ℝ)≤(46451/25000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (140467/100000:ℝ)≤(42119/50000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(173/1000:ℝ)) (q:=(140467/100000:ℝ)) (v:=(195969/200000:ℝ))
    (u:=(40031/500000:ℝ)^2*(42119/50000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_18 {r x:ℝ} (hr:r∈Icc (87/500:ℝ) (7/40:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (7/40:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (140141/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (140141/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (7/40:ℝ) ≤ p (140141/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (140141/100000:ℝ)≤(20137/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (140141/100000:ℝ)≤(371059/200000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (140141/100000:ℝ)≤(842091/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(87/500:ℝ)) (q:=(140141/100000:ℝ)) (v:=(979609/1000000:ℝ))
    (u:=(20137/250000:ℝ)^2*(842091/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_19 {r x:ℝ} (hr:r∈Icc (7/40:ℝ) (22/125:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (22/125:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (17477/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (17477/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (22/125:ℝ) ≤ p (17477/12500:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (17477/12500:ℝ)≤(16207/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (17477/12500:ℝ)≤(1852559/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (17477/12500:ℝ)≤(841801/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(7/40:ℝ)) (q:=(17477/12500:ℝ)) (v:=(979371/1000000:ℝ))
    (u:=(16207/200000:ℝ)^2*(841801/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_20 {r x:ℝ} (hr:r∈Icc (22/125:ℝ) (177/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (177/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (34873/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (34873/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (177/1000:ℝ) ≤ p (34873/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (34873/25000:ℝ)≤(40761/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (34873/25000:ℝ)≤(231229/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (34873/25000:ℝ)≤(841511/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(22/125:ℝ)) (q:=(34873/25000:ℝ)) (v:=(244783/250000:ℝ))
    (u:=(40761/500000:ℝ)^2*(841511/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_21 {r x:ℝ} (hr:r∈Icc (177/1000:ℝ) (89/500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (89/500:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (13917/10000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (13917/10000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (89/500:ℝ) ≤ p (13917/10000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (13917/10000:ℝ)≤(82009/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (13917/10000:ℝ)≤(1847123/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (13917/10000:ℝ)≤(841223/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(177/1000:ℝ)) (q:=(13917/10000:ℝ)) (v:=(244723/250000:ℝ))
    (u:=(82009/1000000:ℝ)^2*(841223/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_22 {r x:ℝ} (hr:r∈Icc (89/500:ℝ) (179/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (179/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (138849/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (138849/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (179/1000:ℝ) ≤ p (138849/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (138849/100000:ℝ)≤(1289/15625:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (138849/100000:ℝ)≤(230553/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (138849/100000:ℝ)≤(105117/125000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(89/500:ℝ)) (q:=(138849/100000:ℝ)) (v:=(19573/20000:ℝ))
    (u:=(1289/15625:ℝ)^2*(105117/125000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_23 {r x:ℝ} (hr:r∈Icc (179/1000:ℝ) (9/50:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (9/50:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (138529/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (138529/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (9/50:ℝ) ≤ p (138529/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (138529/100000:ℝ)≤(10373/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (138529/100000:ℝ)≤(920867/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (138529/100000:ℝ)≤(840649/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(179/1000:ℝ)) (q:=(138529/100000:ℝ)) (v:=(978407/1000000:ℝ))
    (u:=(10373/125000:ℝ)^2*(840649/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_of_loss {r x:ℝ} (hr:r∈Icc (39/250:ℝ) (9/50:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_cases h0 : r≤(157/1000:ℝ)
  · exact small_0 ⟨by linarith only [hr.1],h0⟩ hx hl
  by_cases h1 : r≤(79/500:ℝ)
  · exact small_1 ⟨by linarith only [h0],h1⟩ hx hl
  by_cases h2 : r≤(159/1000:ℝ)
  · exact small_2 ⟨by linarith only [h1],h2⟩ hx hl
  by_cases h3 : r≤(4/25:ℝ)
  · exact small_3 ⟨by linarith only [h2],h3⟩ hx hl
  by_cases h4 : r≤(161/1000:ℝ)
  · exact small_4 ⟨by linarith only [h3],h4⟩ hx hl
  by_cases h5 : r≤(81/500:ℝ)
  · exact small_5 ⟨by linarith only [h4],h5⟩ hx hl
  by_cases h6 : r≤(163/1000:ℝ)
  · exact small_6 ⟨by linarith only [h5],h6⟩ hx hl
  by_cases h7 : r≤(41/250:ℝ)
  · exact small_7 ⟨by linarith only [h6],h7⟩ hx hl
  by_cases h8 : r≤(33/200:ℝ)
  · exact small_8 ⟨by linarith only [h7],h8⟩ hx hl
  by_cases h9 : r≤(83/500:ℝ)
  · exact small_9 ⟨by linarith only [h8],h9⟩ hx hl
  by_cases h10 : r≤(167/1000:ℝ)
  · exact small_10 ⟨by linarith only [h9],h10⟩ hx hl
  by_cases h11 : r≤(21/125:ℝ)
  · exact small_11 ⟨by linarith only [h10],h11⟩ hx hl
  by_cases h12 : r≤(169/1000:ℝ)
  · exact small_12 ⟨by linarith only [h11],h12⟩ hx hl
  by_cases h13 : r≤(17/100:ℝ)
  · exact small_13 ⟨by linarith only [h12],h13⟩ hx hl
  by_cases h14 : r≤(171/1000:ℝ)
  · exact small_14 ⟨by linarith only [h13],h14⟩ hx hl
  by_cases h15 : r≤(43/250:ℝ)
  · exact small_15 ⟨by linarith only [h14],h15⟩ hx hl
  by_cases h16 : r≤(173/1000:ℝ)
  · exact small_16 ⟨by linarith only [h15],h16⟩ hx hl
  by_cases h17 : r≤(87/500:ℝ)
  · exact small_17 ⟨by linarith only [h16],h17⟩ hx hl
  by_cases h18 : r≤(7/40:ℝ)
  · exact small_18 ⟨by linarith only [h17],h18⟩ hx hl
  by_cases h19 : r≤(22/125:ℝ)
  · exact small_19 ⟨by linarith only [h18],h19⟩ hx hl
  by_cases h20 : r≤(177/1000:ℝ)
  · exact small_20 ⟨by linarith only [h19],h20⟩ hx hl
  by_cases h21 : r≤(89/500:ℝ)
  · exact small_21 ⟨by linarith only [h20],h21⟩ hx hl
  by_cases h22 : r≤(179/1000:ℝ)
  · exact small_22 ⟨by linarith only [h21],h22⟩ hx hl
  exact small_23 ⟨by linarith only [h22],hr.2⟩ hx hl

end GaussianPropeller.FourCertificates

end OAI


-- ---- inlined from the OAI_GaussianPropeller_FourCertificates_large_of_loss solution (the platform cannot check that node's statement) ----
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







section GeneralCell
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GeneralCell
end GaussianPropeller.OneCell

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Mills ----
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

namespace GaussianPropeller.Mills
open OneCell











end GaussianPropeller.Mills

end OAI

-- ---- from OAI.Probability.GaussianPropeller.ProbabilityBounds ----
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

namespace GaussianPropeller.ProbabilityBounds
open OneCell Mills Taylor





end GaussianPropeller.ProbabilityBounds

end OAI

-- ---- from OAI.Probability.GaussianPropeller.QuarticCertificates ----
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

namespace GaussianPropeller.FourCertificates
open OneCell ProbabilityBounds Mills Taylor


lemma large_mono : MonotoneOn large (Ici 0) := by
  intro a ha b hb hab
  have h2:=pow_le_pow_left₀ ha hab 2
  unfold large; linarith only [h2]

end GaussianPropeller.FourCertificates

end OAI

-- ---- from OAI.Probability.GaussianPropeller.LossCertificates ----
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
namespace GaussianPropeller.FourCertificates
open OneCell ProbabilityBounds Mills Taylor

lemma large_25 {r x:ℝ} (hr:r∈Icc (37/80:ℝ) (93/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (93/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (73703/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (73703/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (93/200:ℝ) ≤ p (73703/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (73703/100000:ℝ)≤(46111/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (73703/100000:ℝ)≤(263773/200000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (73703/100000:ℝ)≤(383681/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(37/80:ℝ)) (q:=(73703/100000:ℝ)) (v:=(422727/500000:ℝ))
    (u:=(46111/200000:ℝ)^2*(383681/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_26 {r x:ℝ} (hr:r∈Icc (93/200:ℝ) (187/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (187/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (36603/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (36603/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (187/400:ℝ) ≤ p (36603/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (36603/50000:ℝ)≤(58017/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (36603/50000:ℝ)≤(657527/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (36603/50000:ℝ)≤(766669/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(93/200:ℝ)) (q:=(36603/50000:ℝ)) (v:=(105453/125000:ℝ))
    (u:=(58017/250000:ℝ)^2*(766669/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_27 {r x:ℝ} (hr:r∈Icc (187/400:ℝ) (47/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (47/100:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (18177/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (18177/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (47/100:ℝ) ≤ p (18177/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (18177/25000:ℝ)≤(233591/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (18177/25000:ℝ)≤(655619/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (18177/25000:ℝ)≤(765971/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(187/400:ℝ)) (q:=(18177/25000:ℝ)) (v:=(841779/1000000:ℝ))
    (u:=(233591/1000000:ℝ)^2*(765971/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_28 {r x:ℝ} (hr:r∈Icc (47/100:ℝ) (189/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (189/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (4513/6250:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (4513/6250:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (189/400:ℝ) ≤ p (4513/6250:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (4513/6250:ℝ)≤(1881/8000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (4513/6250:ℝ)≤(130741/100000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (4513/6250:ℝ)≤(765267/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(47/100:ℝ)) (q:=(4513/6250:ℝ)) (v:=(839921/1000000:ℝ))
    (u:=(1881/8000:ℝ)^2*(765267/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_29 {r x:ℝ} (hr:r∈Icc (189/400:ℝ) (19/40:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (19/40:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (17927/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (17927/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (19/40:ℝ) ≤ p (17927/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (17927/25000:ℝ)≤(47333/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (17927/25000:ℝ)≤(651793/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (17927/25000:ℝ)≤(382281/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(189/400:ℝ)) (q:=(17927/25000:ℝ)) (v:=(838049/1000000:ℝ))
    (u:=(47333/200000:ℝ)^2*(382281/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_30 {r x:ℝ} (hr:r∈Icc (19/40:ℝ) (191/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (191/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (8901/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (8901/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (191/400:ℝ) ≤ p (8901/12500:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (8901/12500:ℝ)≤(23821/100000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (8901/12500:ℝ)≤(649883/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (8901/12500:ℝ)≤(152771/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(19/40:ℝ)) (q:=(8901/12500:ℝ)) (v:=(418081/500000:ℝ))
    (u:=(23821/100000:ℝ)^2*(152771/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_31 {r x:ℝ} (hr:r∈Icc (191/400:ℝ) (12/25:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (12/25:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (35353/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (35353/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (12/25:ℝ) ≤ p (35353/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (35353/50000:ℝ)≤(239767/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (35353/50000:ℝ)≤(1295933/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (35353/50000:ℝ)≤(38157/50000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(191/400:ℝ)) (q:=(35353/50000:ℝ)) (v:=(417131/500000:ℝ))
    (u:=(239767/1000000:ℝ)^2*(38157/50000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_32 {r x:ℝ} (hr:r∈Icc (12/25:ℝ) (193/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (193/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (70203/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (70203/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (193/400:ℝ) ≤ p (70203/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (70203/100000:ℝ)≤(241333/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (70203/100000:ℝ)≤(1292097/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (70203/100000:ℝ)≤(95303/125000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(12/25:ℝ)) (q:=(70203/100000:ℝ)) (v:=(832347/1000000:ℝ))
    (u:=(241333/1000000:ℝ)^2*(95303/125000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_33 {r x:ℝ} (hr:r∈Icc (193/400:ℝ) (97/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (97/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (697/1000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (697/1000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (97/200:ℝ) ≤ p (697/1000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (697/1000:ℝ)≤(30363/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (697/1000:ℝ)≤(161033/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (697/1000:ℝ)≤(152341/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(193/400:ℝ)) (q:=(697/1000:ℝ)) (v:=(830417/1000000:ℝ))
    (u:=(30363/125000:ℝ)^2*(152341/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_34 {r x:ℝ} (hr:r∈Icc (97/200:ℝ) (39/80:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (39/80:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (17299/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (17299/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (39/80:ℝ) ≤ p (17299/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (17299/25000:ℝ)≤(61121/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (17299/25000:ℝ)≤(321107/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (17299/25000:ℝ)≤(760983/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(97/200:ℝ)) (q:=(17299/25000:ℝ)) (v:=(828473/1000000:ℝ))
    (u:=(61121/250000:ℝ)^2*(760983/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_35 {r x:ℝ} (hr:r∈Icc (39/80:ℝ) (49/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (49/100:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (68691/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (68691/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (49/100:ℝ) ≤ p (68691/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (68691/100000:ℝ)≤(30759/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (68691/100000:ℝ)≤(1280587/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (68691/100000:ℝ)≤(11879/15625:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(39/80:ℝ)) (q:=(68691/100000:ℝ)) (v:=(413257/500000:ℝ))
    (u:=(30759/125000:ℝ)^2*(11879/15625:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_36 {r x:ℝ} (hr:r∈Icc (49/100:ℝ) (197/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (197/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (13637/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (13637/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (197/400:ℝ) ≤ p (13637/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (13637/20000:ℝ)≤(247669/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (13637/20000:ℝ)≤(638371/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (13637/20000:ℝ)≤(189881/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(49/100:ℝ)) (q:=(13637/20000:ℝ)) (v:=(824541/1000000:ℝ))
    (u:=(247669/1000000:ℝ)^2*(189881/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_37 {r x:ℝ} (hr:r∈Icc (197/400:ℝ) (99/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (99/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (67679/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (67679/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (99/200:ℝ) ≤ p (67679/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (67679/100000:ℝ)≤(31159/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (67679/100000:ℝ)≤(636451/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (67679/100000:ℝ)≤(758793/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(197/400:ℝ)) (q:=(67679/100000:ℝ)) (v:=(102819/125000:ℝ))
    (u:=(31159/125000:ℝ)^2*(758793/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_38 {r x:ℝ} (hr:r∈Icc (99/200:ℝ) (199/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (199/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (67171/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (67171/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (199/400:ℝ) ≤ p (67171/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (67171/100000:ℝ)≤(250887/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (67171/100000:ℝ)≤(1269049/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (67171/100000:ℝ)≤(758053/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(99/200:ℝ)) (q:=(67171/100000:ℝ)) (v:=(820549/1000000:ℝ))
    (u:=(250887/1000000:ℝ)^2*(758053/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_39 {r x:ℝ} (hr:r∈Icc (199/400:ℝ) (1/2:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (1/2:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (66663/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (66663/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (1/2:ℝ) ≤ p (66663/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (66663/100000:ℝ)≤(252507/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (66663/100000:ℝ)≤(1265201/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (66663/100000:ℝ)≤(757313/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(199/400:ℝ)) (q:=(66663/100000:ℝ)) (v:=(818531/1000000:ℝ))
    (u:=(252507/1000000:ℝ)^2*(757313/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_40 {r x:ℝ} (hr:r∈Icc (1/2:ℝ) (201/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (201/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (33077/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (33077/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (201/400:ℝ) ≤ p (33077/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (33077/50000:ℝ)≤(31767/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (33077/50000:ℝ)≤(315337/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (33077/50000:ℝ)≤(756567/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(1/2:ℝ)) (q:=(33077/50000:ℝ)) (v:=(816497/1000000:ℝ))
    (u:=(31767/125000:ℝ)^2*(756567/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_41 {r x:ℝ} (hr:r∈Icc (201/400:ℝ) (101/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (101/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (16411/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (16411/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (101/200:ℝ) ≤ p (16411/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (16411/25000:ℝ)≤(255773/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (16411/25000:ℝ)≤(314373/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (16411/25000:ℝ)≤(755819/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(201/400:ℝ)) (q:=(16411/25000:ℝ)) (v:=(50903/62500:ℝ))
    (u:=(255773/1000000:ℝ)^2*(755819/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_42 {r x:ℝ} (hr:r∈Icc (101/200:ℝ) (203/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (203/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (65133/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (65133/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (203/400:ℝ) ≤ p (65133/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (65133/100000:ℝ)≤(257419/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (65133/100000:ℝ)≤(19588/15625:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (65133/100000:ℝ)≤(377533/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(101/200:ℝ)) (q:=(65133/100000:ℝ)) (v:=(25387/31250:ℝ))
    (u:=(257419/1000000:ℝ)^2*(377533/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_43 {r x:ℝ} (hr:r∈Icc (203/400:ℝ) (51/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (51/100:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (32311/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (32311/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (51/100:ℝ) ≤ p (32311/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (32311/50000:ℝ)≤(259071/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (32311/50000:ℝ)≤(78111/62500:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (32311/50000:ℝ)≤(75431/100000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(203/400:ℝ)) (q:=(32311/50000:ℝ)) (v:=(12661/15625:ℝ))
    (u:=(259071/1000000:ℝ)^2*(75431/100000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_44 {r x:ℝ} (hr:r∈Icc (51/100:ℝ) (41/80:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (41/80:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (64109/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (64109/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (41/80:ℝ) ≤ p (64109/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (64109/100000:ℝ)≤(52147/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (64109/100000:ℝ)≤(1245909/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (64109/100000:ℝ)≤(15071/20000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(51/100:ℝ)) (q:=(64109/100000:ℝ)) (v:=(50513/62500:ℝ))
    (u:=(52147/200000:ℝ)^2*(15071/20000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_45 {r x:ℝ} (hr:r∈Icc (41/80:ℝ) (103/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (103/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (15899/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (15899/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (103/200:ℝ) ≤ p (15899/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (15899/25000:ℝ)≤(65601/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (15899/25000:ℝ)≤(621023/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (15899/25000:ℝ)≤(752787/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(41/80:ℝ)) (q:=(15899/25000:ℝ)) (v:=(806097/1000000:ℝ))
    (u:=(65601/250000:ℝ)^2*(752787/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_46 {r x:ℝ} (hr:r∈Icc (103/200:ℝ) (207/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (207/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (31541/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (31541/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (207/400:ℝ) ≤ p (31541/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (31541/50000:ℝ)≤(132041/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (31541/50000:ℝ)≤(1238179/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (31541/50000:ℝ)≤(37601/50000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(103/200:ℝ)) (q:=(31541/50000:ℝ)) (v:=(80397/100000:ℝ))
    (u:=(132041/500000:ℝ)^2*(37601/50000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_47 {r x:ℝ} (hr:r∈Icc (207/400:ℝ) (13/25:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (13/25:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (62567/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (62567/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (13/25:ℝ) ≤ p (62567/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (62567/100000:ℝ)≤(33221/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (62567/100000:ℝ)≤(1234309/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (62567/100000:ℝ)≤(751249/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(207/400:ℝ)) (q:=(62567/100000:ℝ)) (v:=(801827/1000000:ℝ))
    (u:=(33221/125000:ℝ)^2*(751249/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_48 {r x:ℝ} (hr:r∈Icc (13/25:ℝ) (209/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (209/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (15513/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (15513/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (209/400:ℝ) ≤ p (15513/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (15513/25000:ℝ)≤(13373/50000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (15513/25000:ℝ)≤(615221/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (15513/25000:ℝ)≤(375237/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(13/25:ℝ)) (q:=(15513/25000:ℝ)) (v:=(799667/1000000:ℝ))
    (u:=(13373/50000:ℝ)^2*(375237/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_49 {r x:ℝ} (hr:r∈Icc (209/400:ℝ) (21/40:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (21/40:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (12307/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (12307/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (21/40:ℝ) ≤ p (12307/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (12307/20000:ℝ)≤(67291/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (12307/20000:ℝ)≤(245313/200000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (12307/20000:ℝ)≤(149939/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(209/400:ℝ)) (q:=(12307/20000:ℝ)) (v:=(797491/1000000:ℝ))
    (u:=(67291/250000:ℝ)^2*(149939/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_of_loss {r x:ℝ} (hr:r∈Icc (2/5:ℝ) (21/40:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_cases h0 : r≤(161/400:ℝ)
  · exact large_0 ⟨by linarith only [hr.1],h0⟩ hx hl
  by_cases h1 : r≤(81/200:ℝ)
  · exact large_1 ⟨by linarith only [h0],h1⟩ hx hl
  by_cases h2 : r≤(163/400:ℝ)
  · exact large_2 ⟨by linarith only [h1],h2⟩ hx hl
  by_cases h3 : r≤(41/100:ℝ)
  · exact large_3 ⟨by linarith only [h2],h3⟩ hx hl
  by_cases h4 : r≤(33/80:ℝ)
  · exact large_4 ⟨by linarith only [h3],h4⟩ hx hl
  by_cases h5 : r≤(83/200:ℝ)
  · exact large_5 ⟨by linarith only [h4],h5⟩ hx hl
  by_cases h6 : r≤(167/400:ℝ)
  · exact large_6 ⟨by linarith only [h5],h6⟩ hx hl
  by_cases h7 : r≤(21/50:ℝ)
  · exact large_7 ⟨by linarith only [h6],h7⟩ hx hl
  by_cases h8 : r≤(169/400:ℝ)
  · exact large_8 ⟨by linarith only [h7],h8⟩ hx hl
  by_cases h9 : r≤(17/40:ℝ)
  · exact large_9 ⟨by linarith only [h8],h9⟩ hx hl
  by_cases h10 : r≤(171/400:ℝ)
  · exact large_10 ⟨by linarith only [h9],h10⟩ hx hl
  by_cases h11 : r≤(43/100:ℝ)
  · exact large_11 ⟨by linarith only [h10],h11⟩ hx hl
  by_cases h12 : r≤(173/400:ℝ)
  · exact large_12 ⟨by linarith only [h11],h12⟩ hx hl
  by_cases h13 : r≤(87/200:ℝ)
  · exact large_13 ⟨by linarith only [h12],h13⟩ hx hl
  by_cases h14 : r≤(7/16:ℝ)
  · exact large_14 ⟨by linarith only [h13],h14⟩ hx hl
  by_cases h15 : r≤(11/25:ℝ)
  · exact large_15 ⟨by linarith only [h14],h15⟩ hx hl
  by_cases h16 : r≤(177/400:ℝ)
  · exact large_16 ⟨by linarith only [h15],h16⟩ hx hl
  by_cases h17 : r≤(89/200:ℝ)
  · exact large_17 ⟨by linarith only [h16],h17⟩ hx hl
  by_cases h18 : r≤(179/400:ℝ)
  · exact large_18 ⟨by linarith only [h17],h18⟩ hx hl
  by_cases h19 : r≤(9/20:ℝ)
  · exact large_19 ⟨by linarith only [h18],h19⟩ hx hl
  by_cases h20 : r≤(181/400:ℝ)
  · exact large_20 ⟨by linarith only [h19],h20⟩ hx hl
  by_cases h21 : r≤(91/200:ℝ)
  · exact large_21 ⟨by linarith only [h20],h21⟩ hx hl
  by_cases h22 : r≤(183/400:ℝ)
  · exact large_22 ⟨by linarith only [h21],h22⟩ hx hl
  by_cases h23 : r≤(23/50:ℝ)
  · exact large_23 ⟨by linarith only [h22],h23⟩ hx hl
  by_cases h24 : r≤(37/80:ℝ)
  · exact large_24 ⟨by linarith only [h23],h24⟩ hx hl
  by_cases h25 : r≤(93/200:ℝ)
  · exact large_25 ⟨by linarith only [h24],h25⟩ hx hl
  by_cases h26 : r≤(187/400:ℝ)
  · exact large_26 ⟨by linarith only [h25],h26⟩ hx hl
  by_cases h27 : r≤(47/100:ℝ)
  · exact large_27 ⟨by linarith only [h26],h27⟩ hx hl
  by_cases h28 : r≤(189/400:ℝ)
  · exact large_28 ⟨by linarith only [h27],h28⟩ hx hl
  by_cases h29 : r≤(19/40:ℝ)
  · exact large_29 ⟨by linarith only [h28],h29⟩ hx hl
  by_cases h30 : r≤(191/400:ℝ)
  · exact large_30 ⟨by linarith only [h29],h30⟩ hx hl
  by_cases h31 : r≤(12/25:ℝ)
  · exact large_31 ⟨by linarith only [h30],h31⟩ hx hl
  by_cases h32 : r≤(193/400:ℝ)
  · exact large_32 ⟨by linarith only [h31],h32⟩ hx hl
  by_cases h33 : r≤(97/200:ℝ)
  · exact large_33 ⟨by linarith only [h32],h33⟩ hx hl
  by_cases h34 : r≤(39/80:ℝ)
  · exact large_34 ⟨by linarith only [h33],h34⟩ hx hl
  by_cases h35 : r≤(49/100:ℝ)
  · exact large_35 ⟨by linarith only [h34],h35⟩ hx hl
  by_cases h36 : r≤(197/400:ℝ)
  · exact large_36 ⟨by linarith only [h35],h36⟩ hx hl
  by_cases h37 : r≤(99/200:ℝ)
  · exact large_37 ⟨by linarith only [h36],h37⟩ hx hl
  by_cases h38 : r≤(199/400:ℝ)
  · exact large_38 ⟨by linarith only [h37],h38⟩ hx hl
  by_cases h39 : r≤(1/2:ℝ)
  · exact large_39 ⟨by linarith only [h38],h39⟩ hx hl
  by_cases h40 : r≤(201/400:ℝ)
  · exact large_40 ⟨by linarith only [h39],h40⟩ hx hl
  by_cases h41 : r≤(101/200:ℝ)
  · exact large_41 ⟨by linarith only [h40],h41⟩ hx hl
  by_cases h42 : r≤(203/400:ℝ)
  · exact large_42 ⟨by linarith only [h41],h42⟩ hx hl
  by_cases h43 : r≤(51/100:ℝ)
  · exact large_43 ⟨by linarith only [h42],h43⟩ hx hl
  by_cases h44 : r≤(41/80:ℝ)
  · exact large_44 ⟨by linarith only [h43],h44⟩ hx hl
  by_cases h45 : r≤(103/200:ℝ)
  · exact large_45 ⟨by linarith only [h44],h45⟩ hx hl
  by_cases h46 : r≤(207/400:ℝ)
  · exact large_46 ⟨by linarith only [h45],h46⟩ hx hl
  by_cases h47 : r≤(13/25:ℝ)
  · exact large_47 ⟨by linarith only [h46],h47⟩ hx hl
  by_cases h48 : r≤(209/400:ℝ)
  · exact large_48 ⟨by linarith only [h47],h48⟩ hx hl
  exact large_49 ⟨by linarith only [h48],hr.2⟩ hx hl

end GaussianPropeller.FourCertificates

end OAI


-- ---- from OAI.Probability.GaussianPropeller.FourCells ----
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction
open FourCertificates ProbabilityBounds
open scoped RealInnerProductSpace
variable {d:ℕ}

lemma triangle_gram (u v w : Space d) (hs:u+v+w=0) :
    let D:=‖u‖^2*‖v‖^2-⟪u,v⟫^2
    D=‖u‖^2*‖w‖^2-⟪u,w⟫^2 ∧ D=‖v‖^2*‖w‖^2-⟪v,w⟫^2 ∧
    4*D=(‖u‖^2+‖v‖^2+‖w‖^2)^2-2*(‖u‖^4+‖v‖^4+‖w‖^4) := by
  have hw:w=-(u+v) := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hs)
  subst w
  simp only [norm_neg,norm_add_sq_real,inner_neg_right,inner_add_right,real_inner_self_eq_norm_sq,
    real_inner_comm u v]
  constructor
  · ring
  constructor
  · ring
  · have h4:‖u+v‖^4=(‖u‖^2+‖v‖^2+2*⟪u,v⟫)^2 := by rw [show (4:ℕ)=2*2 by rfl,pow_mul,norm_add_sq_real]; ring
    rw [h4]
    ring

lemma residual_fourth_le (x y:Space d) (hx:x≠0) :
    ‖residualVector x y‖^4≤‖y‖^4 := by
  have h:=residual_norm_sq (z:=x) (y:=y) hx
  have hle:‖residualVector x y‖^2≤‖y‖^2 := by nlinarith only [h,mul_nonneg (sq_nonneg (residualCoefficient x y)) (sq_nonneg ‖x‖)]
  have hh: (‖residualVector x y‖^2)^2≤(‖y‖^2)^2 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr hle
  simpa only [←pow_mul] using hh

lemma four_incompatibility (z:Fin 4→Space d) (P:Fin 4→ℝ)
    (hsum:∑ j,z j=0) (hnorm:∑ j,‖z j‖^2=1)
    (hpos:∀ j,z j≠0) (horder:Antitone (fun j=>‖z j‖))
    (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0)) (hcap:∀ j,‖z j‖≤2/3)
    (hprob:∑ j,P j=1) (hPh:∀ j,P j≤1/2)
    (hcap3:∀ j,‖z j‖≤(8/3:ℝ)*P j*(1-P j))
    (hlin:∀ j,0.415*‖z j‖+0.15*‖z j‖^2≤P j)
    (hloss:∀ j,∃ x≥(0:ℝ),p x=P j ∧
      (9/(8*Real.pi))*‖z j‖^2/(1+Real.sqrt (1-(4/3:ℝ)*‖z j‖^2))≤loss x)
    (hpair:∀ i j l, i≠j → i≠l →
      ‖residualVector (z i) (z j)‖^2*‖residualVector (z i) (z l)‖^2-
      ⟪residualVector (z i) (z j),residualVector (z i) (z l)⟫^2≤
      (3/Real.pi)^2*‖z i‖^2*(1+residualCoefficient (z i) (z j))^2*
      (1+residualCoefficient (z i) (z l))^2) : False := by
  have hn:‖z 0‖^2+‖z 1‖^2+‖z 2‖^2+‖z 3‖^2=1 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hnorm
  have hp:P 0+P 1+P 2+P 3=1 := by simpa [Fin.sum_univ_succ,add_assoc] using hprob
  have hq:∀ j,‖z j‖^2≤(2/3:ℝ)^2 := fun j=>(sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr (hcap j)
  have hquartic:∀ j, (147/500:ℝ)≤‖z j‖ → quartic ‖z j‖≤P j := by
    intro j hj
    by_cases ht:‖z j‖≤79/200
    · obtain ⟨x,hx,hpx,hl⟩:=hloss j
      rw [←hpx]
      exact (quartic_of_loss ⟨hj,ht⟩ hx hl).le
    · exact quartic_from_cap ⟨(le_of_not_ge ht),(hcap j)⟩ (hPh j) (hcap3 j)
  by_cases ht:‖z 3‖≤39/250
  · have ht2:‖z 3‖^2≤(39/250:ℝ)^2 := (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr ht
    have h0:(147/500:ℝ)≤‖z 0‖ := by nlinarith only [hn,hq 1,hq 2,ht2,norm_nonneg (z 0)]
    have h1:(147/500:ℝ)≤‖z 1‖ := by nlinarith only [hn,hq 0,hq 2,ht2,norm_nonneg (z 1)]
    have h2:(147/500:ℝ)≤‖z 2‖ := by nlinarith only [hn,hq 0,hq 1,ht2,norm_nonneg (z 2)]
    let a:=residualCoefficient (z 3) (z 0)
    let b:=residualCoefficient (z 3) (z 1)
    let c:=residualCoefficient (z 3) (z 2)
    let u:=residualVector (z 3) (z 0)
    let v:=residualVector (z 3) (z 1)
    let w:=residualVector (z 3) (z 2)
    have ha:0≤a := (residualCoefficient_pos (hneg (by decide : (3:Fin 4)≠0))).le
    have hb:0≤b := (residualCoefficient_pos (hneg (by decide : (3:Fin 4)≠1))).le
    have hc:0≤c := (residualCoefficient_pos (hneg (by decide : (3:Fin 4)≠2))).le
    have habc:a+b+c=1 := by
      have hh:=residual_coefficient_sum z hsum 3 (hpos 3)
      have he:(Finset.univ.erase (3:Fin 4))={0,1,2} := by decide
      rw [he] at hh
      simpa [a,b,c,Finset.sum_insert,add_assoc] using hh
    have hs:u+v+w=0 := by
      have hh:=residual_sum z hsum 3 (hpos 3)
      have he:(Finset.univ.erase (3:Fin 4))={0,1,2} := by decide
      rw [he] at hh
      simpa [u,v,w,Finset.sum_insert,add_assoc] using hh
    obtain ⟨hD1,hD2,hD3⟩:=triangle_gram u v w hs
    have hu:‖u‖^2=‖z 0‖^2-a^2*‖z 3‖^2 := residual_norm_sq (hpos 3)
    have hv:‖v‖^2=‖z 1‖^2-b^2*‖z 3‖^2 := residual_norm_sq (hpos 3)
    have hw:‖w‖^2=‖z 2‖^2-c^2*‖z 3‖^2 := residual_norm_sq (hpos 3)
    have hH:‖u‖^2+‖v‖^2+‖w‖^2=1-‖z 3‖^2-(a^2+b^2+c^2)*‖z 3‖^2 := by
      nlinarith only [hu,hv,hw,hn]
    have he0:=hquartic 0 h0
    have he1:=hquartic 1 h1
    have he2:=hquartic 2 h2
    unfold quartic at he0 he1 he2
    have hV:(3/5:ℝ)*(‖u‖^4+‖v‖^4+‖w‖^4)≤(10003/40000:ℝ)-(83/200:ℝ)*‖z 3‖+(81/250:ℝ)*‖z 3‖^2 := by
      nlinarith only [he0,he1,he2,hlin 3,hn,hp,
        residual_fourth_le (z 3) (z 0) (hpos 3),residual_fourth_le (z 3) (z 1) (hpos 3),residual_fourth_le (z 3) (z 2) (hpos 3)]
    apply FourAlgebra.small_exclusion ⟨norm_nonneg _,ht⟩ ha hb hc habc hH hV hD3
    · exact hpair 3 0 1 (by decide) (by decide)
    · rw [hD1]; exact hpair 3 0 2 (by decide) (by decide)
    · rw [hD2]; exact hpair 3 1 2 (by decide) (by decide)
  have htlo:(39/250:ℝ)≤‖z 3‖ := (lt_of_not_ge ht).le
  have hmin:∀ j, ‖z 3‖≤‖z j‖ := fun j=>horder (show j≤3 by omega)
  have haff:∀ j,affine ‖z j‖≤P j := fun j=> affine_from_cap ⟨htlo.trans (hmin j),hcap j⟩ (hPh j) (hcap3 j)
  have ha0:=haff 0; have ha1:=haff 1; have ha2:=haff 2
  unfold affine at ha0 ha1 ha2
  by_cases ht18:‖z 3‖≤9/50
  · obtain ⟨x,hx,hpx,hl⟩:=hloss 3
    have hsmall:=small_of_loss ⟨htlo,ht18⟩ hx hl
    rw [hpx] at hsmall
    unfold small at hsmall
    have hprod:=mul_nonneg (sub_nonneg.mpr htlo) (sub_nonneg.mpr ht18)
    nlinarith only [ha0,ha1,ha2,hsmall,hn,hp,hprod,htlo,ht18]
  by_cases ht40:‖z 3‖≤2/5
  · have hlo:(9/50:ℝ)≤‖z 3‖ := (lt_of_not_ge ht18).le
    have hprod:=mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr ht40)
    nlinarith only [ha0,ha1,ha2,hlin 3,hn,hp,hprod,hlo,ht40]
  have hlarge:∀ j,large ‖z j‖≤P j := by
    intro j
    have hj:(2/5:ℝ)≤‖z j‖ := (le_of_not_ge ht40).trans (hmin j)
    by_cases hj525:‖z j‖≤21/40
    · obtain ⟨x,hx,hpx,hl⟩:=hloss j
      rw [←hpx]
      exact (large_of_loss ⟨hj,hj525⟩ hx hl).le
    · exact large_from_cap ⟨le_of_not_ge hj525,hcap j⟩ (hPh j) (hcap3 j)
  have hl0:=hlarge 0; have hl1:=hlarge 1; have hl2:=hlarge 2; have hl3:=hlarge 3
  unfold large at hl0 hl1 hl2 hl3
  nlinarith only [hl0,hl1,hl2,hl3,hn,hp]

end GaussianPropeller.Reduction

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace
open FourCertificates ProbabilityBounds
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.four_incompatibility := @_root_.OAI.GaussianPropeller.Reduction.four_incompatibility
