-- Prove2me | solution 1 for OAI.GaussianPropeller.FourCertificates.affine_from_cap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:17:24.18476+00:00
-- url     : https://prove2.me/submissions/c0f3c6ff-c94f-406e-a95b-33db8f9763db

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/CapCertificates.lean:L90-L105
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.FourCertificates.affine_from_cap. The node keeps its source
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

lemma affine_cap_poly_0 {r:ℝ} (hr:r∈Icc (39/250:ℝ) (617/1500:ℝ)) :
    (8/3:ℝ)*affine r*(1-affine r)≤r := by
  have hl : 0≤r-(39/250:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(617/1500:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) =
    (2391277896991494/336213480015625:ℝ)*(r-(39/250:ℝ))^0*((617/1500:ℝ)-r)^4 + (16684638404902488/336213480015625:ℝ)*(r-(39/250:ℝ))^1*((617/1500:ℝ)-r)^3 + (26003061476182116/336213480015625:ℝ)*(r-(39/250:ℝ))^2*((617/1500:ℝ)-r)^2 + (13152961928422872/336213480015625:ℝ)*(r-(39/250:ℝ))^3*((617/1500:ℝ)-r)^1 + (2112546341425734/336213480015625:ℝ)*(r-(39/250:ℝ))^4*((617/1500:ℝ)-r)^0 := by unfold affine; ring
  have hp : 0≤r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma affine_cap_poly_1 {r:ℝ} (hr:r∈Icc (617/1500:ℝ) (539/1000:ℝ)) :
    (8/3:ℝ)*affine r*(1-affine r)≤r := by
  have hl : 0≤r-(617/1500:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(539/1000:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) =
    (33800741462811744/336213480015625:ℝ)*(r-(617/1500:ℝ))^0*((539/1000:ℝ)-r)^4 + (97580753349487488/336213480015625:ℝ)*(r-(617/1500:ℝ))^1*((539/1000:ℝ)-r)^3 + (86815626229463616/336213480015625:ℝ)*(r-(617/1500:ℝ))^2*((539/1000:ℝ)-r)^2 + (24717526517503872/336213480015625:ℝ)*(r-(617/1500:ℝ))^3*((539/1000:ℝ)-r)^1 + (2351197555989984/336213480015625:ℝ)*(r-(617/1500:ℝ))^4*((539/1000:ℝ)-r)^0 := by unfold affine; ring
  have hp : 0≤r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma affine_cap_poly_2 {r:ℝ} (hr:r∈Icc (539/1000:ℝ) (6851/12000:ℝ)) :
    (8/3:ℝ)*affine r*(1-affine r)≤r := by
  have hl : 0≤r-(539/1000:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(6851/12000:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) =
    (601906574333435904/336213480015625:ℝ)*(r-(539/1000:ℝ))^0*((6851/12000:ℝ)-r)^4 + (1427611174546931712/336213480015625:ℝ)*(r-(539/1000:ℝ))^1*((6851/12000:ℝ)-r)^3 + (1099717789846450176/336213480015625:ℝ)*(r-(539/1000:ℝ))^2*((6851/12000:ℝ)-r)^2 + (369439192509401088/336213480015625:ℝ)*(r-(539/1000:ℝ))^3*((6851/12000:ℝ)-r)^1 + (96095288257720704/336213480015625:ℝ)*(r-(539/1000:ℝ))^4*((6851/12000:ℝ)-r)^0 := by unfold affine; ring
  have hp : 0≤r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma affine_cap_poly_3 {r:ℝ} (hr:r∈Icc (6851/12000:ℝ) (3617/6000:ℝ)) :
    (8/3:ℝ)*affine r*(1-affine r)≤r := by
  have hl : 0≤r-(6851/12000:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(3617/6000:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) =
    (96095288257720704/336213480015625:ℝ)*(r-(6851/12000:ℝ))^0*((3617/6000:ℝ)-r)^4 + (399323113552364544/336213480015625:ℝ)*(r-(6851/12000:ℝ))^1*((3617/6000:ℝ)-r)^3 + (1189369552975340544/336213480015625:ℝ)*(r-(6851/12000:ℝ))^2*((3617/6000:ℝ)-r)^2 + (1613038898973118464/336213480015625:ℝ)*(r-(6851/12000:ℝ))^3*((3617/6000:ℝ)-r)^1 + (727566456673695744/336213480015625:ℝ)*(r-(6851/12000:ℝ))^4*((3617/6000:ℝ)-r)^0 := by unfold affine; ring
  have hp : 0≤r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma affine_cap_poly_4 {r:ℝ} (hr:r∈Icc (3617/6000:ℝ) (2/3:ℝ)) :
    (8/3:ℝ)*affine r*(1-affine r)≤r := by
  have hl : 0≤r-(3617/6000:ℝ) := sub_nonneg.mpr hr.1
  have hu : 0≤(2/3:ℝ)-r := sub_nonneg.mpr hr.2
  have he : r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) =
    (45472903542105984/336213480015625:ℝ)*(r-(3617/6000:ℝ))^0*((2/3:ℝ)-r)^4 + (2752359841069056/2689707840125:ℝ)*(r-(3617/6000:ℝ))^1*((2/3:ℝ)-r)^3 + (300227333815296/107588313605:ℝ)*(r-(3617/6000:ℝ))^2*((2/3:ℝ)-r)^2 + (67293444556800/21517662721:ℝ)*(r-(3617/6000:ℝ))^3*((2/3:ℝ)-r)^1 + (26399424960000/21517662721:ℝ)*(r-(3617/6000:ℝ))^4*((2/3:ℝ)-r)^0 := by unfold affine; ring
  have hp : 0≤r-(8/3:ℝ)*affine r*(1-affine r)-(1/10000000:ℝ) := by rw [he]; positivity
  linarith only [hp]

lemma affine_from_cap {r P:ℝ} (hr:r∈Icc (39/250:ℝ) (2/3:ℝ)) (hP:P≤1/2)
    (hcap:r≤(8/3:ℝ)*P*(1-P)) : affine r≤P := by
  have hr0 : 0≤r := by linarith only [hr.1]
  have h2 : r^2≤(2/3:ℝ)^2 := (sq_le_sq₀ hr0 (by norm_num)).mpr hr.2
  have h4 : r^4≤(2/3:ℝ)^4 := pow_le_pow_left₀ hr0 hr.2 4
  apply cap_envelope hP (by unfold affine; nlinarith only [h2,h4]) hcap

  by_cases h0 : r≤(617/1500:ℝ)
  · exact affine_cap_poly_0 ⟨by linarith only [hr.1],h0⟩
  by_cases h1 : r≤(539/1000:ℝ)
  · exact affine_cap_poly_1 ⟨by linarith only [h0],h1⟩
  by_cases h2 : r≤(6851/12000:ℝ)
  · exact affine_cap_poly_2 ⟨by linarith only [h1],h2⟩
  by_cases h3 : r≤(3617/6000:ℝ)
  · exact affine_cap_poly_3 ⟨by linarith only [h2],h3⟩
  exact affine_cap_poly_4 ⟨by linarith only [h3],hr.2⟩

end GaussianPropeller.FourCertificates

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.FourCertificates
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


theorem solution : type_of% @_root_.OAI.GaussianPropeller.FourCertificates.affine_from_cap := @_root_.OAI.GaussianPropeller.FourCertificates.affine_from_cap
