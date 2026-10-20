-- Prove2me | solution 1 for OAI.GaussianPropeller.FourAlgebra.small_core
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:30:33.461661+00:00
-- url     : https://prove2.me/submissions/53a2ccc3-b8b3-46e0-9b3e-1f9b5b3e717b

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/FourAlgebra.lean:L83-L129
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.FourAlgebra.small_core. The node keeps its source
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
import Theorems.Thm_OAI_GaussianPropeller_FourAlgebra_quartic_positive

-- ---- from OAI.Probability.GaussianPropeller.FourAlgebra ----
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

namespace GaussianPropeller.FourAlgebra
open scoped RealInnerProductSpace

lemma small_numeric_one {t:ℝ} (ht:t∈Set.Icc (0:ℝ) (39/250:ℝ)) :
    4*(150/157:ℝ)^2*t^2*(13/10:ℝ)^4 <
      (1-2*t^2)^2-(10/3:ℝ)*((10003/40000:ℝ)-(83/200:ℝ)*t+(81/250:ℝ)*t^2) := by
  have hh:=quartic_positive (c₀:=(1997/12000:ℝ)) (c₁:=(83/60:ℝ))
    (c₂:=-(9556648/616225:ℝ)) (c₄:=4) ht.1 ht.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  nlinarith only [hh]

lemma small_numeric_two {t:ℝ} (ht:t∈Set.Icc (0:ℝ) (39/250:ℝ)) :
    4*(150/157:ℝ)^2*t^2*(4/3:ℝ)^4 <
      (1-(14/9:ℝ)*t^2)^2-(10/3:ℝ)*((10003/40000:ℝ)-(83/200:ℝ)*t+(81/250:ℝ)*t^2) := by
  have hh:=quartic_positive (c₀:=(1997/12000:ℝ)) (c₁:=(83/60:ℝ))
    (c₂:=-(87244007/5546025:ℝ)) (c₄:=(196/81:ℝ)) ht.1 ht.2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  nlinarith only [hh]

lemma pair_product {a b B:ℝ} (ha:0≤a) (hb:0≤b) (hab:a+b≤B) :
    (1+a)^2*(1+b)^2≤(1+B/2)^4 := by
  have hB:0≤B := (add_nonneg ha hb).trans hab
  have hh : (1+a)*(1+b)≤(1+B/2)^2 := by
    have hs:(a+b)^2≤B^2 := (sq_le_sq₀ (add_nonneg ha hb) hB).mpr hab
    nlinarith only [hs,hab,sq_nonneg (a-b)]
  have hq:((1+a)*(1+b))^2≤((1+B/2)^2)^2 :=
    (sq_le_sq₀ (by positivity) (sq_nonneg _)).mpr hh
  nlinarith only [hq]

lemma small_core {t a b c H V D:ℝ} (ht:t∈Set.Icc (0:ℝ) (39/250:ℝ))
    (ha:0≤a) (hb:0≤b) (hc:0≤c) (hs:a+b+c=1) (hac:a≤c) (hbc:b≤c)
    (hH:H=1-t^2-(a^2+b^2+c^2)*t^2)
    (hV:(3/5:ℝ)*V≤(10003/40000:ℝ)-(83/200:ℝ)*t+(81/250:ℝ)*t^2)
    (hD:4*D=H^2-2*V)
    (hpair:D≤(3/Real.pi)^2*t^2*(1+a)^2*(1+b)^2) : False := by
  have hk : (3/Real.pi)^2≤(150/157:ℝ)^2 := by
    apply (sq_le_sq₀ (by positivity) (by norm_num)).mpr
    rw [div_le_iff₀ Real.pi_pos]
    have hp:=Real.pi_gt_d2
    linarith only [hp]
  have hab : a+b≤2/3 := by linarith only [hac,hbc,hs]
  have ht2 : t^2≤(39/250:ℝ)^2 := (sq_le_sq₀ ht.1 (by norm_num)).mpr ht.2
  have hcoef : a^2+b^2+c^2≤1 := by
    nlinarith only [hs,mul_nonneg ha hb,mul_nonneg ha hc,mul_nonneg hb hc]
  have hpair' : D≤(150/157:ℝ)^2*t^2*(1+a)^2*(1+b)^2 := hpair.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hk (sq_nonneg t)) (sq_nonneg (1+a))) (sq_nonneg (1+b)))
  by_cases hsmall : a+b≤3/5
  · have hprod := pair_product ha hb hsmall
    have hd : D≤(150/157:ℝ)^2*t^2*(13/10:ℝ)^4 := by
      have hh:=mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg (150/157:ℝ)) (sq_nonneg t))
      norm_num at hh
      nlinarith only [hpair',hh]
    have hl : 1-2*t^2≤H := by
      have hh:=mul_le_mul_of_nonneg_right hcoef (sq_nonneg t)
      nlinarith only [hh,hH]
    have hl0 : 0≤1-2*t^2 := by nlinarith only [ht2]
    have hsq : (1-2*t^2)^2≤H^2 := (sq_le_sq₀ hl0 (hl0.trans hl)).mpr hl
    have hn:=small_numeric_one ht
    nlinarith only [hV,hD,hd,hsq,hn]
  · have hablo : 3/5≤a+b := (lt_of_not_ge hsmall).le
    have hcoef' : a^2+b^2+c^2≤5/9 := by
      have hh:=mul_nonneg (sub_nonneg.mpr hab) (show 0≤2*(a+b)-2/3 by linarith only [hablo])
      nlinarith only [hs,hh,mul_nonneg ha hb]
    have hprod := pair_product ha hb hab
    have hd : D≤(150/157:ℝ)^2*t^2*(4/3:ℝ)^4 := by
      have hh:=mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg (150/157:ℝ)) (sq_nonneg t))
      norm_num at hh
      nlinarith only [hpair',hh]
    have hl : 1-(14/9:ℝ)*t^2≤H := by
      have hh:=mul_le_mul_of_nonneg_right hcoef' (sq_nonneg t)
      nlinarith only [hh,hH]
    have hl0 : 0≤1-(14/9:ℝ)*t^2 := by nlinarith only [ht2]
    have hsq : (1-(14/9:ℝ)*t^2)^2≤H^2 := (sq_le_sq₀ hl0 (hl0.trans hl)).mpr hl
    have hn:=small_numeric_two ht
    nlinarith only [hV,hD,hd,hsq,hn]

end GaussianPropeller.FourAlgebra

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.FourAlgebra
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
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.FourAlgebra.small_core := @_root_.OAI.GaussianPropeller.FourAlgebra.small_core
