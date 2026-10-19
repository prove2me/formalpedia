-- Prove2me | solution 1 for OAI.GaussianPropeller.Cap.cone_four
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:18:34.387988+00:00
-- url     : https://prove2.me/submissions/051e358f-6fa4-4212-aeb4-41dffdb0ef17

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/CapNumeric.lean:L205-L270
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Cap.cone_four. The node keeps its source
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
import Theorems.Thm_OAI_GaussianPropeller_Cap_capP_three_sphere
import Theorems.Thm_OAI_GaussianPropeller_Cap_integral_cone_norm
import Theorems.Thm_OAI_GaussianPropeller_Cap_moment_rearrange
import Theorems.Thm_OAI_GaussianPropeller_Polar_integral_norm_pow_exp
import Theorems.Thm_OAI_GaussianPropeller_Polar_radial_half_four
import Theorems.Thm_OAI_GaussianPropeller_Polar_radial_scale

-- ---- from OAI.Probability.GaussianPropeller.Polar ----
namespace OAI

universe uι

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
namespace GaussianPropeller.Polar
open Translation

variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "S" => sphere (0 : E) 1
local notation "V" => (volume : Measure E)

end GaussianPropeller.Polar

namespace GaussianPropeller.Polar
open Real
lemma radial_eq (n : ℕ) {b : ℝ} (hb : 0<b) :
    radial n b = b ^ (-((n:ℝ)+1)/2) * (1/2) * Gamma (((n:ℝ)+1)/2) := by
  have hh := integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=n) (b:=b)
    (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) n]) hb
  simpa only [Real.rpow_natCast, Real.rpow_two, neg_mul, radial] using hh

lemma radial_pos (n : ℕ) {b : ℝ} (hb : 0<b) : 0<radial n b := by
  rw [radial_eq n hb]
  exact mul_pos (mul_pos (rpow_pos_of_pos hb _) (by norm_num))
    (Gamma_pos_of_pos (by positivity))

lemma radial_half_three : radial 3 (1/2) = 2 := by
  rw [radial_eq 3 (by norm_num)]
  norm_num [Gamma_nat_eq_factorial, rpow_neg, rpow_natCast]

variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "S" => Metric.sphere (0:E) 1

end GaussianPropeller.Polar

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

variable {n : ℕ}
lemma capM_eq (hn : 0<n) (a : ℝ) :
    capM n a = gaussianConst * (Real.sqrt (1+a^2))⁻¹^n := by
  let : NeZero n := ⟨by omega⟩
  have hh := integral_norm_pow_exp (ι:=Fin n) 0 (a:=a^2/2) (by positivity)
  have hs := radial_scale (n-1) (b:=a^2/2+1/2) (by positivity)
  simp only [Fintype.card_fin, add_zero, pow_zero, one_mul] at hh
  unfold capM
  have he : (fun y : CE n => density (a*‖y‖)) = fun y => Real.exp (-(a^2/2)*‖y‖^2) := by
    funext y; unfold density; congr 1; ring
  rw [he,hh,hs,show 2*(a^2/2+1/2)=1+a^2 by ring,
    show n-1+1=n by omega, mul_div_cancel_right₀ _ (radial_pos _ (by norm_num)).ne']

end GaussianPropeller.Cap

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

lemma integrable_coord : Integrable (fun x : CE (n+1) => x 0) (stdGaussian (CE (n+1))) := by
  apply Integrable.mono' IsGaussian.integrable_id.norm (by fun_prop)
  filter_upwards [] with x
  exact PiLp.norm_apply_le x 0

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar

lemma cap_parameter {b : ℝ} (hb : 0≤b) (hb1 : b<1) :
    Real.sqrt (1+(b/Real.sqrt (1-b^2))^2) = (Real.sqrt (1-b^2))⁻¹ ∧
    (b/Real.sqrt (1-b^2))/Real.sqrt (1+(b/Real.sqrt (1-b^2))^2)=b := by
  have hpos : 0<1-b^2 := by nlinarith only [hb,hb1]
  have hp : 0<Real.sqrt (1-b^2) := Real.sqrt_pos.mpr hpos
  have hs := Real.sq_sqrt hpos.le
  have he : 1+(b/Real.sqrt (1-b^2))^2 = ((Real.sqrt (1-b^2))⁻¹)^2 := by
    field_simp
    nlinarith only [hs]
  refine ⟨?_,?_⟩
  · rw [he,Real.sqrt_sq (by positivity)]
  · rw [he,Real.sqrt_sq (by positivity)]
    field_simp

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar
open scoped Topology

end GaussianPropeller.Cap

end OAI

-- ---- from OAI.Probability.GaussianPropeller.CapNumeric ----
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

namespace GaussianPropeller.CapNumeric
open Real Set
lemma hasDerivAt_Q (t:ℝ) : HasDerivAt Q (-1/35-2*t/504) t := by
  unfold Q
  convert (((hasDerivAt_id t).div_const 35).const_sub (4/15) |>.sub
    (((hasDerivAt_id t).pow 2).div_const 504)) using 1 <;> first | rfl | (simp only [id_eq]; ring)
lemma hasDerivAt_R (t:ℝ) : HasDerivAt R (-31/15+67*t/140+11*t^2/168) t := by
  unfold R
  convert ((((hasDerivAt_id t).const_mul 31).div_const 15).const_sub (4/3) |>.add
    ((((hasDerivAt_id t).pow 2).const_mul 67).div_const 280) |>.add
    ((((hasDerivAt_id t).pow 3).const_mul 11).div_const 504)) using 1 <;> first | rfl | (simp only [id_eq]; ring)
lemma hasDerivAt_U {t:ℝ} (ht:0<t) : HasDerivAt U (Real.sqrt (2*t)*t/2*R t) t := by
  have hs : 0<Real.sqrt (2*t) := by positivity
  have hsq := Real.sq_sqrt (show 0≤2*t by positivity)
  unfold U
  convert ((((hasDerivAt_id t).const_sub 1).mul ((hasDerivAt_id t).pow 2)).mul
    (((hasDerivAt_id t).const_mul 2).sqrt (by positivity)) |>.mul (hasDerivAt_Q t)) using 1 <;> first | rfl | (dsimp [Q,R]; field_simp; rw [hsq]; ring)

lemma Q_nonneg {t:ℝ} (ht:t∈Icc (0:ℝ) 1) : 0≤Q t := by
  have hsq : t^2≤1 := by nlinarith only [ht.1,ht.2]
  unfold Q; linarith only [ht.2,hsq]
lemma Q_antitone : AntitoneOn Q (Icc (0:ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (by unfold Q; fun_prop)
    (fun t ht=>(hasDerivAt_Q t).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hasDerivAt_Q t).deriv]
  rw [interior_Icc] at ht
  linarith only [ht.1]
lemma R_antitone : AntitoneOn R (Icc (0:ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (by unfold R; fun_prop)
    (fun t ht=>(hasDerivAt_R t).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hasDerivAt_R t).deriv]
  rw [interior_Icc] at ht
  have hsq : t^2≤1 := by nlinarith only [ht.1,ht.2]
  linarith only [ht.2,hsq]

lemma U_middle {t:ℝ} (ht:t∈Icc (7067/10000:ℝ) (7068/10000:ℝ)) : U t < (428/10000:ℝ) := by
  have ht0 : 0≤t := by linarith only [ht.1]
  have ht1 : t≤1 := by linarith only [ht.2]
  have hq : Q t≤Q (7067/10000) := Q_antitone (by norm_num) ⟨ht0,ht1⟩ ht.1
  have hs : Real.sqrt (2*t)≤1189/1000 := Real.sqrt_le_iff.mpr ⟨by norm_num,by linarith only [ht.2]⟩
  have ht2 : t^2≤(7068/10000:ℝ)^2 := (sq_le_sq₀ ht0 (by norm_num)).mpr ht.2
  have hp := mul_le_mul (show 1-t≤2933/10000 by linarith only [ht.1]) ht2 (sq_nonneg t) (by norm_num)
  have hp' := mul_le_mul hp hs (Real.sqrt_nonneg _) (by norm_num)
  have hp'' := mul_le_mul hp' hq (Q_nonneg ⟨ht0,ht1⟩) (by norm_num)
  dsimp [U]
  exact hp''.trans_lt (by norm_num [Q])

lemma U_bound {t:ℝ} (ht:t∈Icc (0:ℝ) 1) : U t < (428/10000:ℝ) := by
  have hl : MonotoneOn U (Icc (0:ℝ) (7067/10000)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by unfold U Q; fun_prop)
      (fun x hx=>(hasDerivAt_U (by rw [interior_Icc] at hx; exact hx.1)).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_U hx.1).deriv]
    have hR := R_antitone ⟨hx.1.le,by linarith only [hx.2]⟩ (by norm_num) hx.2.le
    have hpos : 0≤R (7067/10000) := by norm_num [R]
    exact mul_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hx.1.le) (by norm_num)) (hpos.trans hR)
  have hu : AntitoneOn U (Icc (7068/10000:ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (by unfold U Q; fun_prop)
      (fun x hx=>(hasDerivAt_U (by rw [interior_Icc] at hx; linarith only [hx.1])).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0<x := by linarith only [hx.1]
    rw [(hasDerivAt_U hx0).deriv]
    have hR := R_antitone (by norm_num) ⟨hx0.le,hx.2.le⟩ hx.1.le
    have hneg : R (7068/10000)≤0 := by norm_num [R]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hR.trans hneg)
  by_cases htl : t≤7067/10000
  · exact (hl ⟨ht.1,htl⟩ (by norm_num) htl).trans_lt (U_middle (by norm_num))
  by_cases htu : 7068/10000≤t
  · exact (hu (by norm_num) ⟨htu,ht.2⟩ htu).trans_lt (U_middle (by norm_num))
  exact U_middle ⟨(lt_of_not_ge htl).le,(lt_of_not_ge htu).le⟩

end GaussianPropeller.CapNumeric

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar CapNumeric

lemma integral_u_sqrt {b:ℝ} (hb:b∈Icc (0:ℝ) 1) :
    (∫ u in b..1, u*Real.sqrt (1-u^2)) = (1-b^2)*Real.sqrt (1-b^2)/3 := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.2
    (f:=fun u:ℝ=>-(1-u^2)*Real.sqrt (1-u^2)/3)
    (f':=fun u:ℝ=>u*Real.sqrt (1-u^2)) (by fun_prop) (fun u hu=>?_)
    (by exact (by fun_prop : Continuous (fun u:ℝ=>u*Real.sqrt (1-u^2))).intervalIntegrable _ _)
  · simp only [one_pow,sub_self,neg_zero,zero_mul,zero_div,zero_sub] at hh
    rw [hh]; ring
  have hu0 : 0≤u := hb.1.trans hu.1.le
  have hsq : u^2<1 := by nlinarith only [hu0,hu.2]
  have hp : 0<Real.sqrt (1-u^2) := by positivity
  have hs := Real.sq_sqrt (show 0≤1-u^2 by linarith only [hsq])
  have hd := ((hasDerivAt_id u).pow 2).const_sub 1
  convert ((hd.neg.mul (hd.sqrt (by change 1-u^2≠0; linarith only [hsq]))).div_const 3) using 1 <;> first | rfl | (dsimp; field_simp; rw [hs]; ring)

lemma sphereGap_eq {b:ℝ} (hb:b∈Icc (0:ℝ) 1) :
    sphereGap b = (1-b^2)*Real.sqrt (1-b^2)/3-b*sphereTail b := by
  have he : (fun u:ℝ => (u-b)*Real.sqrt (1-u^2)) =
      fun u=> u*Real.sqrt (1-u^2)-b*Real.sqrt (1-u^2) := by funext u; ring
  rw [sphereGap,he,intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun u:ℝ=>u*Real.sqrt (1-u^2))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun u:ℝ=>b*Real.sqrt (1-u^2))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,integral_u_sqrt hb]
  rfl

lemma sqrt_two_upper {s:ℝ} (hs:s∈Icc (0:ℝ) 1) :
    Real.sqrt (2*s-s^2) ≤ Real.sqrt (2*s)*(1-s/4-s^2/32) := by
  have hs2 : s^2≤1 := by nlinarith only [hs.1,hs.2]
  have hp : 0≤1-s/4-s^2/32 := by linarith only [hs.2,hs2]
  have ha : 0≤2*s-s^2 := by nlinarith only [hs.1,hs.2]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hp)).mp
  rw [mul_pow,Real.sq_sqrt ha,Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hs.1)]
  have he : 2*s*(1-s/4-s^2/32)^2-(2*s-s^2) = s^4/32+s^5/512 := by ring
  nlinarith only [he,pow_nonneg hs.1 4,pow_nonneg hs.1 5]

lemma hasDerivAt_sqrt_two {s:ℝ} (hs:0<s) : HasDerivAt (fun s:ℝ=>Real.sqrt (2*s))
    (Real.sqrt (2*s)/(2*s)) s := by
  have hp : 0<Real.sqrt (2*s) := by positivity
  have hsq := Real.sq_sqrt (show 0≤2*s by positivity)
  convert (((hasDerivAt_id s).const_mul 2).sqrt (by positivity)) using 1 <;> first | rfl | (dsimp; field_simp; nlinarith only [hsq])

lemma hasDerivAt_gapPrim (t:ℝ) {s:ℝ} (hs:0<s) : HasDerivAt (gapPrim t)
    ((t-s)*Real.sqrt (2*s)*(1-s/4-s^2/32)) s := by
  unfold gapPrim
  convert (hasDerivAt_sqrt_two hs).mul
    (((((hasDerivAt_id s).const_mul (2*t)).div_const 3).sub
      (((hasDerivAt_id s).pow 2).const_mul (2/5+t/10))).add
      (((hasDerivAt_id s).pow 3).const_mul (1/14-t/112)) |>.add
      (((hasDerivAt_id s).pow 4).div_const 144)) using 1 <;> first | rfl | (dsimp; field_simp; ring)

lemma sphereGap_upper {b:ℝ} (hb:b∈Icc (0:ℝ) 1) :
    b*sphereGap b ≤ U (1-b) := by
  let t := 1-b
  have ht : t∈Icc (0:ℝ) 1 := ⟨by dsimp [t]; linarith only [hb.2],by dsimp [t]; linarith only [hb.1]⟩
  have hsub := intervalIntegral.integral_comp_sub_left (a:=(0:ℝ)) (b:=t)
    (fun u:ℝ=>(u-b)*Real.sqrt (1-u^2)) 1
  have he : (fun s:ℝ=>(1-s-b)*Real.sqrt (1-(1-s)^2)) =
      fun s=>(t-s)*Real.sqrt (2*s-s^2) := by funext s; dsimp [t]; rw [show 1-(1-s)^2=2*s-s^2 by ring]; ring
  rw [he,show 1-t=b by dsimp [t]; ring,sub_zero] at hsub
  have hi := intervalIntegral.integral_mono_on (μ:=volume) ht.1
    ((by fun_prop : Continuous (fun s:ℝ=>(t-s)*Real.sqrt (2*s-s^2))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun s:ℝ=>(t-s)*Real.sqrt (2*s)*(1-s/4-s^2/32))).intervalIntegrable _ _)
    (fun s hs=>show (t-s)*Real.sqrt (2*s-s^2)≤(t-s)*Real.sqrt (2*s)*(1-s/4-s^2/32) from by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (sqrt_two_upper ⟨hs.1,hs.2.trans ht.2⟩) (sub_nonneg.mpr hs.2))
  have hj := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (f:=gapPrim t) (by unfold gapPrim; fun_prop)
    (fun s hs=>hasDerivAt_gapPrim t hs.1)
    ((by fun_prop : Continuous (fun s:ℝ=>(t-s)*Real.sqrt (2*s)*(1-s/4-s^2/32))).intervalIntegrable _ _)
  rw [hsub,hj,show gapPrim t 0=0 by simp [gapPrim],sub_zero] at hi
  have hh := mul_le_mul_of_nonneg_left hi hb.1
  change b*sphereGap b≤_ at hh
  convert hh using 1
  dsimp [gapPrim,U,CapNumeric.Q,t]
  ring

end GaussianPropeller.Cap

namespace GaussianPropeller.Cap
open OneCell ProbabilityBounds Polar CapNumeric

lemma cone_four (K : Set (CE 4)) (hK : MeasurableSet K)
    (hcone : ∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K)
    (hP : 0<(stdGaussian (CE 4)).real K)
    (hM0 : 0≤∫ x : CE 4, K.indicator (fun x=>x 0) x ∂stdGaussian (CE 4)) :
    (∫ x : CE 4, K.indicator (fun x=>x 0) x ∂stdGaussian (CE 4))^2 ≤
      (963/2500:ℝ)*(stdGaussian (CE 4)).real K := by
  let P := (stdGaussian (CE 4)).real K
  let M := ∫ x : CE 4, K.indicator (fun x=>x 0) x ∂stdGaussian (CE 4)
  let ρ := 3*Real.sqrt (2*Real.pi)/4
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hρsq : ρ^2=9*Real.pi/8 := by
    dsimp [ρ]
    rw [div_pow,mul_pow,Real.sq_sqrt (by positivity)]
    ring
  have hρrad : radial 4 (1/2)/radial 3 (1/2)=ρ := by
    rw [radial_half_four,radial_half_three]; dsimp [ρ]; ring
  have hφ : gaussianConst=ρ*(2/Real.pi)/3 := by
    have hs := Real.sq_sqrt (show 0≤2*Real.pi by positivity)
    dsimp [gaussianConst,ρ]
    field_simp
    nlinarith only [hs]
  have hm : M≤ρ*P := by
    have hn : Integrable (fun x:CE 4=>‖x‖) (stdGaussian (CE 4)) := IsGaussian.integrable_id.norm
    have hh := integral_mono (integrable_coord.indicator hK) (hn.indicator hK) (fun x=>show
        K.indicator (fun x=>x 0) x≤K.indicator (fun x=>‖x‖) x from by
      by_cases hx:x∈K
      · simp only [indicator_of_mem hx]
        exact (le_abs_self _).trans (PiLp.norm_apply_le x 0)
      · simp [hx])
    rw [integral_cone_norm (by omega) K hK hcone,hρrad] at hh
    exact hh
  let b := M/(2*ρ*P)
  have hb : 0≤b := div_nonneg hM0 (by positivity)
  have hbhalf : b≤1/2 := (div_le_iff₀ (by positivity : 0<2*ρ*P)).mpr (by nlinarith only [hm])
  have hb1 : b<1 := by linarith only [hbhalf]
  have hM : M=2*ρ*P*b := by dsimp [b]; field_simp [ne_of_gt (show 0<P from hP)]
  have hh := cap_parameter hb hb1
  have hr := moment_rearrange (n:=3) K hK hcone (a:=b/Real.sqrt (1-b^2)) (by positivity)
  rw [capM_eq (by omega),hh.2,hh.1,inv_inv,capP_three_sphere ⟨by linarith only [hb],hb1⟩,
    hρrad] at hr
  have hs := Real.sq_sqrt (show 0≤1-b^2 by nlinarith only [hb,hb1])
  have hg := sphereGap_eq ⟨hb,hb1.le⟩
  have he : gaussianConst*Real.sqrt (1-b^2)^3+b*ρ*(P-(2/Real.pi)*sphereTail b) =
      ρ*(b*P+(2/Real.pi)*sphereGap b) := by
    rw [hφ,hg]
    have hs3 : Real.sqrt (1-b^2)^3 = (1-b^2)*Real.sqrt (1-b^2) := by
      rw [pow_succ,hs]
    rw [hs3]; ring
  change M≤gaussianConst*Real.sqrt (1-b^2)^3+b*ρ*(P-(2/Real.pi)*sphereTail b) at hr
  rw [he] at hr
  have hu : b*sphereGap b≤428/10000 :=
    (sphereGap_upper ⟨hb,hb1.le⟩).trans (U_bound ⟨by linarith only [hb1],by linarith only [hb]⟩).le
  have hmb : M*b/2≤ρ*(2/Real.pi)*(b*sphereGap b) := by
    have hh := mul_le_mul_of_nonneg_right hr hb
    have he : ρ*(b*P+(2/Real.pi)*sphereGap b)*b = M*b/2+ρ*(2/Real.pi)*(b*sphereGap b) := by rw [hM]; ring
    rw [he] at hh
    linarith only [hh]
  calc
    M^2 = (4*ρ*P)*(M*b/2) := by rw [hM]; ring
    _ ≤ (4*ρ*P)*(ρ*(2/Real.pi)*(b*sphereGap b)) := mul_le_mul_of_nonneg_left hmb (by positivity)
    _ ≤ (4*ρ*P)*(ρ*(2/Real.pi)*(428/10000)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu (by positivity)) (by positivity)
    _ = (963/2500)*P := by
      calc
        _ = (428/10000)*8*ρ^2/Real.pi*P := by ring
        _ = _ := by rw [hρsq]; field_simp; ring

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
open OneCell ProbabilityBounds Polar CapNumeric


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Cap.cone_four := @_root_.OAI.GaussianPropeller.Cap.cone_four
