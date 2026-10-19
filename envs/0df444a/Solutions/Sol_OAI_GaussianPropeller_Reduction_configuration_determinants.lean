-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.configuration_determinants
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:25:59.996535+00:00
-- url     : https://prove2.me/submissions/edcbe3dd-5f5b-414c-bd2c-fbc1bb5d29e9

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/FourReduction.lean:L160-L212
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.configuration_determinants. The node keeps its source
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
import Theorems.Thm_OAI_GaussianPropeller_Geometry_row_two_le

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

-- ---- from OAI.Probability.GaussianPropeller.Geometry ----
namespace OAI

universe uE uι

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

namespace GaussianPropeller.Geometry

open scoped RealInnerProductSpace

lemma pair_factor_le_eight {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c ≤ 1) :
    (1 + c)^2 * ((1 + a)^2 + (1 + b)^2) ≤ 8 := by
  have hc1 : c ≤ 1 := by linarith
  have hab : a + b ≤ 1 - c := by linarith
  have hab2 := (sq_le_sq₀ (by linarith : 0 ≤ a+b) (by linarith : 0 ≤ 1-c)).mpr hab
  have hu : (1+a)^2 + (1+b)^2 ≤ (2-c)^2 + 1 := by
    nlinarith only [hab, hab2, mul_nonneg ha hb]
  have hmul := mul_le_mul_of_nonneg_left hu (sq_nonneg (1+c))
  have hc2 := (sq_le_sq₀ hc (by norm_num : (0:ℝ) ≤ 1)).mpr hc1
  have hpos : 0 ≤ (1-c)^2 * (3-c^2) := mul_nonneg (sq_nonneg _) (by nlinarith)
  have hid : 8 - (1+c)^2 * ((2-c)^2+1) = (1-c)^2*(3-c^2) := by ring
  linarith only [hmul, hpos, hid]

lemma triple_factor_le_ten {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c ≤ 1) :
    (1+a)^2*(1+b)^2 + (1+a)^2*(1+c)^2 + (1+b)^2*(1+c)^2 ≤ 10 := by
  let s := a+b+c
  let p := a*b+a*c+b*c
  let q := a*b*c
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := hs
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hs2 : s^2 ≤ 1 := by nlinarith only [hs0, hs1, mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hps : 3*p ≤ s^2 := by
    dsimp [p,s]
    nlinarith only [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]
  have hp1 : p ≤ 1/3 := by linarith only [hps,hs2]
  have hsp : s*p ≤ 1/3 := (mul_le_mul_of_nonneg_right hs1 hp0).trans (by simpa using hp1)
  have hp2 : p^2 ≤ 1/9 := by
    have hh := (sq_le_sq₀ hp0 (by norm_num : (0:ℝ) ≤ 1/3)).mpr hp1
    norm_num at hh ⊢
    exact hh
  have hq : 0 ≤ (6+2*s)*q := mul_nonneg (by positivity) hq0
  have hid : (1+a)^2*(1+b)^2 + (1+a)^2*(1+c)^2 + (1+b)^2*(1+c)^2 =
      3+4*s+2*s^2+2*s*p+p^2-(6+2*s)*q := by dsimp [s,p,q]; ring
  rw [hid]
  linarith only [hs1, hs2, hsp, hp2, hq]

lemma row_determinants_lower {h₁ h₂ h₃ u v : ℝ}
    (hu : u ≤ 0) (hv : v ≤ 0) (hr : -u-v ≤ h₃) :
    h₃*(h₁+h₂-h₃) ≤ (h₃*h₁-u^2)+(h₃*h₂-v^2) := by
  have hp : 0 ≤ -u-v := by linarith
  have hh : 0 ≤ h₃ := hp.trans hr
  have hs := (sq_le_sq₀ hp hh).mpr hr
  nlinarith only [hs, mul_nonneg (neg_nonneg.mpr hu) (neg_nonneg.mpr hv)]

lemma three_correlations_lower {h₁ h₂ h₃ s ρ₁₂ ρ₁₃ ρ₂₃ : ℝ}
    (hs : 0 ≤ s) (hh₁ : s ≤ h₁) (hh₂ : s ≤ h₂) (hh₃ : s ≤ h₃)
    (h₁₂ : -1 ≤ ρ₁₂ ∧ ρ₁₂ ≤ 0) (h₁₃ : -1 ≤ ρ₁₃ ∧ ρ₁₃ ≤ 0)
    (h₂₃ : -1 ≤ ρ₂₃ ∧ ρ₂₃ ≤ 0) (hvar : 0 ≤ 3+2*(ρ₁₂+ρ₁₃+ρ₂₃)) :
    (3/2:ℝ)*s^2 ≤ h₁*h₂*(1-ρ₁₂^2)+h₁*h₃*(1-ρ₁₃^2)+h₂*h₃*(1-ρ₂₃^2) := by
  have hb {x : ℝ} (hx : -1 ≤ x ∧ x ≤ 0) : x^2 ≤ -x := by
    nlinarith only [mul_nonneg (by linarith only [hx.1] : 0 ≤ 1+x) (neg_nonneg.mpr hx.2)]
  have hv₁₂ : 0 ≤ 1-ρ₁₂^2 := by nlinarith only [hb h₁₂, h₁₂.1]
  have hv₁₃ : 0 ≤ 1-ρ₁₃^2 := by nlinarith only [hb h₁₃, h₁₃.1]
  have hv₂₃ : 0 ≤ 1-ρ₂₃^2 := by nlinarith only [hb h₂₃, h₂₃.1]
  have hsum : 3/2 ≤ (1-ρ₁₂^2)+(1-ρ₁₃^2)+(1-ρ₂₃^2) := by
    linarith only [hb h₁₂, hb h₁₃, hb h₂₃, hvar]
  have hprod {a b : ℝ} (ha : s ≤ a) (hb : s ≤ b) : s^2 ≤ a*b := by
    simpa only [pow_two] using mul_le_mul ha hb hs (hs.trans ha)
  calc
    (3/2:ℝ)*s^2 ≤ ((1-ρ₁₂^2)+(1-ρ₁₃^2)+(1-ρ₂₃^2))*s^2 :=
      mul_le_mul_of_nonneg_right hsum (sq_nonneg s)
    _ = s^2*(1-ρ₁₂^2)+s^2*(1-ρ₁₃^2)+s^2*(1-ρ₂₃^2) := by ring
    _ ≤ _ := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right (hprod hh₁ hh₂) hv₁₂)
      (mul_le_mul_of_nonneg_right (hprod hh₁ hh₃) hv₁₃))
      (mul_le_mul_of_nonneg_right (hprod hh₂ hh₃) hv₂₃)

section InnerProduct
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma unitVector_norm {w : E} (hw : w ≠ 0) : ‖unitVector w‖ = 1 := by
  simp [unitVector, norm_smul, norm_ne_zero_iff.mpr hw]

lemma unitVector_inner_cancel (u v : E) :
    ‖u‖ * ‖v‖ * ⟪unitVector u, unitVector v⟫ = ⟪u,v⟫ := by
  by_cases hu : u = 0
  · simp [hu, unitVector]
  by_cases hv : v = 0
  · simp [hv, unitVector]
  simp only [unitVector, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  field_simp [norm_ne_zero_iff.mpr hu, norm_ne_zero_iff.mpr hv]

lemma unitVector_inner_nonpos {u v : E} (h : ⟪u,v⟫ ≤ 0) :
    ⟪unitVector u, unitVector v⟫ ≤ 0 := by
  simp only [unitVector, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _))
    (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) h)

lemma unitVector_inner_bounds {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : ⟪u,v⟫ ≤ 0) :
    -1 ≤ ⟪unitVector u, unitVector v⟫ ∧ ⟪unitVector u, unitVector v⟫ ≤ 0 := by
  have hc := norm_inner_le_norm (𝕜 := ℝ) (unitVector u) (unitVector v)
  rw [unitVector_norm hu, unitVector_norm hv, mul_one, Real.norm_eq_abs] at hc
  exact ⟨(abs_le.mp hc).1, unitVector_inner_nonpos h⟩

lemma unitVector_variance (u v w : E) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    0 ≤ 3 + 2 * (⟪unitVector u, unitVector v⟫ + ⟪unitVector u, unitVector w⟫ +
      ⟪unitVector v, unitVector w⟫) := by
  have h := sq_nonneg ‖unitVector u + unitVector v + unitVector w‖
  rw [norm_add_sq_real, norm_add_sq_real, inner_add_left,
    unitVector_norm hu, unitVector_norm hv, unitVector_norm hw] at h
  nlinarith only [h]

lemma gram_det_unitVector (u v : E) :
    ‖u‖^2 * ‖v‖^2 * (1-⟪unitVector u, unitVector v⟫^2) =
      ‖u‖^2 * ‖v‖^2 - ⟪u,v⟫^2 := by
  calc
    _ = ‖u‖^2*‖v‖^2-(‖u‖*‖v‖*⟪unitVector u, unitVector v⟫)^2 := by ring
    _ = _ := by rw [unitVector_inner_cancel]

lemma three_gram_determinants_lower (u v w : E) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : ⟪u,v⟫ ≤ 0) (huw : ⟪u,w⟫ ≤ 0) (hvw : ⟪v,w⟫ ≤ 0)
    {s : ℝ} (hs : 0 ≤ s) (hsu : s ≤ ‖u‖^2) (hsv : s ≤ ‖v‖^2) (hsw : s ≤ ‖w‖^2) :
    (3/2:ℝ)*s^2 ≤ (‖u‖^2*‖v‖^2-⟪u,v⟫^2) + (‖u‖^2*‖w‖^2-⟪u,w⟫^2) +
      (‖v‖^2*‖w‖^2-⟪v,w⟫^2) := by
  have h := three_correlations_lower hs hsu hsv hsw
    (unitVector_inner_bounds hu hv huv) (unitVector_inner_bounds hu hw huw)
    (unitVector_inner_bounds hv hw hvw) (unitVector_variance u v w hu hv hw)
  simpa only [gram_det_unitVector] using h

lemma gram_det_nonneg (u v : E) : 0 ≤ ‖u‖^2*‖v‖^2-⟪u,v⟫^2 := by
  have h := real_inner_mul_inner_self_le u v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith only [h]

lemma first_constraint_of_pair_bounds (u v w : E) {t c L κ a b q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) (hsum : a+b+q ≤ 1)
    (hc : t^2 ≤ c) (hw : c-t^2 ≤ ‖w‖^2)
    (hdiag : L-c-2*t^2 ≤ ‖u‖^2+‖v‖^2-‖w‖^2)
    (hwu : ⟪w,u⟫ ≤ 0) (hwv : ⟪w,v⟫ ≤ 0)
    (hrow : -⟪w,u⟫-⟪w,v⟫ ≤ ‖w‖^2)
    (hpair₁ : ‖w‖^2*‖u‖^2-⟪w,u⟫^2 ≤ κ^2*t^2*(1+q)^2*(1+a)^2)
    (hpair₂ : ‖w‖^2*‖v‖^2-⟪w,v⟫^2 ≤ κ^2*t^2*(1+q)^2*(1+b)^2) :
    (c-t^2)*(L-c-2*t^2) ≤ 8*κ^2*t^2 := by
  have hlower : (c-t^2)*(L-c-2*t^2) ≤
      (‖w‖^2*‖u‖^2-⟪w,u⟫^2)+(‖w‖^2*‖v‖^2-⟪w,v⟫^2) := by
    by_cases hsign : 0 ≤ L-c-2*t^2
    · exact (mul_le_mul hw hdiag hsign (sq_nonneg ‖w‖)).trans
        (row_determinants_lower hwu hwv hrow)
    · exact (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hc) (le_of_not_ge hsign)).trans
        (add_nonneg (gram_det_nonneg w u) (gram_det_nonneg w v))
  have hu := mul_le_mul_of_nonneg_left (pair_factor_le_eight ha hb hq hsum)
    (mul_nonneg (sq_nonneg κ) (sq_nonneg t))
  nlinarith only [hlower, hpair₁, hpair₂, hu]

lemma second_constraint_of_pair_bounds (u v w : E)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) {t c κ a b q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) (hsum : a+b+q ≤ 1)
    (hc : t^2 ≤ c) (hsu : c-t^2 ≤ ‖u‖^2) (hsv : c-t^2 ≤ ‖v‖^2)
    (hsw : c-t^2 ≤ ‖w‖^2) (huv : ⟪u,v⟫ ≤ 0) (huw : ⟪u,w⟫ ≤ 0) (hvw : ⟪v,w⟫ ≤ 0)
    (hpair₁ : ‖u‖^2*‖v‖^2-⟪u,v⟫^2 ≤ κ^2*t^2*(1+a)^2*(1+b)^2)
    (hpair₂ : ‖u‖^2*‖w‖^2-⟪u,w⟫^2 ≤ κ^2*t^2*(1+a)^2*(1+q)^2)
    (hpair₃ : ‖v‖^2*‖w‖^2-⟪v,w⟫^2 ≤ κ^2*t^2*(1+b)^2*(1+q)^2) :
    (3/2:ℝ)*(c-t^2)^2 ≤ 10*κ^2*t^2 := by
  have hlow := three_gram_determinants_lower u v w hu hv hw huv huw hvw
    (sub_nonneg.mpr hc) hsu hsv hsw
  have hup := mul_le_mul_of_nonneg_left (triple_factor_le_ten ha hb hq hsum)
    (mul_nonneg (sq_nonneg κ) (sq_nonneg t))
  nlinarith only [hlow, hpair₁, hpair₂, hpair₃, hup]

end InnerProduct

end GaussianPropeller.Geometry

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

lemma residual_inner {z y v:Space d} (hz:z≠0) :
    ⟪residualVector z y,residualVector z v⟫ =
      ⟪y,v⟫-residualCoefficient z y*residualCoefficient z v*‖z‖^2 := by
  simp only [residualVector,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,real_inner_self_eq_norm_sq]
  rw [real_inner_comm z y,residual_inner_base hz (y:=y),residual_inner_base hz (y:=v)]
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

lemma residual_self (z:Space d) : residualVector z z=0 := by
  by_cases hz:z=0
  · simp [hz,residualVector,residualCoefficient]
  · have hn:‖z‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
    simp [residualVector,residualCoefficient,hn]

lemma residual_sum_all (z:Fin k→Space d) (hsum:∑ j,z j=0) (i:Fin k) (hi:z i≠0) :
    ∑ j,residualVector (z i) (z j)=0 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),residual_sum z hsum i hi,residual_self,add_zero]

lemma residual_obtuse (z:Fin k→Space d) (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0))
    (i:Fin k) (hi:z i≠0) {j l:Fin k} (hij:i≠j) (hil:i≠l) (hjl:j≠l) :
    ⟪residualVector (z i) (z j),residualVector (z i) (z l)⟫<0 := by
  rw [residual_inner hi]
  have ha:0<residualCoefficient (z i) (z j) := residualCoefficient_pos (hneg hij)
  have hb:0<residualCoefficient (z i) (z l) := residualCoefficient_pos (hneg hil)
  have hh : 0≤residualCoefficient (z i) (z j)*residualCoefficient (z i) (z l)*‖z i‖^2 := by positivity
  linarith only [hneg hjl,hh]

lemma residual_obtuse_all (z:Fin k→Space d) (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0))
    (i:Fin k) (hi:z i≠0) : ∀ j l, j≠l →
    ⟪residualVector (z i) (z j),residualVector (z i) (z l)⟫≤0 := by
  intro j l hjl
  by_cases hij:i=j
  · subst j; simp [residual_self]
  by_cases hil:i=l
  · subst l; simp [residual_self]
  exact (residual_obtuse z hneg i hi hij hil hjl).le

lemma residual_coefficients_three (z:Fin k→Space d) (hsum:∑ j,z j=0)
    (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0)) (i:Fin k) (hi:z i≠0)
    {j l q : Fin k} (hij:i≠j) (hil:i≠l) (hiq:i≠q) (hjl:j≠l) (hjq:j≠q) (hlq:l≠q) :
    residualCoefficient (z i) (z j)+residualCoefficient (z i) (z l)+
      residualCoefficient (z i) (z q)≤1 := by
  have hsub : ({j,l,q}:Finset (Fin k))⊆Finset.univ.erase i := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl <;> simp [Ne.symm hij,Ne.symm hil,Ne.symm hiq]
  have h:=Finset.sum_le_sum_of_subset_of_nonneg hsub (f:=fun a=>residualCoefficient (z i) (z a))
    (fun a ha _ => (residualCoefficient_pos (hneg (Finset.mem_erase.mp ha).1.symm)).le)
  rw [residual_coefficient_sum z hsum i hi] at h
  simpa [Finset.sum_insert,Finset.sum_singleton,hjl,hjq,hlq,add_assoc] using h

lemma configuration_determinants (z:Fin k→Space d) (hsum:∑ j,z j=0)
    (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0)) (i:Fin k) (hi:z i≠0)
    {j l q : Fin k} (hij:i≠j) (hil:i≠l) (hiq:i≠q) (hjl:j≠l) (hjq:j≠q) (hlq:l≠q)
    (hj:‖z q‖≤‖z j‖) (hl:‖z q‖≤‖z l‖) (hmin:‖z i‖≤‖z q‖)
    (hpair:∀ a b, i≠a → i≠b →
      ‖residualVector (z i) (z a)‖^2*‖residualVector (z i) (z b)‖^2-
      ⟪residualVector (z i) (z a),residualVector (z i) (z b)⟫^2≤
      (3/Real.pi)^2*‖z i‖^2*(1+residualCoefficient (z i) (z a))^2*
      (1+residualCoefficient (z i) (z b))^2) :
    (‖z q‖^2-‖z i‖^2)*(‖z j‖^2+‖z l‖^2-‖z q‖^2-2*‖z i‖^2)≤
      8*(3/Real.pi)^2*‖z i‖^2 ∧
    (3/2:ℝ)*(‖z q‖^2-‖z i‖^2)^2≤10*(3/Real.pi)^2*‖z i‖^2 := by
  let a:=residualCoefficient (z i) (z j)
  let b:=residualCoefficient (z i) (z l)
  let c:=residualCoefficient (z i) (z q)
  let u:=residualVector (z i) (z j)
  let v:=residualVector (z i) (z l)
  let w:=residualVector (z i) (z q)
  have ha:0<a := residualCoefficient_pos (hneg hij)
  have hb:0<b := residualCoefficient_pos (hneg hil)
  have hc:0<c := residualCoefficient_pos (hneg hiq)
  have hs:a+b+c≤1 := residual_coefficients_three z hsum hneg i hi hij hil hiq hjl hjq hlq
  have ha1:a^2≤1 := by nlinarith only [ha,hb,hc,hs]
  have hb1:b^2≤1 := by nlinarith only [ha,hb,hc,hs]
  have hc1:c^2≤1 := by nlinarith only [ha,hb,hc,hs]
  have hu:‖u‖^2=‖z j‖^2-a^2*‖z i‖^2 := residual_norm_sq hi
  have hv:‖v‖^2=‖z l‖^2-b^2*‖z i‖^2 := residual_norm_sq hi
  have hw:‖w‖^2=‖z q‖^2-c^2*‖z i‖^2 := residual_norm_sq hi
  have ht:‖z i‖^2≤‖z q‖^2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hmin
  have hrj:‖z q‖^2≤‖z j‖^2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hj
  have hrl:‖z q‖^2≤‖z l‖^2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hl
  have hla:=mul_le_mul_of_nonneg_right ha1 (sq_nonneg ‖z i‖)
  have hlb:=mul_le_mul_of_nonneg_right hb1 (sq_nonneg ‖z i‖)
  have hlc:=mul_le_mul_of_nonneg_right hc1 (sq_nonneg ‖z i‖)
  have hlu:‖z q‖^2-‖z i‖^2≤‖u‖^2 := by nlinarith only [hu,hla,hrj]
  have hlv:‖z q‖^2-‖z i‖^2≤‖v‖^2 := by nlinarith only [hv,hlb,hrl]
  have hlw:‖z q‖^2-‖z i‖^2≤‖w‖^2 := by nlinarith only [hw,hlc]
  have huw:⟪u,w⟫<0 := residual_obtuse z hneg i hi hij hiq hjq
  have hvw:⟪v,w⟫<0 := residual_obtuse z hneg i hi hil hiq hlq
  have huv:⟪u,v⟫<0 := residual_obtuse z hneg i hi hij hil hjl
  have hwu:⟪w,u⟫≤0 := by rw [real_inner_comm u w]; exact huw.le
  have hwv:⟪w,v⟫≤0 := by rw [real_inner_comm v w]; exact hvw.le
  have hrow := Geometry.row_two_le (fun a=>residualVector (z i) (z a))
    (residual_sum_all z hsum i hi) (residual_obtuse_all z hneg i hi) hjq.symm hlq.symm hjl
  constructor
  · exact Geometry.first_constraint_of_pair_bounds u v w ha.le hb.le hc.le hs ht hlw
      (by nlinarith only [hu,hv,hw,hla,hlb,mul_nonneg (sq_nonneg c) (sq_nonneg ‖z i‖)])
      hwu hwv hrow (hpair q j hiq hij) (hpair q l hiq hil)
  · have hu0:u≠0 := by intro he; rw [he,inner_zero_left] at huv; exact (lt_irrefl _ huv)
    have hv0:v≠0 := by intro he; rw [he,inner_zero_right] at huv; exact (lt_irrefl _ huv)
    have hw0:w≠0 := by intro he; rw [he,inner_zero_right] at huw; exact (lt_irrefl _ huw)
    exact Geometry.second_constraint_of_pair_bounds u v w hu0 hv0 hw0 ha.le hb.le hc.le hs
      ht hlu hlv hlw huv.le huw.le hvw.le (hpair j l hij hil) (hpair j q hij hiq) (hpair l q hil hiq)

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


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.configuration_determinants := @_root_.OAI.GaussianPropeller.Reduction.configuration_determinants
