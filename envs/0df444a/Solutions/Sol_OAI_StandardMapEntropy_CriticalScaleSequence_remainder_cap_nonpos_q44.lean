-- Prove2me | solution 1 for OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_nonpos_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:30:06.15661+00:00
-- url     : https://prove2.me/submissions/fc09446d-648e-4706-8947-2a5b117cd55a

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_capG_integrable_remainder_q44
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_dilation_balance_q44
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_noCancellation_aemulti_q44
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_remainder_left_ray_zero_q44
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_remainder_right_ray_zero_q44
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_remainder_shape_q44
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_remainder_translate_q44
import Theorems.Thm_OAI_StandardMapEntropy_bandMoment_order_q44
import Theorems.Thm_OAI_StandardMapEntropy_band_coboundary_q44

section
-- module Solutions.OAIQ44_CM.StandardMap_PlaneGeometry
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma abs_dot_le_norm_mul (z w : ℂ) : |dot z w| ≤ ‖z‖*‖w‖ := by
  have h := dot_wedge_sq z w
  have h0 := sq_nonneg (wedge z w)
  have hs : (dot z w)^2 ≤ (‖z‖*‖w‖)^2 := by nlinarith
  exact (abs_le_of_sq_le_sq hs (mul_nonneg (norm_nonneg z) (norm_nonneg w)))
lemma abs_wedge_le_norm_mul (z w : ℂ) : |wedge z w| ≤ ‖z‖*‖w‖ := by
  have h := dot_wedge_sq z w
  have hs : (wedge z w)^2 ≤ (‖z‖*‖w‖)^2 := by nlinarith [sq_nonneg (dot z w)]
  exact (abs_le_of_sq_le_sq hs (mul_nonneg (norm_nonneg z) (norm_nonneg w)))
lemma wedge_add_left (z w a : ℂ) : wedge (z+w) a = wedge z a + wedge w a := by
  simp [wedge]; ring
lemma wedge_smul_left (t : ℝ) (z w : ℂ) : wedge (t • z) w = t*wedge z w := by
  simp [wedge]; ring
lemma wedge_swap (z w : ℂ) : wedge z w = -wedge w z := by dsimp [wedge]; ring
lemma wedge_sine_triangle (a b c : ℂ) (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1) :
    |wedge a c| ≤ |wedge a b|+|wedge b c| := by
  have he : wedge a c = dot b a * wedge b c + wedge b a * wedge (quarterTurn b) c := by
    conv_lhs => rw [unit_expansion b a hb]
    rw [wedge_add_left, wedge_smul_left, wedge_smul_left]
  rw [he]
  calc
    _ ≤ |dot b a| * |wedge b c|+|wedge b a| * |wedge (quarterTurn b) c| := by
      simpa only [abs_mul] using abs_add_le (dot b a * wedge b c) (wedge b a * wedge (quarterTurn b) c)
    _ ≤ |wedge b c|+|wedge b a| := by
      have h1 : |dot b a|≤1 := by simpa [ha,hb] using abs_dot_le_norm_mul b a
      have h2 : |wedge (quarterTurn b) c|≤1 := by simpa [norm_quarterTurn,hb,hc] using abs_wedge_le_norm_mul (quarterTurn b) c
      nlinarith [abs_nonneg (wedge b c), abs_nonneg (wedge b a)]
    _ = _ := by rw [wedge_swap b a, abs_neg]; ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_PlaneTransfer
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma dot_quarterTurn_right (a z : ℂ) : dot a (quarterTurn z) = -wedge a z := by
  simp [dot,wedge,quarterTurn]; ring
lemma PlaneAreaPreserving.norm_le_product {A B C : ℂ →L[ℝ] ℂ}
    (_hB : PlaneAreaPreserving B) (hBC : ∀ z, C (B z)=A z) : ‖A‖≤‖C‖*‖B‖ := by
  have he : A=C.comp B := by ext z; exact (hBC z).symm
  rw [he]
  exact C.opNorm_comp_le B
lemma expanded_projection_bound {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A)
    (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) (z : ℂ) :
    ‖A‖*|dot a z| ≤ ‖A z‖ := by
  have hs := h.norm_map_sq a ha hA z
  have hnon := mul_nonneg (sq_nonneg (wedge a z)) (sq_nonneg (‖A‖⁻¹))
  have hsq : (‖A‖*|dot a z|)^2≤‖A z‖^2 := by nlinarith [sq_abs (dot a z)]
  exact (sq_le_sq₀ (mul_nonneg (norm_nonneg A) (abs_nonneg _)) (norm_nonneg _)).mp hsq
lemma two_singular_upper {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A)
    (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) (z : ℂ) :
    ‖A z‖ ≤ ‖A‖*|dot a z| + ‖A‖⁻¹*|wedge a z| := by
  have hd := orthogonal_image_of_max A a ha hA
  have hs := h.norm_map_sq a ha hA (quarterTurn a)
  rw [dot_quarterTurn,wedge_quarterTurn,ha] at hs
  have hb : ‖A (quarterTurn a)‖=‖A‖⁻¹ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))).mp
    simpa using hs
  conv_lhs => rw [unit_expansion a z ha]
  rw [map_add,map_smul,map_smul]
  calc
    _ ≤ ‖(dot a z : ℝ) • A a‖+‖(wedge a z : ℝ) • A (quarterTurn a)‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,hA,hb]; ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_FourPoint
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma PlaneAreaPreserving.injective {A : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A) :
    Function.Injective A := by
  intro x y hxy
  have hh:=hA.norm_lower (x-y)
  rw [map_sub,hxy,sub_self,norm_zero,mul_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
lemma PlaneAreaPreserving.surjective {A : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A) :
    Function.Surjective A := LinearMap.surjective_of_injective (f := A.toLinearMap) hA.injective

lemma transfer_angle_bounds {A B C : ℂ →L[ℝ] ℂ}
    (hA : PlaneAreaPreserving A) (hB : PlaneAreaPreserving B) (hC : PlaneAreaPreserving C)
    (he : ∀ z, C (B z)=A z)
    (a b : ℂ) (ha : ‖a‖=1) (hb : ‖b‖=1) (hAa : ‖A a‖=‖A‖) (hBb : ‖B b‖=‖B‖) :
    max |wedge a b| (max (‖A‖⁻¹^2) (‖B‖⁻¹^2)) ≤ ‖C‖/(‖A‖*‖B‖) ∧
    ‖C‖/(‖A‖*‖B‖) ≤ |wedge a b|+‖A‖⁻¹^2+‖B‖⁻¹^2 := by
  have hDA : 1 ≤ ‖A‖ := hA.singular_pair.choose_spec.2.2.2.2
  have hDB : 1 ≤ ‖B‖ := hB.singular_pair.choose_spec.2.2.2.2
  have hAp : 0 < ‖A‖ := by linarith
  have hBp : 0 < ‖B‖ := by linarith
  have hbperp : ‖B (quarterTurn b)‖=‖B‖⁻¹ := by
    have hs:=hB.norm_map_sq b hb hBb (quarterTurn b)
    rw [dot_quarterTurn,wedge_quarterTurn,hb] at hs
    apply (sq_eq_sq₀ (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))).mp
    simpa using hs
  have angle : ‖A‖*|wedge a b| ≤ ‖C‖*‖B‖⁻¹ := by
    have hh:=expanded_projection_bound hA a ha hAa (quarterTurn b)
    rw [dot_quarterTurn_right,abs_neg,← he] at hh
    exact hh.trans (by simpa [hbperp] using C.le_opNorm (B (quarterTurn b)))
  have normAB : ‖A‖ ≤ ‖C‖*‖B‖ := hB.norm_le_product he
  have normBA : ‖B‖ ≤ ‖C‖*‖A‖ := by
    apply B.opNorm_le_bound (by positivity)
    intro z
    have hh:=hC.norm_lower (B z)
    rw [he] at hh
    calc
      _ ≤ ‖C‖*‖A z‖ := hh
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (A.le_opNorm z) (norm_nonneg C)
  have upper : ‖C‖ ≤ ‖A‖/‖B‖+‖A‖*‖B‖*|wedge a b|+‖B‖/‖A‖ := by
    apply C.opNorm_le_bound (by positivity)
    intro z
    obtain ⟨y,rfl⟩:=hB.surjective z
    rw [he]
    have hdot : |dot b y| ≤ ‖B y‖/‖B‖ := by
      apply (le_div_iff₀ hBp).mpr
      simpa [mul_comm] using expanded_projection_bound hB b hb hBb y
    have hwedge : |wedge b y| ≤ ‖B‖*‖B y‖ := by
      have hh : |wedge b y| ≤ ‖y‖ := by simpa only [hb,one_mul] using abs_wedge_le_norm_mul b y
      exact hh.trans (hB.norm_lower y)
    have hwb : |wedge a (quarterTurn b)| ≤ 1 := by
      simpa [ha,hb,norm_quarterTurn] using abs_wedge_le_norm_mul a (quarterTurn b)
    have hAperp : ‖A (quarterTurn b)‖ ≤ ‖A‖*|wedge a b|+‖A‖⁻¹ := by
      have hh:=two_singular_upper hA a ha hAa (quarterTurn b)
      rw [dot_quarterTurn_right,abs_neg] at hh
      exact hh.trans (add_le_add_right (by simpa using mul_le_mul_of_nonneg_left hwb (inv_nonneg.mpr (norm_nonneg A))) _)
    calc
      ‖A y‖ = ‖dot b y • A b+wedge b y • A (quarterTurn b)‖ := by
        conv_lhs => rw [unit_expansion b y hb]
        rw [map_add,map_smul,map_smul]
      _ ≤ |dot b y| *‖A b‖+|wedge b y| *‖A (quarterTurn b)‖ := by
        simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le (dot b y • A b) (wedge b y • A (quarterTurn b))
      _ ≤ (‖B y‖/‖B‖)*‖A‖+(‖B‖*‖B y‖)*(‖A‖*|wedge a b|+‖A‖⁻¹) := by
        gcongr
        simpa [hb] using A.le_opNorm b
      _ = _ := by ring
  constructor
  · apply max_le
    · apply (le_div_iff₀ (mul_pos hAp hBp)).mpr
      have hh:=mul_le_mul_of_nonneg_right angle hBp.le
      simp only [mul_assoc,inv_mul_cancel₀ hBp.ne',mul_one] at hh
      nlinarith only [hh]
    · apply max_le
      · apply (le_div_iff₀ (mul_pos hAp hBp)).mpr
        apply (mul_le_mul_iff_right₀ hAp).mp
        calc
          _ = ‖B‖ := by field_simp [hAp.ne',hBp.ne']
          _ ≤ _ := by simpa only [mul_comm] using normBA
      · apply (le_div_iff₀ (mul_pos hAp hBp)).mpr
        apply (mul_le_mul_iff_right₀ hBp).mp
        calc
          _ = ‖A‖ := by field_simp [hAp.ne',hBp.ne']
          _ ≤ _ := by simpa only [mul_comm] using normAB
  · apply (div_le_iff₀ (mul_pos hAp hBp)).mpr
    calc
      _ ≤ _ := upper
      _ = _ := by field_simp [hAp.ne',hBp.ne']; ring

lemma normalized_transfer_fourpoint {ι : Type*}
    (A : ι → (ℂ →L[ℝ] ℂ)) (T : ι → ι → (ℂ →L[ℝ] ℂ))
    (hA : ∀ i, PlaneAreaPreserving (A i)) (hT : ∀ i j, PlaneAreaPreserving (T i j))
    (hcomp : ∀ i j z, T i j (A j z)=A i z) (j l p : ι) :
    ‖T j p‖/(‖A j‖*‖A p‖) ≤
      6*max (‖T j l‖/(‖A j‖*‖A l‖)) (‖T l p‖/(‖A l‖*‖A p‖)) := by
  choose a ha hnorm horth hperp hD using fun i => (hA i).singular_pair
  have hs (i q : ι) := transfer_angle_bounds (hA i) (hA q) (hT i q)
    (hcomp i q) (a i) (a q) (ha i) (ha q) (hnorm i) (hnorm q)
  have hjl:=hs j l
  have hlp:=hs l p
  have hjp:=hs j p
  have hangle:=wedge_sine_triangle (a j) (a l) (a p) (ha j) (ha l) (ha p)
  have hj : ‖A j‖⁻¹^2 ≤ ‖T j l‖/(‖A j‖*‖A l‖) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hjl.1)
  have hp : ‖A p‖⁻¹^2 ≤ ‖T l p‖/(‖A l‖*‖A p‖) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlp.1)
  have ha1 : |wedge (a j) (a l)| ≤ ‖T j l‖/(‖A j‖*‖A l‖) := (le_max_left _ _).trans hjl.1
  have ha2 : |wedge (a l) (a p)| ≤ ‖T l p‖/(‖A l‖*‖A p‖) := (le_max_left _ _).trans hlp.1
  have hm1 := le_max_left (‖T j l‖/(‖A j‖*‖A l‖)) (‖T l p‖/(‖A l‖*‖A p‖))
  have hm2 := le_max_right (‖T j l‖/(‖A j‖*‖A l‖)) (‖T l p‖/(‖A l‖*‖A p‖))
  have hnon : 0 ≤ max (‖T j l‖/(‖A j‖*‖A l‖)) (‖T l p‖/(‖A l‖*‖A p‖)) := by positivity
  linarith [hjp.2]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ProductDistances
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma transfer_distance_fourpoint (k : ℝ) (hk : 0≤k) (z : Torus) (i j l p : ℤ) :
    productDistance k z j p-productDistance k z i j-productDistance k z i p ≤
      max (productDistance k z j l-productDistance k z i j-productDistance k z i l)
        (productDistance k z l p-productDistance k z i l-productDistance k z i p)+
        Real.log 6/Real.log (growthBase k) := by
  let A := fun j => (torusTransfer k z i j).toContinuousLinearMap
  let T := fun j p => (torusTransfer k z p j).toContinuousLinearMap
  let R := fun j p => ‖T j p‖/(‖A j‖*‖A p‖)
  have hR : ∀ j p, 0<R j p := fun j p => div_pos (torusTransfer_norm_pos k z p j)
    (mul_pos (torusTransfer_norm_pos k z i j) (torusTransfer_norm_pos k z i p))
  have hc := normalized_transfer_fourpoint A T (fun j => torusTransfer_area k z i j)
    (fun j p => torusTransfer_area k z p j) (fun j p u => torusTransfer_comp k z i p j u) j l p
  change R j p≤6*max (R j l) (R l p) at hc
  have he (j p : ℤ) : Real.log (R j p)/Real.log (growthBase k)=
      productDistance k z j p-productDistance k z i j-productDistance k z i p := by
    dsimp only [R,A,T]
    rw [Real.log_div (torusTransfer_norm_pos k z p j).ne'
      (mul_pos (torusTransfer_norm_pos k z i j) (torusTransfer_norm_pos k z i p)).ne',
      Real.log_mul (torusTransfer_norm_pos k z i j).ne' (torusTransfer_norm_pos k z i p).ne',
      torusTransfer_norm_symm k z p j]
    unfold productDistance; ring
  have hm : Real.log (max (R j l) (R l p))=max (Real.log (R j l)) (Real.log (R l p)) := by
    rcases le_total (R j l) (R l p) with h | h
    · rw [max_eq_right h,max_eq_right (Real.log_le_log (hR j l) h)]
    · rw [max_eq_left h,max_eq_left (Real.log_le_log (hR l p) h)]
  have hlog := Real.log_le_log (hR j p) hc
  rw [Real.log_mul (by norm_num : (6:ℝ)≠0) (lt_of_lt_of_le (hR j l) (le_max_left _ _)).ne',hm] at hlog
  have hd := div_le_div_of_nonneg_right hlog (log_growthBase_pos k hk).le
  rw [add_div,← max_div_div_right (log_growthBase_pos k hk).le,he,he,he] at hd
  linarith
lemma log_six_div_growth_le_three (k : ℝ) (hk : 0≤k) : Real.log 6/Real.log (growthBase k)≤3 := by
  apply (div_le_iff₀ (log_growthBase_pos k hk)).mpr
  have hh := Real.log_le_log (by norm_num : (0:ℝ)<6)
    (show (6:ℝ)≤growthBase k^3 by
      have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4) (growthBase_ge_four k hk) 3
      norm_num at hp ⊢; linarith)
  simpa only [Real.log_pow,Nat.cast_ofNat] using hh

lemma productDistance_tree (k : ℝ) (hk : 0≤k) (z : Torus) (i j l p : ℤ) :
    min (productDistance k z i j+productDistance k z i l-productDistance k z j l)
        (productDistance k z i l+productDistance k z i p-productDistance k z l p)-3 ≤
      productDistance k z i j+productDistance k z i p-productDistance k z j p := by
  have hh := transfer_distance_fourpoint k hk z i j l p
  have he := log_six_div_growth_le_three k hk
  rcases le_total (productDistance k z i j+productDistance k z i l-productDistance k z j l)
      (productDistance k z i l+productDistance k z i p-productDistance k z l p) with h | h
  · rw [min_eq_left h]
    rw [max_eq_left (by linarith)] at hh
    linarith
  · rw [min_eq_right h]
    rw [max_eq_right (by linarith)] at hh
    linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_SmoothCap
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Interval Topology
namespace StandardMapEntropy
lemma capSlope_contDiff : ContDiff ℝ 2 capSlope := by unfold capSlope; fun_prop
lemma capSlope_continuous : Continuous capSlope := capSlope_contDiff.continuous
lemma capSlope_zero {u : ℝ} (hu : 1/5000≤ u) : capSlope u=0 := by
  unfold capSlope
  rw [Real.smoothTransition.one_of_one_le (by linarith)]; ring
lemma capPrimitive_constant {u : ℝ} (hu : 1/5000≤ u) : capPrimitive u=capBase := by
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (capSlope_continuous.intervalIntegrable 0 (1/5000)) (capSlope_continuous.intervalIntegrable (1/5000) u)
  have hzero : (∫ t in (1/5000:ℝ)..u,capSlope t)=0 := by
    calc
      (∫ t in (1/5000:ℝ)..u,capSlope t)=(∫ _t in (1/5000:ℝ)..u,(0:ℝ)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact capSlope_zero (by rw [uIcc_of_le hu] at ht; exact ht.1)
      _=0 := by simp
  rw [hzero,add_zero] at he
  exact he.symm
lemma entropyCap_one {α u : ℝ} (hu : 3/10000≤ u) : entropyCap α u=1 := by
  unfold entropyCap
  rw [capPrimitive_constant (by linarith),Real.smoothTransition.one_of_one_le (by linarith)]
  ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CriticalSequence
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Filter Set
open scoped Topology Classical
namespace StandardMapEntropy
lemma criticalTheta_pos (r i : ℕ) : 0 < criticalTheta r i := by unfold criticalTheta; positivity
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence)
lemma epsilon_pos (i : ℕ) : 0 < S.epsilon i := (criticalTheta_pos S.offset i).trans (S.threshold i)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RescaledArrays
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma continuous_sampleArray (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) : Continuous (fun z => sampleArray k hk z n hn) := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro s
  apply continuous_pi; intro t
  exact (continuous_productDistance k hk _ _).div_const _
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_SampleLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
instance sampleLawProbability (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) :
    IsProbabilityMeasure (sampleLaw k hk n hn) := by
  unfold sampleLaw
  exact (Measure.isProbabilityMeasure_map_iff (continuous_sampleArray k hk n hn).measurable.aemeasurable).2 inferInstance
lemma integral_sampleLaw (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) (F : DistanceArray → ℝ)
    (hF : Continuous F) :
    (∫ d,F d ∂sampleLaw k hk n hn)=∫ z,F (sampleArray k hk z n hn) ∂area :=
  integral_map_of_stronglyMeasurable (continuous_sampleArray k hk n hn).measurable hF.stronglyMeasurable
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ScaleLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable instance scaleLawFinite (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) :
    IsFiniteMeasure (scaleLaw k hk p l ε) := by
  unfold scaleLaw
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top
lemma integral_scaleLaw (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) (hε : 0<ε)
    (F : DistanceArray → ℝ) (hF : Continuous F) :
    (∫ d,F d ∂scaleLaw k hk p l ε)=(∑ i∈Finset.range l,∫ d,F d ∂sampleLaw k hk (2^(p+i)) (by positivity))/ε := by
  rw [scaleLaw,integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0≤1/ε)]
  rw [integral_finsetSum_measure]
  · simp only [smul_eq_mul]; ring
  · intro i hi
    exact hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CriticalLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence)
instance initialLaw_finite (i : ℕ) : IsFiniteMeasure (S.initialLaw i) := inferInstanceAs (IsFiniteMeasure (scaleLaw _ _ _ _ _))
instance terminalLaw_finite (i : ℕ) : IsFiniteMeasure (S.terminalLaw i) := inferInstanceAs (IsFiniteMeasure (scaleLaw _ _ _ _ _))
instance multiLaw_finite (i : ℕ) : IsFiniteMeasure (S.multiLaw i) := inferInstanceAs (IsFiniteMeasure (scaleLaw _ _ _ _ _))
lemma lowerExponent_tendsto : Tendsto (criticalLowerExponent S.offset) atTop atTop := by
  apply tendsto_atTop_mono (f := fun i : ℕ => i) _ tendsto_id
  intro i
  unfold criticalLowerExponent
  omega
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayActions
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma arrayTestExtend_affine (g : C_c(NonAffineArray,ℝ)) (d : DistanceArray) (hd : d∈affineLocus) :
    arrayTestExtend g d=0 := by
  apply Function.extend_apply' _ _ _
  rintro ⟨u,rfl⟩
  exact u.property hd
lemma integral_arrayTestExtend (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (g : C_c(NonAffineArray,ℝ)) : (∫ d,arrayTestExtend g d ∂μ)=∫ d,g d ∂nonaffinePart μ := by
  have he : (∫ d,g d ∂nonaffinePart μ)=∫ d in affineLocusᶜ,arrayTestExtend g d ∂μ := by
    convert! integral_subtype_comap isClosed_affineLocus.isOpen_compl.measurableSet (arrayTestExtend g) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [arrayTestExtend_apply]
    rfl
  rw [he]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro d hd
  exact arrayTestExtend_affine g d (not_not.mp hd)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_VagueSupport
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma open_null_of_integral_zero {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [RegularSpace X]
    (μ : Measure X) [μ.Regular] {U : Set X} (hU : IsOpen U)
    (hzero : ∀ g : C_c(X,ℝ), (∀ x,0 ≤ g x) → (∀ x∉U,g x=0) → ∫ x,g x ∂μ=0) : μ U=0 := by
  rw [hU.measure_eq_iSup_isCompact μ]
  apply le_antisymm _ bot_le
  simp only [iSup_le_iff]
  intro K hKU hK
  obtain ⟨⟨f,hfc⟩,hfK,hfU,hfs,hfr⟩ := exists_continuous_one_zero_of_isCompact
    hK hU.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKU)
  let g : C_c(X,ℝ) := ⟨⟨f,hfc⟩,hfs⟩
  have hint := hzero g (fun x => (hfr x).1) (fun x hx => hfU hx)
  have hb := (hfc.integrable_of_hasCompactSupport hfs (μ := μ)).measure_le_integral
    (Eventually.of_forall fun x => (hfr x).1) (fun x hx => (hfK hx).ge)
  change μ K ≤ ENNReal.ofReal (∫ x,g x ∂μ) at hb
  rw [hint,ENNReal.ofReal_zero] at hb
  convert! hb using 1
  all_goals try with_reducible_and_instances rfl
lemma vague_open_null {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [RegularSpace X]
    (l : Filter ι) [l.NeBot] (μ : ι → Measure X) (ν : Measure X) [ν.Regular]
    (hconv : ∀ g : C_c(X,ℝ), Tendsto (fun i => ∫ x,g x ∂μ i) l (𝓝 (∫ x,g x ∂ν)))
    {U : Set X} (hU : IsOpen U)
    (hzero : ∀ g : C_c(X,ℝ), (∀ x,0 ≤ g x) → (∀ x∉U,g x=0) →
      Tendsto (fun i => ∫ x,g x ∂μ i) l (𝓝 0)) : ν U=0 := by
  apply open_null_of_integral_zero ν hU
  intro g hg hz
  exact tendsto_nhds_unique (hconv g) (hzero g hg hz)
lemma ae_le_zero_of_positive_rational_null {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hn : ∀ q : ℚ,0<q → μ {x | (q:ℝ)<f x}=0) : ∀ᵐ x ∂μ, f x ≤ 0 := by
  have hh : ∀ q : ℚ,0<q → ∀ᵐ x ∂μ,¬(q:ℝ)<f x := fun q hq => ae_iff.mpr (by simpa using hn q hq)
  have h := ae_all_iff.mpr (fun q : ℚ => ae_all_iff.mpr (hh q))
  filter_upwards [h] with x hx
  by_contra hpos
  obtain ⟨q,hq,hqx⟩ := exists_rat_btwn (lt_of_not_ge hpos)
  exact hx q (by exact_mod_cast hq) hqx
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RealArrays
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma unitArray_diff (d : DistanceArray) (hd : UnitArray d) (s t u v : DyadicTime) :
    |d.val s t-d.val u v| ≤ |(s:ℝ)-(u:ℝ)|+|(t:ℝ)-(v:ℝ)| := by
  have ht := d.property.2.2.2.1
  have hsy := d.property.2.2.1
  have h1 := ht s u t
  have h2 := ht u v t
  have h3 := ht u s v
  have h4 := ht s t v
  have hsu := hd s u
  have htv := hd t v
  rw [abs_sub_comm] at hsu htv
  have hste : d.val u s=d.val s u := hsy _ _
  have hvte : d.val v t=d.val t v := hsy _ _
  rw [abs_le]
  constructor <;> linarith
lemma unitArray_lipschitz (d : DistanceArray) (hd : UnitArray d) :
    LipschitzWith 2 (fun p : DyadicTime × DyadicTime => d.val p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h := unitArray_diff d hd p.1 p.2 q.1 q.2
  rw [Real.dist_eq,Prod.dist_eq]
  change |d.val p.1 p.2-d.val q.1 q.2| ≤ (2:ℝ)*max |(p.1:ℝ)-(q.1:ℝ)| |(p.2:ℝ)-(q.2:ℝ)|
  linarith [le_max_left |(p.1:ℝ)-(q.1:ℝ)| |(p.2:ℝ)-(q.2:ℝ)|,
    le_max_right |(p.1:ℝ)-(q.1:ℝ)| |(p.2:ℝ)-(q.2:ℝ)|]
@[simp] lemma realArray_coe (d : DistanceArray) (hd : UnitArray d) (s t : DyadicTime) :
    realArray d (s:ℝ) (t:ℝ)=d.val s t :=
  uniformly_extend_of_ind
    ((isUniformInducing_val (dyadicTimes:Set ℝ)).prod (isUniformInducing_val (dyadicTimes:Set ℝ)))
    (denseRange_dyadicTime.prodMap denseRange_dyadicTime) (unitArray_lipschitz d hd).uniformContinuous (s,t)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayLimitSupport
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma rescaledDistance_tree (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) (hn : 0<n)
    (v x y w : DyadicTime) :
    min (rescaledDistance k z n v x+rescaledDistance k z n v y-rescaledDistance k z n x y)
      (rescaledDistance k z n v y+rescaledDistance k z n v w-rescaledDistance k z n y w)-
      (rescaledDistance k z n v x+rescaledDistance k z n v w-rescaledDistance k z n x w) ≤ 3/(n:ℝ) := by
  have hh := productDistance_tree k hk z ⌊(n:ℝ)*(v:ℝ)⌋ ⌊(n:ℝ)*(x:ℝ)⌋ ⌊(n:ℝ)*(y:ℝ)⌋ ⌊(n:ℝ)*(w:ℝ)⌋
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  unfold rescaledDistance
  simp_rw [← add_div,← sub_div]
  rw [min_div_div_right hn'.le,← sub_div]
  exact div_le_div_of_nonneg_right (by linarith) hn'.le
lemma integral_nonaffine_scale_zero (k : ℝ) (hk : 0 ≤ k) (p l : ℕ) (ε : ℝ) (hε : 0<ε)
    (g : C_c(NonAffineArray,ℝ))
    (hz : ∀ j∈Finset.range l,∀ z,arrayTestExtend g (sampleArray k hk z (2^(p+j)) (by positivity))=0) :
    (∫ d,g d ∂nonaffinePart (scaleLaw k hk p l ε))=0 := by
  rw [←integral_arrayTestExtend,integral_scaleLaw k hk p l ε hε (fun d => arrayTestExtend g d) (arrayTestExtend g).continuous]
  have hs : (∑ j∈Finset.range l,∫ d,arrayTestExtend g d ∂sampleLaw k hk (2^(p+j)) (by positivity))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [integral_sampleLaw _ _ _ _ (fun d => arrayTestExtend g d) (arrayTestExtend g).continuous]
    simp_rw [hz j hj]
    simp
  rw [hs,zero_div]
lemma integral_nonaffine_scale_zero_of_bound (k : ℝ) (hk : 0 ≤ k) (p l : ℕ) (ε : ℝ) (hε : 0<ε)
    (g : C_c(NonAffineArray,ℝ)) (f : DistanceArray → ℝ) (q : ℝ)
    (hg : ∀ d : NonAffineArray, f d.val ≤ q → g d=0)
    (hf : ∀ j∈Finset.range l,∀ z,f (sampleArray k hk z (2^(p+j)) (by positivity)) ≤ q) :
    (∫ d,g d ∂nonaffinePart (scaleLaw k hk p l ε))=0 := by
  apply integral_nonaffine_scale_zero k hk p l ε hε g
  intro j hj z
  let d := sampleArray k hk z (2^(p+j)) (by positivity)
  by_cases hd : d∈affineLocus
  · exact arrayTestExtend_affine g d hd
  · exact (arrayTestExtend_apply g ⟨d,hd⟩).trans (hg ⟨d,hd⟩ (hf j hj z))
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma power_lower_tendsto : Tendsto (fun i => (2:ℝ)^(criticalLowerExponent S.offset i)) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp S.lowerExponent_tendsto
lemma sample_constraint_aemulti (f : DistanceArray → ℝ) (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k : ℝ,∀ hk : 0 ≤ k,∀ z : Torus,∀ n : ℕ,∀ hn : 0<n,
      f (sampleArray k hk z n hn) ≤ C/(n:ℝ)) : ∀ᵐ d ∂L.multi, f d.val ≤ 0 := by
  apply ae_le_zero_of_positive_rational_null
  intro q hq
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  apply vague_open_null L.filter (fun i => nonaffinePart (S.multiLaw i)) L.multi L.multi_converges
    (isOpen_lt continuous_const (hf.comp continuous_subtype_val))
  intro g hg hz
  have he : ∀ᶠ i in atTop,C/(2:ℝ)^(criticalLowerExponent S.offset i)<q :=
    (tendsto_const_nhds.div_atTop S.power_lower_tendsto).eventually (gt_mem_nhds hqR)
  apply tendsto_const_nhds.congr'
  filter_upwards [L.refines he] with i hi
  symm
  apply integral_nonaffine_scale_zero_of_bound _ _ _ _ _ (S.epsilon_pos i) g f q
  · intro d hd; exact hz d (not_lt.mpr hd)
  · intro j hj z
    exact (hb _ _ z _ (by positivity)).trans ((div_le_div_of_nonneg_left hC (by positivity)
      (by exact_mod_cast pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_right (criticalLowerExponent S.offset i) j))).trans hi.le)
lemma unit_aemulti : ∀ᵐ d ∂L.multi, UnitArray d.val := by
  have h (s t : DyadicTime) : ∀ᵐ d ∂L.multi,d.val.val s t-|(t:ℝ)-(s:ℝ)| ≤ 0 := by
    apply S.sample_constraint_aemulti L (fun d => d.val s t-|(t:ℝ)-(s:ℝ)|)
      ((continuous_arrayEval s t).sub continuous_const) 1 (by norm_num)
    intro k hk z n hn
    change rescaledDistance k z n s t-|(t:ℝ)-(s:ℝ)| ≤ 1/(n:ℝ)
    linarith [rescaledDistance_bound k hk z n hn s t]
  filter_upwards [ae_all_iff.mpr (fun s => ae_all_iff.mpr (h s))] with d hd
  intro s t
  linarith [hd s t]
lemma tree_aemulti : ∀ᵐ d ∂L.multi, TreeArray d.val := by
  have h (v x y z : DyadicTime) : ∀ᵐ d ∂L.multi,
      min (d.val.val v x+d.val.val v y-d.val.val x y) (d.val.val v y+d.val.val v z-d.val.val y z)-
      (d.val.val v x+d.val.val v z-d.val.val x z) ≤ 0 := by
    have hc (a b c : DyadicTime) : Continuous (fun d : DistanceArray => d.val a b+d.val a c-d.val b c) :=
      ((continuous_arrayEval a b).add (continuous_arrayEval a c)).sub (continuous_arrayEval b c)
    exact S.sample_constraint_aemulti L _ (((hc v x y).min (hc v y z)).sub (hc v x z)) 3 (by norm_num)
      (fun k hk q n hn => rescaledDistance_tree k hk q n hn v x y z)
  filter_upwards [ae_all_iff.mpr (fun v => ae_all_iff.mpr (fun x => ae_all_iff.mpr
    (fun y => ae_all_iff.mpr (h v x y))))] with d hd
  intro v x y z
  linarith [hd v x y z]
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayHalf
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Topology Classical
namespace StandardMapEntropy
lemma map_half_dilate (μ : Measure NonAffineArray) (hu : ∀ᵐ d ∂μ,UnitArray d.val) :
    (μ.map nonaffineDilate).map nonaffineHalf=μ := by
  rw [Measure.map_map measurable_nonaffineHalf continuous_nonaffineDilate.measurable]
  calc
    μ.map (nonaffineHalf ∘ nonaffineDilate)=μ.map id := Measure.map_congr (hu.mono (fun d hd => nonaffineHalf_dilate d hd))
    _=μ := Measure.map_id
lemma map_dilate_half (μ : Measure NonAffineArray) (hu : ∀ᵐ d ∂μ,UnitArray d.val) :
    (μ.map nonaffineHalf).map nonaffineDilate=μ := by
  rw [Measure.map_map continuous_nonaffineDilate.measurable measurable_nonaffineHalf]
  calc
    μ.map (nonaffineDilate ∘ nonaffineHalf)=μ.map id := Measure.map_congr (hu.mono (fun d hd => nonaffineDilate_half d hd))
    _=μ := Measure.map_id
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma half_balance : L.multi=L.multi.map nonaffineHalf+L.terminal.map nonaffineHalf := by
  have hh := congrArg (fun μ : Measure NonAffineArray => μ.map nonaffineHalf) (S.dilation_balance_q44 L)
  rw [map_half_dilate L.multi (S.unit_aemulti L),Measure.map_add] at hh <;> try exact measurable_nonaffineHalf
  exact hh
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_HalfDecomposition
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal
namespace StandardMapEntropy
lemma sub_add_cancel_sigma {X : Type*} [MeasurableSpace X] (μ ν : Measure X) [SigmaFinite ν]
    (h : ν≤μ) : μ-ν+ν=μ := by
  have hr : ∀n:ℕ,(μ-ν+ν).restrict (spanningSets ν n)=μ.restrict (spanningSets ν n) := by
    intro n
    rw [Measure.restrict_add,Measure.restrict_sub_eq_restrict_sub_restrict (measurableSet_spanningSets ν n)]
    have : IsFiniteMeasure (ν.restrict (spanningSets ν n)) := isFiniteMeasure_restrict.mpr (measure_spanningSets_lt_top ν n).ne
    exact Measure.sub_add_cancel_of_le (Measure.restrict_mono le_rfl h)
  have hh := Measure.restrict_iUnion_congr.mpr hr
  rwa [iUnion_spanningSets,Measure.restrict_univ,Measure.restrict_univ] at hh
lemma map_iterate_succ {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → X) (hf : Measurable f) (n : ℕ) :
    (μ.map (f^[n])).map f=μ.map (f^[n+1]) := by
  rw [Measure.map_map hf (hf.iterate n)]
  congr 1
  exact funext (fun x => (Function.iterate_succ_apply' f n x).symm)
lemma map_iterate_succ' {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → X) (hf : Measurable f) (n : ℕ) :
    (μ.map f).map (f^[n])=μ.map (f^[n+1]) := by
  rw [Measure.map_map (hf.iterate n) hf]
  congr 1
lemma renewal_partial {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (f : X → X) (hf : Measurable f)
    (hb : μ=μ.map f+ν.map f) (n : ℕ) :
    μ=μ.map (f^[n])+∑j∈Finset.range n,ν.map (f^[j+1]) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := congrArg (fun m : Measure X => m.map (f^[n])) hb
    rw [Measure.map_add _ _ (hf.iterate n),map_iterate_succ' μ f hf n,map_iterate_succ' ν f hf n] at hh
    rw [Finset.sum_range_succ]
    calc
      μ=μ.map (f^[n])+∑j∈Finset.range n,ν.map (f^[j+1]) := ih
      _=μ.map (f^[n+1])+(∑j∈Finset.range n,ν.map (f^[j+1])+ν.map (f^[n+1])) := by rw [hh]; ac_rfl
lemma renewal_sum_le {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (f : X → X) (hf : Measurable f)
    (hb : μ=μ.map f+ν.map f) : (Measure.sum (fun j : ℕ => ν.map (f^[j+1])))≤μ := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.sum_apply _ hs]
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  have hh : (∑j∈Finset.range n,ν.map (f^[j+1]))≤μ := by
    rw [renewal_partial μ ν f hf hb n]
    exact Measure.le_add_left le_rfl
  simpa only [Measure.finsetSum_apply] using hh s
lemma renewal_sum_balance {X : Type*} [MeasurableSpace X] (ν : Measure X) (f : X → X) (hf : Measurable f) :
    Measure.sum (fun j : ℕ => ν.map (f^[j+1]))=
      (Measure.sum (fun j : ℕ => ν.map (f^[j+1]))).map f+ν.map f := by
  rw [Measure.map_sum hf.aemeasurable]
  ext s hs
  simp_rw [Measure.add_apply,Measure.sum_apply _ hs,map_iterate_succ ν f hf]
  rw [add_comm]
  exact tsum_eq_zero_add' ENNReal.summable
lemma renewal_remainder_invariant {X : Type*} [MeasurableSpace X] (μ ν : Measure X) [SigmaFinite μ]
    (f : X → X) (hf : Measurable f) (hb : μ=μ.map f+ν.map f) :
    let σ:=Measure.sum (fun j : ℕ => ν.map (f^[j+1])); (μ-σ).map f=μ-σ := by
  dsimp only
  let σ:=Measure.sum (fun j : ℕ => ν.map (f^[j+1]))
  have hσ : σ≤μ := renewal_sum_le μ ν f hf hb
  have : SigmaFinite σ := Measure.sigmaFinite_of_le μ hσ
  have he : μ-σ+σ=μ := sub_add_cancel_sigma μ σ hσ
  have hs : σ=σ.map f+ν.map f := renewal_sum_balance ν f hf
  apply (Measure.add_left_inj σ _ _).mp
  calc
    (μ-σ).map f+σ=(μ-σ).map f+σ.map f+ν.map f := by calc
      (μ-σ).map f+σ=(μ-σ).map f+(σ.map f+ν.map f) := congrArg ((μ-σ).map f+·) hs
      _=_ := (add_assoc _ _ _).symm
    _=(μ-σ+σ).map f+ν.map f := by rw [Measure.map_add _ _ hf]
    _=μ := by rw [he]; exact hb.symm
    _=μ-σ+σ := he.symm
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RemainderLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma remainder_le : S.remainderLaw L≤L.multi := Measure.sub_le
lemma remainder_unit : ∀ᵐd ∂S.remainderLaw L,UnitArray d.val := ae_mono (S.remainder_le L) (S.unit_aemulti L)
lemma remainder_half : (S.remainderLaw L).map nonaffineHalf=S.remainderLaw L := by
  have : IsFiniteMeasureOnCompacts L.multi := L.multi_local
  exact renewal_remainder_invariant _ _ _ measurable_nonaffineHalf (S.half_balance L)
lemma remainder_dilate : (S.remainderLaw L).map nonaffineDilate=S.remainderLaw L := by
  have hh := congrArg (fun μ : Measure NonAffineArray => μ.map nonaffineDilate) (S.remainder_half L)
  rw [map_dilate_half _ (S.remainder_unit L)] at hh
  exact hh.symm
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CappedTests
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical ENNReal
namespace StandardMapEntropy
lemma capG_slow {α : ℝ} {d : DistanceArray}
    (h : ∀s t:DyadicTime,d.val s t≤(999/1000)*|(t:ℝ)-(s:ℝ)|) : capG α d=0 := by
  have hh (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) : entropyCap α (arrayShortfall s t d)=1 := by
    apply entropyCap_one
    have hs := h s t
    rw [abs_of_pos (sub_pos.mpr hst)] at hs
    have he := (div_le_iff₀ (sub_pos.mpr hst)).mpr hs
    unfold arrayShortfall
    linarith
  unfold capG
  rw [hh _ _ (by norm_num),hh _ _ (by norm_num),hh _ _ (by norm_num)]
  norm_num
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointDefinition
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy

lemma measurable_leftEndpoint : Measurable leftEndpoint := by
  apply Measurable.iInf; intro s
  apply Measurable.iInf; intro t
  exact measurable_const.ite
    ((isClosed_eq (continuous_arrayEval s t) continuous_const).measurableSet.compl) measurable_const
lemma measurable_rightEndpoint : Measurable rightEndpoint := by
  apply Measurable.iSup; intro s
  apply Measurable.iSup; intro t
  exact measurable_const.ite
    ((isClosed_eq (continuous_arrayEval s t) continuous_const).measurableSet.compl) measurable_const
lemma leftEndpoint_le_of_nonunit (d : DistanceArray) {s t : DyadicTime}
    (h : d.val s t≠|(t:ℝ)-(s:ℝ)|) : leftEndpoint d≤((max (s:ℝ) (t:ℝ)):EReal) := by
  unfold leftEndpoint
  exact (iInf_le_of_le s (iInf_le_of_le t (by rw [ite_eq_left h])))
lemma le_rightEndpoint_of_nonunit (d : DistanceArray) {s t : DyadicTime}
    (h : d.val s t≠|(t:ℝ)-(s:ℝ)|) : ((min (s:ℝ) (t:ℝ)):EReal) ≤ rightEndpoint d := by
  unfold rightEndpoint
  exact (le_iSup_of_le s (le_iSup_of_le t (by rw [ite_eq_left h])))
lemma le_leftEndpoint_iff (d : DistanceArray) (a : EReal) : a≤leftEndpoint d ↔
    ∀s t:DyadicTime,d.val s t≠|(t:ℝ)-(s:ℝ)| → a≤((max (s:ℝ) (t:ℝ)):EReal) := by
  simp only [leftEndpoint,le_iInf_iff]
  constructor
  · intro h s t hn; simpa only [ite_eq_left hn] using h s t
  · intro h s t; split_ifs with hn
    · exact h s t hn
    · exact le_top
lemma rightEndpoint_le_iff (d : DistanceArray) (a : EReal) : rightEndpoint d≤a ↔
    ∀s t:DyadicTime,d.val s t≠|(t:ℝ)-(s:ℝ)| → ((min (s:ℝ) (t:ℝ)):EReal)≤a := by
  simp only [rightEndpoint,iSup_le_iff]
  constructor
  · intro h s t hn; simpa only [ite_eq_left hn] using h s t
  · intro h s t; split_ifs with hn
    · exact h s t hn
    · exact bot_le
lemma leftEndpoint_lower_ray (d : DistanceArray) {a : ℝ}
    (h : ∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) : (a:EReal)≤leftEndpoint d := by
  apply (le_leftEndpoint_iff d a).mpr
  intro s t hn
  have hh : a < max (s:ℝ) (t:ℝ) := by
    by_contra hm
    have hm' := le_of_not_gt hm
    exact hn (h s t ((le_max_left _ _).trans hm') ((le_max_right _ _).trans hm'))
  exact EReal.coe_le_coe_iff.mpr hh.le
lemma rightEndpoint_upper_ray (d : DistanceArray) {b : ℝ}
    (h : ∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) : rightEndpoint d≤(b:EReal) := by
  apply (rightEndpoint_le_iff d b).mpr
  intro s t hn
  have hh : min (s:ℝ) (t:ℝ)<b := by
    by_contra hm
    have hm' := le_of_not_gt hm
    exact hn (h s t (hm'.trans (min_le_left _ _)) (hm'.trans (min_le_right _ _)))
  exact EReal.coe_le_coe_iff.mpr hh.le
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointShapes
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
lemma dyadic_between {a b : ℝ} (hab : a < b) : ∃s : DyadicTime,a < (s:ℝ) ∧ (s:ℝ) < b := by
  obtain ⟨x,⟨s,rfl⟩,ha,hb⟩ := dyadicTime_dense.exists_between hab
  exact ⟨s,ha,hb⟩
lemma dyadic_pair_between {a b : ℝ} (hab : a < b) :
    ∃s t : DyadicTime,a < (s:ℝ) ∧ (s:ℝ) < (t:ℝ) ∧ (t:ℝ) < b := by
  obtain ⟨s,has,hsb⟩ := dyadic_between hab
  obtain ⟨t,hst,htb⟩ := dyadic_between hsb
  exact ⟨s,t,has,hst,htb⟩
lemma nonunit_of_slow {d : DistanceArray} {c : ℝ} (hc : c < 1) {s t : DyadicTime}
    (hst : (s:ℝ) < (t:ℝ)) (h : d.val s t ≤ c*((t:ℝ)-(s:ℝ))) : d.val s t ≠ |(t:ℝ)-(s:ℝ)| := by
  rw [abs_of_pos (sub_pos.mpr hst)]
  intro he
  have hp := mul_lt_mul_of_pos_right hc (sub_pos.mpr hst)
  nlinarith
lemma leftEndpoint_le_of_slow_interval {d : DistanceArray} {a b c : ℝ} (hab : a < b) (hc : c < 1)
    (h : ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d ≤ (a:EReal) := by
  by_contra hn
  obtain ⟨r,har,hr⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have har' : a < r := EReal.coe_lt_coe_iff.mp har
  obtain ⟨s,t,has,hst,htb⟩ := dyadic_pair_between (lt_min har' hab)
  have htb' := (lt_min_iff.mp htb).2
  have htr := (lt_min_iff.mp htb).1
  have hs := h s t ⟨has.le,(hst.trans htb').le⟩ ⟨(has.trans hst).le,htb'.le⟩
  rw [abs_of_pos (sub_pos.mpr hst)] at hs
  have hu := leftEndpoint_le_of_nonunit d (nonunit_of_slow hc hst hs)
  rw [max_eq_right (EReal.coe_le_coe_iff.mpr hst.le)] at hu
  exact (not_le_of_gt hr) (hu.trans (EReal.coe_le_coe_iff.mpr htr.le))
lemma rightEndpoint_ge_of_slow_interval {d : DistanceArray} {a b c : ℝ} (hab : a < b) (hc : c < 1)
    (h : ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) :
    (b:EReal) ≤ rightEndpoint d := by
  by_contra hn
  obtain ⟨r,hr,hrb⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have hrb' : r < b := EReal.coe_lt_coe_iff.mp hrb
  obtain ⟨s,t,has,hst,htb⟩ := dyadic_pair_between (max_lt hrb' hab)
  have has' := (max_lt_iff.mp has).2
  have hrs := (max_lt_iff.mp has).1
  have hs := h s t ⟨has'.le,(hst.trans htb).le⟩ ⟨(has'.trans hst).le,htb.le⟩
  rw [abs_of_pos (sub_pos.mpr hst)] at hs
  have hu := le_rightEndpoint_of_nonunit d (nonunit_of_slow hc hst hs)
  rw [min_eq_left (EReal.coe_le_coe_iff.mpr hst.le)] at hu
  exact (not_le_of_gt hr) ((EReal.coe_le_coe_iff.mpr hrs.le).trans hu)
lemma endpoints_left_ray {d : DistanceArray} {a c : ℝ} (hc : c < 1)
    (hl : ∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hs : ∀s t:DyadicTime,a≤(s:ℝ) → a≤(t:ℝ) → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d=(a:EReal) ∧ rightEndpoint d=⊤ := by
  constructor
  · exact le_antisymm (leftEndpoint_le_of_slow_interval (b := a+1) (by linarith) hc (fun s t hp hq => hs s t hp.1 hq.1))
      (leftEndpoint_lower_ray d hl)
  · apply eq_top_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,hr,_⟩ := EReal.exists_between_coe_real hh
    have he := rightEndpoint_ge_of_slow_interval (d := d) (a := max r a) (b := max r a+1) (by linarith) hc
      (fun s t hp hq => hs s t ((le_max_right _ _).trans hp.1) ((le_max_right _ _).trans hq.1))
    exact (not_le_of_gt hr) ((EReal.coe_le_coe_iff.mpr (by linarith [le_max_left r a])).trans he)
lemma endpoints_right_ray {d : DistanceArray} {b c : ℝ} (hc : c < 1)
    (hr : ∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hs : ∀s t:DyadicTime,(s:ℝ)≤b → (t:ℝ)≤b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d=⊥ ∧ rightEndpoint d=(b:EReal) := by
  constructor
  · apply eq_bot_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,_,hr'⟩ := EReal.exists_between_coe_real hh
    have he := leftEndpoint_le_of_slow_interval (d := d) (a := min r b-1) (b := min r b) (by linarith) hc
      (fun s t hp hq => hs s t (hp.2.trans (min_le_right _ _)) (hq.2.trans (min_le_right _ _)))
    exact (not_le_of_gt hr') (he.trans (EReal.coe_le_coe_iff.mpr (by linarith [min_le_left r b])))
  · exact le_antisymm (rightEndpoint_upper_ray d hr)
      (rightEndpoint_ge_of_slow_interval (a := b-1) (by linarith) hc (fun s t hp hq => hs s t hp.2 hq.2))
lemma endpoints_two_rays {d : DistanceArray} {a b c : ℝ} (hab : a < b) (hc : c < 1)
    (hl : ∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hr : ∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hs : ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d=(a:EReal) ∧ rightEndpoint d=(b:EReal) :=
  ⟨le_antisymm (leftEndpoint_le_of_slow_interval hab hc hs) (leftEndpoint_lower_ray d hl),
   le_antisymm (rightEndpoint_upper_ray d hr) (rightEndpoint_ge_of_slow_interval hab hc hs)⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointCovariance
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
lemma endpoints_reindex (d d' : DistanceArray) (e : ℝ ≃o ℝ) (b : DyadicTime ≃ DyadicTime)
    (hb : ∀s:DyadicTime,(b s:ℝ)=e (s:ℝ))
    (he : ∀s t:DyadicTime,d'.val (b s) (b t)≠|(b t:ℝ)-(b s:ℝ)| ↔ d.val s t≠|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d'=erealOrderIso e (leftEndpoint d) ∧ rightEndpoint d'=erealOrderIso e (rightEndpoint d) := by
  constructor
  · unfold leftEndpoint
    rw [←b.iInf_comp]
    simp_rw [←b.iInf_comp (g := fun t => if d'.val (b _) t≠|(t:ℝ)-(b _:ℝ)| then ((max (b _:ℝ) (t:ℝ)):EReal) else ⊤)]
    simp only [OrderIso.map_iInf]
    apply iInf_congr; intro s
    apply iInf_congr; intro t
    simp only [he s t]
    split_ifs
    · rcases le_total (s:ℝ) (t:ℝ) with h|h
      · rw [max_eq_right (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact max_eq_right (EReal.coe_le_coe_iff.mpr (e.monotone h))
      · rw [max_eq_left (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact max_eq_left (EReal.coe_le_coe_iff.mpr (e.monotone h))
    · rfl
  · unfold rightEndpoint
    rw [←b.iSup_comp]
    simp_rw [←b.iSup_comp (g := fun t => if d'.val (b _) t≠|(t:ℝ)-(b _:ℝ)| then ((min (b _:ℝ) (t:ℝ)):EReal) else ⊥)]
    simp only [OrderIso.map_iSup]
    apply iSup_congr; intro s
    apply iSup_congr; intro t
    simp only [he s t]
    split_ifs
    · rcases le_total (s:ℝ) (t:ℝ) with h|h
      · rw [min_eq_left (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact min_eq_left (EReal.coe_le_coe_iff.mpr (e.monotone h))
      · rw [min_eq_right (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact min_eq_right (EReal.coe_le_coe_iff.mpr (e.monotone h))
    · rfl
lemma endpoints_dilate (d : DistanceArray) :
    leftEndpoint (arrayDilate d)=erealOrderIso (OrderIso.mulRight₀ (1/2:ℝ) (by norm_num)) (leftEndpoint d) ∧
    rightEndpoint (arrayDilate d)=erealOrderIso (OrderIso.mulRight₀ (1/2:ℝ) (by norm_num)) (rightEndpoint d) := by
  apply endpoints_reindex d _ _ dyadicHalfEquiv
  · intro s; change (s:ℝ)/2=(s:ℝ)*(1/2); ring
  · intro s t
    change (d.val (dyadicHalf s+dyadicHalf s) (dyadicHalf t+dyadicHalf t)/2≠|(t:ℝ)/2-(s:ℝ)/2|) ↔ _
    rw [dyadicHalf_add_self,dyadicHalf_add_self,←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact not_congr (div_left_inj' (by norm_num))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointClasses
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
lemma measurable_endpointLeft : Measurable endpointLeft := measurable_ereal_toReal.comp measurable_leftEndpoint
lemma measurable_endpointRight : Measurable endpointRight := measurable_ereal_toReal.comp measurable_rightEndpoint
lemma measurableSet_twoRayClass : MeasurableSet twoRayClass :=
  ((measurable_leftEndpoint (measurableSet_singleton ⊥)).compl).inter
    (((measurable_leftEndpoint (measurableSet_singleton ⊤)).compl).inter
      (((measurable_rightEndpoint (measurableSet_singleton ⊥)).compl).inter ((measurable_rightEndpoint (measurableSet_singleton ⊤)).compl)))
lemma slowShape_dyadic {d : DistanceArray} {c:ℝ} (hu:UnitArray d) (h:SlowShape (realArray d) c) :
    (∀s t:DyadicTime,d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) ∨
    (∃a:ℝ,(∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,a≤(s:ℝ) → a≤(t:ℝ) → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|)) ∨
    (∃b:ℝ,(∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,(s:ℝ)≤b → (t:ℝ)≤b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|)) ∨
    (∃a b:ℝ,a<b ∧
      (∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|)) := by
  rcases h with hs|⟨a,hl,hs⟩|⟨b,hr,hs⟩|⟨a,b,hab,⟨hl,hr⟩,hs⟩
  · exact Or.inl (fun s t => by simpa only [realArray_coe d hu] using hs s t)
  · exact Or.inr (Or.inl ⟨a,fun s t hp hq => by simpa only [realArray_coe d hu] using hl s hp t hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨b,fun s t hp hq => by simpa only [realArray_coe d hu] using hr s hp t hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a,b,hab,fun s t hp hq => by simpa only [realArray_coe d hu] using hl s t hp hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hr s t hp hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointActions
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma erealOrderIso_eq_bot (e:ℝ≃oℝ) (x:EReal) : erealOrderIso e x=⊥ ↔ x=⊥ := by
  constructor
  · intro h; apply (erealOrderIso e).injective; simpa only [erealOrderIso_bot] using h
  · intro h; rw [h,erealOrderIso_bot]
lemma erealOrderIso_eq_top (e:ℝ≃oℝ) (x:EReal) : erealOrderIso e x=⊤ ↔ x=⊤ := by
  constructor
  · intro h; apply (erealOrderIso e).injective; simpa only [erealOrderIso_top] using h
  · intro h; rw [h,erealOrderIso_top]
lemma twoRayClass_dilate (d:DistanceArray) : arrayDilate d∈twoRayClass ↔ d∈twoRayClass := by
  change (_≠⊥ ∧ _≠⊤ ∧ _≠⊥ ∧ _≠⊤) ↔ _
  rw [(endpoints_dilate d).1,(endpoints_dilate d).2]
  simp only [ne_eq,erealOrderIso_eq_bot,erealOrderIso_eq_top]
  rfl
lemma endpointLeft_dilate (d:DistanceArray) (ht:leftEndpoint d≠⊤) (hb:leftEndpoint d≠⊥) :
    endpointLeft (arrayDilate d)=endpointLeft d/2 := by
  unfold endpointLeft
  rw [(endpoints_dilate d).1,←EReal.coe_toReal ht hb,erealOrderIso_coe]
  simp only [EReal.toReal_coe]
  simp only [OrderIso.mulRight₀_apply]
  ring
lemma endpointRight_dilate (d:DistanceArray) (ht:rightEndpoint d≠⊤) (hb:rightEndpoint d≠⊥) :
    endpointRight (arrayDilate d)=endpointRight d/2 := by
  unfold endpointRight
  rw [(endpoints_dilate d).2,←EReal.coe_toReal ht hb,erealOrderIso_coe]
  simp only [EReal.toReal_coe]
  simp only [OrderIso.mulRight₀_apply]
  ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ScaleAction
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Classical
namespace StandardMapEntropy
lemma nonaffineDouble_unit (d:NonAffineArray) : UnitArray (nonaffineDouble d).val ↔ UnitArray d.val := by
  by_cases h:UnitArray d.val
  · simp only [nonaffineDouble,h,iff_true]; exact arrayDilate_unit d.val h
  · simp only [nonaffineDouble,ite_eq_right h]
lemma nonaffineHalf_unit_iff (d:NonAffineArray) : UnitArray (nonaffineHalf d).val ↔ UnitArray d.val := by
  by_cases h:UnitArray d.val
  · exact iff_of_true (nonaffineHalf_unit d h) h
  · simp only [nonaffineHalf,dite_eq_right h]
lemma scaleZ_add (i j:ℤ) (d:NonAffineArray) : scaleZ (i+j) d=scaleZ i (scaleZ j d) := by
  change (scaleEquiv.toEquiv^(i+j)) d=(scaleEquiv.toEquiv^i) ((scaleEquiv.toEquiv^j) d)
  rw [zpow_add]; rfl
lemma scaleZ_one (d:NonAffineArray) : scaleZ 1 d=nonaffineDouble d := by simp only [scaleZ,zpow_one]; rfl
lemma scaleZ_neg_one (d:NonAffineArray) : scaleZ (-1) d=nonaffineHalf d := by simp only [scaleZ,zpow_neg_one]; rfl
lemma scaleZ_unit (j:ℤ) (d:NonAffineArray) : UnitArray (scaleZ j d).val ↔ UnitArray d.val := by
  induction j using Int.induction_on with
  | zero => rw [scaleZ_zero]
  | succ j ih =>
    rw [add_comm,scaleZ_add,scaleZ_one,nonaffineDouble_unit,ih]
  | pred j ih =>
    rw [sub_eq_add_neg,add_comm,scaleZ_add,scaleZ_neg_one,nonaffineHalf_unit_iff,ih]
lemma measurable_scaleZ (j:ℤ) : Measurable (scaleZ j) := by
  induction j using Int.induction_on with
  | zero =>
    have he : (scaleZ 0:NonAffineArray→NonAffineArray)=id := funext scaleZ_zero
    rw [he]; exact measurable_id
  | succ j ih =>
    have he : (scaleZ ((j:ℤ)+1):NonAffineArray→NonAffineArray)=nonaffineDouble ∘ scaleZ j := funext (fun d => by rw [add_comm,scaleZ_add,scaleZ_one]; rfl)
    rw [he]; exact measurable_nonaffineDouble.comp ih
  | pred j ih =>
    have he : (scaleZ (-(j:ℤ)-1):NonAffineArray→NonAffineArray)=nonaffineHalf ∘ scaleZ (-(j:ℤ)) := funext (fun d => by rw [sub_eq_add_neg,add_comm,scaleZ_add,scaleZ_neg_one]; rfl)
    rw [he]; exact measurable_nonaffineHalf.comp ih
lemma map_scaleZ (μ:Measure NonAffineArray) (hu:∀ᵐd ∂μ,UnitArray d.val) (h:μ.map nonaffineDilate=μ) (j:ℤ) : μ.map (scaleZ j)=μ := by
  have hd : μ.map nonaffineDouble=μ := (Measure.map_congr (hu.mono (fun d hd => by simp only [nonaffineDouble,ite_eq_left hd]))).trans h
  have hb : μ.map nonaffineHalf=μ := by calc
    μ.map nonaffineHalf=(μ.map nonaffineDilate).map nonaffineHalf := by rw [h]
    _=μ := map_half_dilate μ hu
  induction j using Int.induction_on with
  | zero =>
    have he : (scaleZ 0:NonAffineArray→NonAffineArray)=id := funext scaleZ_zero
    rw [he,Measure.map_id]
  | succ j ih =>
    have he : (scaleZ (j+1):NonAffineArray→NonAffineArray)=nonaffineDouble ∘ scaleZ j := funext (fun d => by rw [add_comm,scaleZ_add,scaleZ_one]; rfl)
    rw [he,←Measure.map_map measurable_nonaffineDouble (measurable_scaleZ j),ih,hd]
  | pred j ih =>
    have he : (scaleZ (-(j:ℤ)-1):NonAffineArray→NonAffineArray)=nonaffineHalf ∘ scaleZ (-(j:ℤ)) := funext (fun d => by rw [sub_eq_add_neg,add_comm,scaleZ_add,scaleZ_neg_one]; rfl)
    rw [he,←Measure.map_map measurable_nonaffineHalf (measurable_scaleZ (-(j:ℤ))),ih,hb]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ScaleEndpoints
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Classical
namespace StandardMapEntropy
lemma measurable_coreLength : Measurable coreLength := measurable_endpointRight.sub measurable_endpointLeft
lemma coreLength_dilate (d:DistanceArray) (hd:d∈twoRayClass) : coreLength (arrayDilate d)=coreLength d/2 := by
  unfold coreLength
  rw [endpointRight_dilate d hd.2.2.2 hd.2.2.1,endpointLeft_dilate d hd.2.1 hd.1]
  ring
lemma twoRayClass_half (d:NonAffineArray) (hu:UnitArray d.val) : (nonaffineHalf d).val∈twoRayClass ↔ d.val∈twoRayClass := by
  have he := twoRayClass_dilate (nonaffineHalf d).val
  change (nonaffineDilate (nonaffineHalf d)).val∈twoRayClass ↔ _ at he
  rw [nonaffineDilate_half d hu] at he
  exact he.symm
lemma coreLength_half (d:NonAffineArray) (hu:UnitArray d.val) (hd:d.val∈twoRayClass) : coreLength (nonaffineHalf d).val=2*coreLength d.val := by
  have he := coreLength_dilate (nonaffineHalf d).val ((twoRayClass_half d hu).mpr hd)
  change coreLength (nonaffineDilate (nonaffineHalf d)).val=_ at he
  rw [nonaffineDilate_half d hu] at he
  linarith
lemma scaleZ_twoRay (j:ℤ) (d:NonAffineArray) (hu:UnitArray d.val) : (scaleZ j d).val∈twoRayClass ↔ d.val∈twoRayClass := by
  induction j using Int.induction_on with
  | zero => rw [scaleZ_zero]
  | succ j ih =>
    rw [add_comm,scaleZ_add,scaleZ_one,nonaffineDouble,ite_eq_left ((scaleZ_unit j d).mpr hu)]
    exact (twoRayClass_dilate _).trans ih
  | pred j ih =>
    rw [sub_eq_add_neg,add_comm,scaleZ_add,scaleZ_neg_one]
    exact (twoRayClass_half _ ((scaleZ_unit (-(j:ℤ)) d).mpr hu)).trans ih
lemma scaleZ_length (j:ℤ) (d:NonAffineArray) (hu:UnitArray d.val) (hd:d.val∈twoRayClass) : coreLength (scaleZ j d).val=coreLength d.val/(2:ℝ)^j := by
  induction j using Int.induction_on with
  | zero => simp only [scaleZ_zero,zpow_zero,div_one]
  | succ j ih =>
    rw [add_comm,scaleZ_add,scaleZ_one,nonaffineDouble,ite_eq_left ((scaleZ_unit j d).mpr hu)]
    change coreLength (arrayDilate (scaleZ j d).val)=_
    rw [coreLength_dilate _ ((scaleZ_twoRay j d hu).mpr hd),ih,zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_one]
    ring
  | pred j ih =>
    rw [sub_eq_add_neg,add_comm,scaleZ_add,scaleZ_neg_one]
    rw [coreLength_half _ ((scaleZ_unit (-(j:ℤ)) d).mpr hu) ((scaleZ_twoRay (-(j:ℤ)) d hu).mpr hd),ih,zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_neg_one]
    ring
lemma measurableSet_lengthBand (j:ℤ) : MeasurableSet (lengthBand j) :=
  (isClosed_unitArray.preimage continuous_subtype_val).measurableSet.inter
    ((measurableSet_twoRayClass.preimage measurable_subtype_coe).inter
      (((measurable_coreLength.comp measurable_subtype_coe) measurableSet_Ici).inter ((measurable_coreLength.comp measurable_subtype_coe) measurableSet_Iio)))
lemma lengthBand_scaleZ (i j:ℤ) : (scaleZ i)⁻¹'lengthBand j=lengthBand (i+j) := by
  ext d
  simp only [mem_preimage,lengthBand,mem_ofPred_eq]
  constructor
  · rintro ⟨hu,hd,hl,hr⟩
    have hud := (scaleZ_unit i d).mp hu
    have hdd := (scaleZ_twoRay i d hud).mp hd
    rw [scaleZ_length i d hud hdd] at hl hr
    refine ⟨hud,hdd,?_,?_⟩
    · have hh := (le_div_iff₀ (zpow_pos (by norm_num : (0:ℝ)<2) i)).mp hl
      rw [zpow_add₀ (by norm_num : (2:ℝ)≠0)]
      simpa only [mul_comm] using hh
    · have hh := (div_lt_iff₀ (zpow_pos (by norm_num : (0:ℝ)<2) i)).mp hr
      rw [show i+j+1=i+(j+1) by omega,zpow_add₀ (by norm_num : (2:ℝ)≠0)]
      simpa only [mul_comm] using hh
  · rintro ⟨hu,hd,hl,hr⟩
    refine ⟨(scaleZ_unit i d).mpr hu,(scaleZ_twoRay i d hu).mpr hd,?_,?_⟩
    · rw [scaleZ_length i d hu hd,le_div_iff₀ (zpow_pos (by norm_num : (0:ℝ)<2) i)]
      rw [zpow_add₀ (by norm_num : (2:ℝ)≠0),mul_comm] at hl
      exact hl
    · rw [scaleZ_length i d hu hd,div_lt_iff₀ (zpow_pos (by norm_num : (0:ℝ)<2) i)]
      rw [show i+j+1=i+(j+1) by omega,zpow_add₀ (by norm_num : (2:ℝ)≠0),mul_comm] at hr
      exact hr
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BandSeries
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma lengthBand_disjoint : Pairwise (fun i j : ℤ => Disjoint (lengthBand i) (lengthBand j)) := by
  intro i j hij
  rw [disjoint_left]
  intro d hi hj
  have hpow : StrictMono (fun n:ℤ => (2:ℝ)^n) := zpow_right_strictMono₀ (by norm_num)
  rcases lt_or_gt_of_ne hij with h|h
  · have hh := hpow.monotone (by omega : i + 1 ≤ j)
    exact (not_le_of_gt hi.2.2.2) (hh.trans hj.2.2.1)
  · have hh := hpow.monotone (by omega : j + 1 ≤ i)
    exact (not_le_of_gt hj.2.2.2) (hh.trans hi.2.2.1)
lemma mem_union_lengthBand {d:NonAffineArray} (hu:UnitArray d.val) (hd:d.val∈twoRayClass) (hl:0 < coreLength d.val) : d∈⋃j:ℤ,lengthBand (-j) := by
  obtain ⟨j,hj⟩ := exists_mem_Ico_zpow hl (by norm_num : (1:ℝ)<2)
  exact mem_iUnion.mpr ⟨-j,by simpa only [neg_neg,lengthBand,mem_Ico,mem_ofPred_eq] using And.intro hu (And.intro hd hj)⟩
lemma restrict_lengthBand (μ:Measure NonAffineArray) (hu:∀ᵐd ∂μ,UnitArray d.val) (hS:μ.map nonaffineDilate=μ) (j:ℤ) :
    μ.restrict (lengthBand (-j))=(bandLaw μ).map (scaleZ j) := by
  have hh := Measure.restrict_map (μ:=μ) (measurable_scaleZ j) (measurableSet_lengthBand (-j))
  rw [map_scaleZ μ hu hS j,lengthBand_scaleZ,add_neg_cancel] at hh
  exact hh
lemma bandSeries_law (μ:Measure NonAffineArray) (hu:∀ᵐd ∂μ,UnitArray d.val) (hS:μ.map nonaffineDilate=μ) :
    μ.restrict (⋃j:ℤ,lengthBand (-j))=Measure.sum (fun j:ℤ => (bandLaw μ).map (scaleZ j)) := by
  rw [Measure.restrict_iUnion (fun i j hij => lengthBand_disjoint (by omega : -i ≠ -j)) (fun j => measurableSet_lengthBand (-j))]
  congr 1; funext j; exact restrict_lengthBand μ hu hS j
lemma band_integral_series (μ:Measure NonAffineArray) (hu:∀ᵐd ∂μ,UnitArray d.val) (hS:μ.map nonaffineDilate=μ)
    (g:NonAffineArray→ℝ) (hg:Integrable g μ) :
    HasSum (fun j:ℤ => ∫d,g (scaleZ j d) ∂bandLaw μ) (∫d in ⋃j:ℤ,lengthBand (-j),g d ∂μ) := by
  have hh : Integrable g (Measure.sum (fun j:ℤ => (bandLaw μ).map (scaleZ j))) := by rw [←bandSeries_law μ hu hS]; exact hg.restrict
  have hm (j:ℤ) : Integrable g ((bandLaw μ).map (scaleZ j)) := hh.mono_measure (Measure.le_sum (fun index : ℤ => (bandLaw μ).map (scaleZ index)) j)
  have he (j:ℤ) : (∫d,g d ∂(bandLaw μ).map (scaleZ j))=∫d,g (scaleZ j d) ∂bandLaw μ :=
    integral_map (measurable_scaleZ j).aemeasurable (hm j).aestronglyMeasurable
  have hh' := hasSum_integral_measure hh
  simp_rw [he] at hh'
  rwa [←bandSeries_law μ hu hS] at hh'
lemma bilateral_coboundary_nonpos (F:ℤ→ℝ) (A:ℝ) (h:HasSum (fun j:ℤ => F (j+1)-F j) A)
    (hf:∀ᶠn:ℕ in atTop,F (n:ℤ)≤F (-(n:ℤ))) : A≤0 := by
  have ht : Tendsto (fun n:ℕ => ∑j∈Finset.Ico (-(n:ℤ)) (n:ℤ),(F (j+1)-F j)) atTop (𝓝 A) :=
    h.comp Finset.tendsto_Ico_neg
  have he (n:ℕ) : (∑j∈Finset.Ico (-(n:ℤ)) (n:ℤ),(F (j+1)-F j))=F (n:ℤ)-F (-(n:ℤ)) := by
    have hh := Finset.sum_Ico_int_sub n (fun j => -F j)
    simpa only [neg_sub_neg] using hh
  simp_rw [he] at ht
  exact le_of_tendsto ht (hf.mono (fun n hn => sub_nonpos.mpr hn))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_OneRayZero
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma remainder_local : IsFiniteMeasureOnCompacts (S.remainderLaw L) := by
  have : IsFiniteMeasureOnCompacts L.multi := L.multi_local
  exact ⟨fun K hK => (S.remainder_le L K).trans_lt hK.measure_lt_top⟩
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RemainderCap
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma shape_nonzero_cap_in_band {α:ℝ} {d:NonAffineArray} (hu:UnitArray d.val)
    (hs:SlowShape (realArray d.val) (999/1000))
    (hl:d.val∉leftRayClass) (hr:d.val∉rightRayClass) (hg:capG α d.val≠0) :
    d∈⋃j:ℤ,lengthBand (-j) := by
  rcases slowShape_dyadic hu hs with hslow|⟨a,hleft,hslow⟩|⟨b,hright,hslow⟩|⟨a,b,hab,hleft,hright,hslow⟩
  · exact (hg (capG_slow hslow)).elim
  · have he:=endpoints_left_ray (by norm_num : (999/1000:ℝ)<1) hleft hslow
    exact (hl (by change leftEndpoint d.val≠⊥ ∧ leftEndpoint d.val≠⊤ ∧ rightEndpoint d.val=⊤; rw [he.1,he.2]; simp)).elim
  · have he:=endpoints_right_ray (by norm_num : (999/1000:ℝ)<1) hright hslow
    exact (hr (by change leftEndpoint d.val=⊥ ∧ rightEndpoint d.val≠⊥ ∧ rightEndpoint d.val≠⊤; rw [he.1,he.2]; simp)).elim
  · have he:=endpoints_two_rays hab (by norm_num : (999/1000:ℝ)<1) hleft hright hslow
    have hd:d.val∈twoRayClass := by
      change leftEndpoint d.val≠⊥ ∧ leftEndpoint d.val≠⊤ ∧ rightEndpoint d.val≠⊥ ∧ rightEndpoint d.val≠⊤
      rw [he.1,he.2]; simp
    apply mem_union_lengthBand hu hd
    simp only [coreLength,endpointLeft,endpointRight,he.1,he.2,EReal.toReal_coe]
    exact sub_pos.mpr hab
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma remainder_cap_band (α:ℝ) :
    (∫d:NonAffineArray,capG α d.val ∂S.remainderLaw L)=
      ∫d in ⋃j:ℤ,lengthBand (-j),capG α d.val ∂S.remainderLaw L := by
  have he :(fun d:NonAffineArray => capG α d.val)=ᵐ[S.remainderLaw L]
      (⋃j:ℤ,lengthBand (-j)).indicator (fun d => capG α d.val) := by
    have hl:∀ᵐd ∂S.remainderLaw L,d.val∉leftRayClass := ae_iff.mpr (by simpa only [not_not] using S.remainder_left_ray_zero_q44 L)
    have hr:∀ᵐd ∂S.remainderLaw L,d.val∉rightRayClass := ae_iff.mpr (by simpa only [not_not] using S.remainder_right_ray_zero_q44 L)
    filter_upwards [S.remainder_unit L,S.remainder_shape_q44 L,hl,hr] with d hd hs hl hr
    by_cases hg:capG α d.val=0
    · simp only [hg,Set.indicator_apply]; split_ifs <;> rfl
    · exact (Set.indicator_of_mem (shape_nonzero_cap_in_band hd hs hl hr hg) (fun d : NonAffineArray => capG α d.val)).symm
  rw [integral_congr_ae he,integral_indicator (MeasurableSet.iUnion (fun j => measurableSet_lengthBand (-j)))]
lemma remainder_cap_nonpos_q44_oai {α:ℝ} (ha:0≤α) (ha1:α≤1) (hasmall:α*1200000004≤1/16) :
    (∫d:NonAffineArray,capG α d.val ∂S.remainderLaw L)≤0 := by
  have:=S.remainder_local L
  have hser:=band_integral_series (S.remainderLaw L) (S.remainder_unit L) (S.remainder_dilate L)
    (fun d => capG α d.val) (S.capG_integrable_remainder_q44 L α)
  simp_rw [band_coboundary_q44 _ (S.remainder_shape_q44 L) (S.remainder_translate_q44 L) ha ha1] at hser
  rw [←S.remainder_cap_band L α] at hser
  apply bilateral_coboundary_nonpos _ _ hser
  exact bandMoment_order_q44 _ (S.remainder_shape_q44 L) (S.remainder_translate_q44 L)
    (ae_mono (S.remainder_le L) (S.tree_aemulti L))
    (ae_mono (S.remainder_le L) (S.noCancellation_aemulti_q44 L)) ha ha1 hasmall
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_nonpos_q44_oai := @OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_nonpos_q44_oai
