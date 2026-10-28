-- Prove2me | solution 1 for OAI.StandardMapEntropy.CriticalScaleSequence.slowPair_aeterminal_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:33:33.630118+00:00
-- url     : https://prove2.me/submissions/35b43085-2fc2-45c4-83a1-7e06606d93a8

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_endpoint_bridge_null_q44

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
-- module Solutions.OAIQ44_CM.StandardMap_ArrayTests
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma arrayV_nonneg (s t : DyadicTime) (d : DistanceArray) : 0≤arrayV s t d := sq_nonneg _
lemma array_zero_test_halves (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) (d : DistanceArray)
    (hzero : arrayJ s t d+arrayV s t d=0) :
    d.val s (dyadicMid s t)=d.val s t/2 ∧ d.val (dyadicMid s t) t=d.val s t/2 := by
  have hJ : arrayJ s t d=0 := by linarith [arrayJ_nonneg s t hst d,arrayV_nonneg s t d]
  have hV : arrayV s t d=0 := by linarith
  have he : arrayShortfall s (dyadicMid s t) d=arrayShortfall (dyadicMid s t) t d := by
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hV)
  rw [arrayJ_eq s t hst d] at hJ
  have hsum : d.val s (dyadicMid s t)+d.val (dyadicMid s t) t=d.val s t := by
    have := (div_eq_zero_iff.mp hJ).resolve_right (sub_ne_zero.mpr hst.ne')
    linarith
  unfold arrayShortfall at he
  rw [dyadicMid_val] at he
  have hm : ((s:ℝ)+(t:ℝ))/2-(s:ℝ)=((t:ℝ)-(s:ℝ))/2 := by ring
  have hm' : (t:ℝ)-((s:ℝ)+(t:ℝ))/2=((t:ℝ)-(s:ℝ))/2 := by ring
  rw [hm,hm'] at he
  have hn : ((t:ℝ)-(s:ℝ))/2≠0 := by positivity
  have he' : d.val s (dyadicMid s t)=d.val (dyadicMid s t) t := (div_left_inj' hn).mp (by linarith)
  constructor <;> linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayGrid
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
lemma dyadic_zsmul_val (i : ℤ) (h : DyadicTime) : ((i • h : DyadicTime):ℝ)=(i:ℝ)*(h:ℝ) := by
  simp only [AddSubgroup.coe_zsmul,zsmul_eq_mul]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayAffinity
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
lemma dyadic_common_grid (s t : DyadicTime) :
    ∃ m : ℕ, ∃ a b : ℤ,s=a • dyadicUnit m ∧ t=b • dyadicUnit m := by
  obtain ⟨n,a,hs⟩ := dyadicTime_mem s
  obtain ⟨m,b,ht⟩ := dyadicTime_mem t
  refine ⟨n+m,a*2^m,b*2^n,?_,?_⟩
  · apply Subtype.ext
    rw [dyadic_zsmul_val,dyadicUnit_val,hs,pow_add]
    push_cast
    field_simp
  · apply Subtype.ext
    rw [dyadic_zsmul_val,dyadicUnit_val,ht,pow_add]
    push_cast
    field_simp
lemma arrayTest_nonneg (i : ArrayTestIndex) (d : DistanceArray) : 0 ≤ arrayTest i d :=
  add_nonneg (arrayJ_nonneg _ _ i.property d) (arrayV_nonneg _ _ d)
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
lemma exponent_tendsto : Tendsto S.exponent atTop atTop := tendsto_atTop_mono (fun i => (S.lower_lt i).le) S.lowerExponent_tendsto
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
lemma continuous_realArray (d : DistanceArray) (hd : UnitArray d) :
    Continuous (fun p : ℝ × ℝ => realArray d p.1 p.2) :=
  (uniformContinuous_uniformly_extend
    ((isUniformInducing_val (dyadicTimes:Set ℝ)).prod (isUniformInducing_val (dyadicTimes:Set ℝ)))
    (denseRange_dyadicTime.prodMap denseRange_dyadicTime) (unitArray_lipschitz d hd).uniformContinuous).continuous
@[simp] lemma realArray_coe (d : DistanceArray) (hd : UnitArray d) (s t : DyadicTime) :
    realArray d (s:ℝ) (t:ℝ)=d.val s t :=
  uniformly_extend_of_ind
    ((isUniformInducing_val (dyadicTimes:Set ℝ)).prod (isUniformInducing_val (dyadicTimes:Set ℝ)))
    (denseRange_dyadicTime.prodMap denseRange_dyadicTime) (unitArray_lipschitz d hd).uniformContinuous (s,t)
lemma realArray_nonneg (d : DistanceArray) (hd : UnitArray d) (s t : ℝ) : 0 ≤ realArray d s t := by
  apply isClosed_property2 (p := fun s t => 0 ≤ realArray d s t) dyadicTime_dense (isClosed_le continuous_const (continuous_realArray d hd)) _ s t
  intro x y; simpa only [realArray_coe d hd] using d.property.1 x y
lemma realArray_le (d : DistanceArray) (hd : UnitArray d) (s t : ℝ) : realArray d s t ≤ |t-s| := by
  apply isClosed_property2 (p := fun s t => realArray d s t ≤ |t-s|) dyadicTime_dense (isClosed_le (continuous_realArray d hd) ((continuous_snd.sub continuous_fst).abs)) _ s t
  intro x y; simpa only [realArray_coe d hd] using hd x y
lemma realArray_self (d : DistanceArray) (hd : UnitArray d) (s : ℝ) : realArray d s s=0 := by
  have h0 := realArray_nonneg d hd s s
  have h1 := realArray_le d hd s s
  simp only [sub_self,abs_zero] at h1
  exact le_antisymm h1 h0
lemma realArray_symm (d : DistanceArray) (hd : UnitArray d) (s t : ℝ) : realArray d s t=realArray d t s := by
  apply isClosed_property2 (p := fun s t => realArray d s t=realArray d t s) dyadicTime_dense
    (isClosed_eq (continuous_realArray d hd) ((continuous_realArray d hd).comp (continuous_snd.prodMk continuous_fst))) _ s t
  intro x y; simpa only [realArray_coe d hd] using d.property.2.2.1 x y
lemma realArray_triangle (d : DistanceArray) (hd : UnitArray d) (s t u : ℝ) :
    realArray d s u ≤ realArray d s t+realArray d t u := by
  have hc := continuous_realArray d hd
  apply isClosed_property3 dyadicTime_dense
    (isClosed_le (hc.comp (continuous_fst.prodMk continuous_snd.snd))
      ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).add (hc.comp (continuous_snd.fst.prodMk continuous_snd.snd)))) _ s t u
  intro x y z; simpa only [realArray_coe d hd] using d.property.2.2.2.1 x y z
lemma realArray_tree (d : DistanceArray) (hd : UnitArray d) (ht : TreeArray d) (v x y z : ℝ) :
    min (realArray d v x+realArray d v y-realArray d x y) (realArray d v y+realArray d v z-realArray d y z) ≤
      realArray d v x+realArray d v z-realArray d x z := by
  have hc := continuous_realArray d hd
  let e : DyadicTime × DyadicTime × DyadicTime × DyadicTime → ℝ × ℝ × ℝ × ℝ :=
    Prod.map ((↑) : DyadicTime → ℝ) (Prod.map ((↑) : DyadicTime → ℝ) (Prod.map ((↑) : DyadicTime → ℝ) ((↑) : DyadicTime → ℝ)))
  have he : DenseRange e := denseRange_dyadicTime.prodMap (denseRange_dyadicTime.prodMap (denseRange_dyadicTime.prodMap denseRange_dyadicTime))
  have hcl : IsClosed {p : ℝ × ℝ × ℝ × ℝ |
      min (realArray d p.1 p.2.1+realArray d p.1 p.2.2.1-realArray d p.2.1 p.2.2.1)
        (realArray d p.1 p.2.2.1+realArray d p.1 p.2.2.2-realArray d p.2.2.1 p.2.2.2) ≤
        realArray d p.1 p.2.1+realArray d p.1 p.2.2.2-realArray d p.2.1 p.2.2.2} := by
    apply isClosed_le
    · apply Continuous.min
      · exact ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).add (hc.comp (continuous_fst.prodMk continuous_snd.snd.fst))).sub
          (hc.comp (continuous_snd.fst.prodMk continuous_snd.snd.fst))
      · exact ((hc.comp (continuous_fst.prodMk continuous_snd.snd.fst)).add (hc.comp (continuous_fst.prodMk continuous_snd.snd.snd))).sub
          (hc.comp (continuous_snd.snd.fst.prodMk continuous_snd.snd.snd))
    · exact ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).add (hc.comp (continuous_fst.prodMk continuous_snd.snd.snd))).sub
        (hc.comp (continuous_snd.fst.prodMk continuous_snd.snd.snd))
  have hh := isClosed_property he hcl (fun p => by simpa only [e,Prod.map,realArray_coe d hd] using ht p.1 p.2.1 p.2.2.1 p.2.2.2) (v,x,y,z)
  exact hh
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
lemma power_terminal_tendsto : Tendsto (fun i => (2:ℝ)^(S.exponent i)) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp S.exponent_tendsto
lemma sample_constraint_aeterminal (f : DistanceArray → ℝ) (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k : ℝ,∀ hk : 0 ≤ k,∀ z : Torus,∀ n : ℕ,∀ hn : 0<n,
      f (sampleArray k hk z n hn) ≤ C/(n:ℝ)) : ∀ᵐ d ∂L.terminal, f d.val ≤ 0 := by
  apply ae_le_zero_of_positive_rational_null
  intro q hq
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  apply vague_open_null L.filter (fun i => nonaffinePart (S.terminalLaw i)) L.terminal L.terminal_converges
    (isOpen_lt continuous_const (hf.comp continuous_subtype_val))
  intro g hg hz
  have he : ∀ᶠ i in atTop,C/(2:ℝ)^(S.exponent i)<q :=
    (tendsto_const_nhds.div_atTop S.power_terminal_tendsto).eventually (gt_mem_nhds hqR)
  apply tendsto_const_nhds.congr'
  filter_upwards [L.refines he] with i hi
  symm
  apply integral_nonaffine_scale_zero_of_bound _ _ _ _ _ (S.epsilon_pos i) g f q
  · intro d hd; exact hz d (not_lt.mpr hd)
  · intro j hj z
    exact (hb _ _ z _ (by positivity)).trans ((div_le_div_of_nonneg_left hC (by positivity)
      (by exact_mod_cast pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_right (S.exponent i) j))).trans hi.le)
lemma unit_aeterminal : ∀ᵐ d ∂L.terminal, UnitArray d.val := by
  have h (s t : DyadicTime) : ∀ᵐ d ∂L.terminal,d.val.val s t-|(t:ℝ)-(s:ℝ)| ≤ 0 := by
    apply S.sample_constraint_aeterminal L (fun d => d.val s t-|(t:ℝ)-(s:ℝ)|)
      ((continuous_arrayEval s t).sub continuous_const) 1 (by norm_num)
    intro k hk z n hn
    change rescaledDistance k z n s t-|(t:ℝ)-(s:ℝ)| ≤ 1/(n:ℝ)
    linarith [rescaledDistance_bound k hk z n hn s t]
  filter_upwards [ae_all_iff.mpr (fun s => ae_all_iff.mpr (h s))] with d hd
  intro s t
  linarith [hd s t]
lemma tree_aeterminal : ∀ᵐ d ∂L.terminal, TreeArray d.val := by
  have h (v x y z : DyadicTime) : ∀ᵐ d ∂L.terminal,
      min (d.val.val v x+d.val.val v y-d.val.val x y) (d.val.val v y+d.val.val v z-d.val.val y z)-
      (d.val.val v x+d.val.val v z-d.val.val x z) ≤ 0 := by
    have hc (a b c : DyadicTime) : Continuous (fun d : DistanceArray => d.val a b+d.val a c-d.val b c) :=
      ((continuous_arrayEval a b).add (continuous_arrayEval a c)).sub (continuous_arrayEval b c)
    exact S.sample_constraint_aeterminal L _ (((hc v x y).min (hc v y z)).sub (hc v x z)) 3 (by norm_num)
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
-- module Solutions.OAIQ44_CM.StandardMap_TreeLine
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
lemma realArray_treeLine (d : DistanceArray) (hu : UnitArray d) (ht : TreeArray d) :
    TreeLine (realArray d) :=
  ⟨realArray_nonneg d hu,realArray_symm d hu,realArray_triangle d hu,
    realArray_le d hu,realArray_tree d hu ht⟩
namespace TreeLine
variable {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
include hd
lemma self (x : ℝ) : d x x=0 := by
  have h := hd.unit x x
  simp only [sub_self,abs_zero] at h
  exact le_antisymm h (hd.nonneg _ _)
lemma b_nonneg (v x y : ℝ) : 0 ≤ lineB d v x y := by
  have h := hd.triangle x v y
  rw [hd.symm x v] at h
  dsimp [lineB]; linarith
lemma b_symm (v x y : ℝ) : lineB d v x y=lineB d v y x := by
  unfold lineB; rw [hd.symm x y]; ring
lemma min_b (v x y z : ℝ) : min (lineB d v x y) (lineB d v y z) ≤ lineB d v x z :=
  hd.tree v x y z
lemma b_nonbacktrack (v x u y : ℝ) (hp : 0 < lineB d v x u) (hz : lineB d v u y=0) :
    lineB d v x y=0 := by
  have hb := hd.min_b v u x y
  rw [hd.b_symm v u x,hz] at hb
  have hh := (min_le_iff.mp hb).resolve_left (not_le.mpr hp)
  exact le_antisymm hh (hd.b_nonneg _ _ _)
end TreeLine

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TreeAffine
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
lemma tree_chain_additive {d : ℝ → ℝ → ℝ} (hd : TreeLine d) (x : ℕ → ℝ) (N : ℕ)
    (he : ∀ i, i<N → 0<d (x i) (x (i+1)))
    (ht : ∀ i, i+1<N → d (x i) (x (i+2))=d (x i) (x (i+1))+d (x (i+1)) (x (i+2))) :
    d (x 0) (x N)=∑ i∈Finset.range N,d (x i) (x (i+1)) := by
  suffices hh : ∀ n≤N,d (x 0) (x n)=∑ i∈Finset.range n,d (x i) (x (i+1)) from hh N le_rfl
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro hn; simp [hd.self]
  | one => intro hn; simp
  | more n h0 h1 =>
    intro hn
    have hn0 : n≤N := by omega
    have hn1 : n+1≤N := by omega
    have hD0 := h0 hn0
    have hD1 := h1 hn1
    have hp : 0<lineB d (x (n+1)) (x 0) (x n) := by
      unfold lineB
      rw [hd.symm (x (n+1)) (x 0),hd.symm (x (n+1)) (x n),hD0,hD1,Finset.sum_range_succ]
      linarith [he n (by omega)]
    have hz : lineB d (x (n+1)) (x n) (x (n+2))=0 := by
      unfold lineB
      rw [hd.symm (x (n+1)) (x n),ht n (by omega)]
      ring
    have hB := hd.b_nonbacktrack (x (n+1)) (x 0) (x n) (x (n+2)) hp hz
    unfold lineB at hB
    rw [hd.symm (x (n+1)) (x 0),hD1] at hB
    rw [show n+2=(n+1)+1 by omega,Finset.sum_range_succ]
    linarith
lemma tree_chain_affine {d : ℝ → ℝ → ℝ} (hd : TreeLine d) (x : ℕ → ℝ) (N : ℕ) (w : ℝ)
    (hw : 0≤w) (hx : ∀ i,i<N → x i<x (i+1))
    (he : ∀ i,i<N → d (x i) (x (i+1))=w*(x (i+1)-x i))
    (ht : ∀ i,i+1<N → d (x i) (x (i+2))=w*(x (i+2)-x i)) :
    d (x 0) (x N)=w*(x N-x 0) := by
  by_cases hw0 : w=0
  · have hh : ∀ n≤N,d (x 0) (x n)=0 := by
      intro n
      induction n with
      | zero => intro hn; exact hd.self _
      | succ n ih =>
        intro hn
        have hb := hd.triangle (x 0) (x n) (x (n+1))
        rw [ih (by omega),he n (by omega),hw0,zero_mul] at hb
        exact le_antisymm (by linarith) (hd.nonneg _ _)
    rw [hw0,zero_mul,hh N le_rfl]
  · have hwP : 0<w := lt_of_le_of_ne hw (Ne.symm hw0)
    have hh := tree_chain_additive hd x N (fun i hi => by rw [he i hi]; exact mul_pos hwP (sub_pos.mpr (hx i hi)))
      (fun i hi => by rw [ht i hi,he i (by omega),he (i+1) (by omega)]; ring)
    rw [hh]
    trans ∑ i∈Finset.range N,w*(x (i+1)-x i)
    · apply Finset.sum_congr rfl; intro i hi; exact he i (Finset.mem_range.mp hi)
    rw [← Finset.mul_sum]
    congr 1
    clear hh he ht hx hwP hw0 hw hd d
    induction N with
    | zero => simp
    | succ N IH => rw [Finset.sum_range_succ,IH]; ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TestObservations
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma unitClip_eq {x : ℝ} (hx : x∈Icc (0:ℝ) 1) : unitClip x=x := by
  dsimp [unitClip]; rw [min_eq_right hx.2,max_eq_right hx.1]
lemma testObservation_eq_arrayTest (j : ArrayTestIndex) (d : DistanceArray)
    (h1 : arrayShortfall j.val.1 (dyadicMid j.val.1 j.val.2) d∈Icc (0:ℝ) 1)
    (h2 : arrayShortfall (dyadicMid j.val.1 j.val.2) j.val.2 d∈Icc (0:ℝ) 1) :
    testObservation (fun i => arrayShortfall (testLeft j.val.1 j.val.2 i) (testRight j.val.1 j.val.2 i) d)=arrayTest j d := by
  change arrayShortfall j.val.1 j.val.2 d-
    (arrayShortfall j.val.1 (dyadicMid j.val.1 j.val.2) d+arrayShortfall (dyadicMid j.val.1 j.val.2) j.val.2 d)/2+
    (unitClip (arrayShortfall j.val.1 (dyadicMid j.val.1 j.val.2) d)-unitClip (arrayShortfall (dyadicMid j.val.1 j.val.2) j.val.2 d))^2=_
  rw [unitClip_eq h1,unitClip_eq h2]
  rfl
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ClippedTests
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma unitArray_shortfall_mem (d : DistanceArray) (hd : UnitArray d) (s t : DyadicTime) (hst : (s:ℝ)< (t:ℝ)) :
    arrayShortfall s t d∈Icc (0:ℝ) 1 := by
  have hlen := sub_pos.mpr hst
  have hn := d.property.1 s t
  have hu := hd s t
  rw [abs_of_pos hlen] at hu
  unfold arrayShortfall
  constructor
  · have hh := (div_le_one hlen).mpr hu
    linarith
  · have hh := div_nonneg hn hlen.le
    linarith
lemma clippedTest_unit (j : ArrayTestIndex) (d : DistanceArray) (hd : UnitArray d) : clippedTest j d=arrayTest j d := by
  apply testObservation_eq_arrayTest
  · exact unitArray_shortfall_mem d hd _ _ (by rw [dyadicMid_val]; linarith [j.property])
  · exact unitArray_shortfall_mem d hd _ _ (by rw [dyadicMid_val]; linarith [j.property])
lemma clippedShortfall_unit (d : DistanceArray) (hd : UnitArray d) (s t : DyadicTime) (hst : (s:ℝ)< (t:ℝ)) :
    clippedShortfall s t d=arrayShortfall s t d := unitClip_eq (unitArray_shortfall_mem d hd s t hst)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointObservations
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma testEndpoint_inWindow (j : ArrayTestIndex) (u : DyadicTime) (q : ℕ)
    (hj : intervalInWindow j u q) : (testEndpoint j).inWindow u q := by
  constructor <;> intro i <;> fin_cases i <;>
    dsimp [testEndpoint,testLeft,testRight,dyadicMid,dyadicHalf] <;>
    have hp := j.property <;> have h1 := hj.1 <;> have h2 := hj.2 <;> linarith
lemma shortfallEndpoint_inWindow (j : ArrayTestIndex) (u : DyadicTime) (q : ℕ)
    (hj : intervalInWindow j u q) : (shortfallEndpoint j).inWindow u q := ⟨fun _ => hj.1,fun _ => hj.2⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeExclusions
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (K : S.LimitLaws)
lemma endpoint_bridge_ae (select : Bool) (u v : DyadicTime) (huv : (u:ℝ)<(v:ℝ))
    (W H : EndpointObservation) (q : ℕ) (hq : (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000)
    (hW : W.inWindow u q) (hH : H.inWindow v q) (j : ArrayTestIndex)
    (htest : (∀d,W.value d=clippedTest j d) ∨ (∀d,H.value d=clippedTest j d)) :
    ∀ᵐ d ∂K.selected S select,0< W.value d.val → 0< H.value d.val →
      d.val.val u v≤(999/1000:ℝ)*((v:ℝ)-(u:ℝ)) := by
  have hh (a c : ℚ) : ∀ᵐ d ∂K.selected S select,
      0<(a:ℝ) → 0<(c:ℝ) → ¬ d.val∈endpointBridgeEvent u v W H a c := by
    by_cases ha : 0<(a:ℝ)
    · by_cases hc : 0<(c:ℝ)
      · have hn : ∀ᵐ d ∂K.selected S select,¬d.val∈endpointBridgeEvent u v W H a c :=
          ae_iff.mpr (by simpa only [not_not] using S.endpoint_bridge_null_q44 K select u v huv W H q hq hW hH j htest a c ha hc)
        filter_upwards [hn] with d hd
        exact fun _ _ => hd
      · exact Eventually.of_forall fun d _ hc' => (hc hc').elim
    · exact Eventually.of_forall fun d ha' _ => (ha ha').elim
  filter_upwards [ae_all_iff.mpr (fun a => ae_all_iff.mpr (hh a))] with d hd
  intro hw hh
  obtain ⟨a,ha0,ha⟩ := exists_rat_btwn hw
  obtain ⟨c,hc0,hc⟩ := exists_rat_btwn hh
  by_contra hn
  exact hd a c ha0 hc0 ⟨lt_of_not_ge hn,ha,hc⟩
lemma dyadicBridge_aeselected (select : Bool) : ∀ᵐ d ∂K.selected S select,DyadicBridgeExclusions d.val := by
  have hh (u v : DyadicTime) (q : ℕ) (j l : ArrayTestIndex) (b : Bool) :
      ∀ᵐ d ∂K.selected S select,
      (u:ℝ)<(v:ℝ) → (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000 →
      (bridgeLeft b j l).inWindow u q → (bridgeRight b j l).inWindow v q →
      0<(bridgeLeft b j l).value d.val → 0<(bridgeRight b j l).value d.val →
      d.val.val u v≤(999/1000:ℝ)*((v:ℝ)-(u:ℝ)) := by
    by_cases h : (u:ℝ)<(v:ℝ) ∧ (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000 ∧
        (bridgeLeft b j l).inWindow u q ∧ (bridgeRight b j l).inWindow v q
    · have he : (∀d,(bridgeLeft b j l).value d=clippedTest j d) ∨
          (∀d,(bridgeRight b j l).value d=clippedTest j d) := by
        cases b <;> simp [bridgeLeft,bridgeRight]
      filter_upwards [S.endpoint_bridge_ae K select u v h.1 _ _ q h.2.1 h.2.2.1 h.2.2.2 j he] with d hd
      exact fun _ _ _ _ => hd
    · exact Eventually.of_forall fun d h1 h2 h3 h4 => (h ⟨h1,h2,h3,h4⟩).elim
  exact ae_all_iff.mpr fun u => ae_all_iff.mpr fun v => ae_all_iff.mpr fun q =>
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun l => ae_all_iff.mpr (hh u v q j l)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalMidpointGrid
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
lemma midpoint_grid_affine {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (a b : ℝ) (hab : a< b) (hm : MidpointAffineOn d (Icc a b))
    (N : ℕ) (hN : 0< N) (i j : ℕ) (hi : i≤ N) (hj : j≤ N) :
    d (a+(i:ℝ)*((b-a)/N)) (a+(j:ℝ)*((b-a)/N))=
      (d a b/(b-a))*|(a+(j:ℝ)*((b-a)/N))-(a+(i:ℝ)*((b-a)/N))| := by
  let h : ℝ := (b-a)/N
  let x : ℕ → ℝ := fun i => a+(i:ℝ)*h
  have hNR : (0:ℝ)< N := by exact_mod_cast hN
  have hp : 0< h := div_pos (sub_pos.mpr hab) hNR
  have hx0 : x 0=a := by simp [x]
  have hxN : x N=b := by dsimp [x,h]; field_simp; ring
  have hdiff (i k : ℕ) : x (i+k)-x i=(k:ℝ)*h := by dsimp [x]; push_cast; ring
  have hmem (i : ℕ) (hi : i≤ N) : x i∈Icc a b := by
    have hib : (i:ℝ)≤ N := by exact_mod_cast hi
    have hh := mul_le_mul_of_nonneg_right hib hp.le
    have hi0 : (0:ℝ)≤ i := Nat.cast_nonneg i
    change a+(N:ℝ)*h=b at hxN
    dsimp [x]
    constructor <;> nlinarith
  have hmid (i : ℕ) : (x i+x (i+2))/2=x (i+1) := by dsimp [x]; push_cast; ring
  have halves (i : ℕ) (hi : i+2≤ N) :
      d (x i) (x (i+1))=d (x i) (x (i+2))/2 ∧
      d (x (i+1)) (x (i+2))=d (x i) (x (i+2))/2 := by
    have hh := hm (x i) (hmem i (by omega)) (x (i+2)) (hmem _ hi)
      (by have hh := hdiff i 2; push_cast at hh; linarith)
    simpa only [hmid] using hh
  let c := d (x 0) (x 1)
  have hedge : ∀i,i< N → d (x i) (x (i+1))=c := by
    intro i
    induction i with
    | zero => intro hi; rfl
    | succ i ih =>
      intro hi
      have hh := halves i (by omega)
      have he := ih (by omega)
      simpa only [Nat.succ_eq_add_one,show i+1+1=i+2 by omega] using hh.2.trans (hh.1.symm.trans he)
  let w := c/h
  have hw : 0≤ w := div_nonneg (hd.nonneg _ _) hp.le
  have hwhole (i n : ℕ) (hn : i+n≤ N) : d (x i) (x (i+n))=w*(x (i+n)-x i) := by
    have hh := tree_chain_affine hd (fun k => x (i+k)) n w hw
      (fun k hk => by have hh := hdiff (i+k) 1; push_cast at hh; simpa only [Nat.add_assoc] using (show x (i+k)< x (i+k+1) by linarith))
      (fun k hk => by
        rw [←Nat.add_assoc,hedge (i+k) (by omega),hdiff]
        simp only [Nat.cast_one,one_mul]
        dsimp [w]
        rw [div_mul_cancel₀ _ hp.ne'])
      (fun k hk => by
        have hh := (halves (i+k) (by omega)).1
        rw [hedge (i+k) (by omega)] at hh
        rw [←Nat.add_assoc,hdiff]
        push_cast
        have hc : w*h=c := div_mul_cancel₀ _ hp.ne'
        nlinarith)
    simpa only [Nat.add_zero] using hh
  have hwD : w=d a b/(b-a) := by
    have hh := hwhole 0 N (by omega)
    simp only [Nat.zero_add,hx0,hxN] at hh
    exact (eq_div_iff (sub_ne_zero.mpr hab.ne')).mpr hh.symm
  change d (x i) (x j)=(d a b/(b-a))*|x j-x i|
  wlog hij : i≤ j generalizing i j
  · rw [hd.symm,abs_sub_comm]
    exact this j i hj hi (le_of_not_ge hij)
  have hh := hwhole i (j-i) (by omega)
  rw [Nat.add_sub_of_le hij,hwD] at hh
  rw [abs_of_nonneg (by
    have hh := mul_le_mul_of_nonneg_right (show (i:ℝ)≤ j by exact_mod_cast hij) hp.le
    dsimp [x]; linarith)]
  exact hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalMidpointAffine
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
lemma midpoint_interval_affine {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (fun p : ℝ × ℝ => d p.1 p.2))
    (a b : ℝ) (hab : a< b) (hm : MidpointAffineOn d (Icc a b)) :
    ∀x∈Ioo a b,∀y∈Ioo a b,d x y=(d a b/(b-a))*|y-x| := by
  let f : ℝ → ℝ := fun t => a+t*(b-a)
  have hf : Continuous f := continuous_const.add (continuous_id.mul continuous_const)
  have hgrid (s t : DyadicTime) (hs : (s:ℝ)∈Ioo (0:ℝ) 1) (ht : (t:ℝ)∈Ioo (0:ℝ) 1) :
      d (f s) (f t)=(d a b/(b-a))*|f t-f s| := by
    obtain ⟨m,i,j,hi,hj⟩ := dyadic_common_grid s t
    have hsc : (s:ℝ)=(i:ℝ)/(2:ℝ)^m := by rw [hi,dyadic_zsmul_val,dyadicUnit_val]; ring
    have htc : (t:ℝ)=(j:ℝ)/(2:ℝ)^m := by rw [hj,dyadic_zsmul_val,dyadicUnit_val]; ring
    have hp : (0:ℝ)<(2:ℝ)^m := by positivity
    have hiR : 0≤(i:ℝ) ∧ (i:ℝ)≤(2:ℝ)^m := by
      rw [hsc] at hs
      exact ⟨by simpa only [zero_mul] using (le_div_iff₀ hp).mp hs.1.le,by have := (div_le_one hp).mp hs.2.le; exact this⟩
    have hjR : 0≤(j:ℝ) ∧ (j:ℝ)≤(2:ℝ)^m := by
      rw [htc] at ht
      exact ⟨by simpa only [zero_mul] using (le_div_iff₀ hp).mp ht.1.le,by have := (div_le_one hp).mp ht.2.le; exact this⟩
    have hi0 : 0≤ i := by exact_mod_cast hiR.1
    have hj0 : 0≤ j := by exact_mod_cast hjR.1
    have hiB : i≤((2^m:ℕ):ℤ) := by exact_mod_cast hiR.2
    have hjB : j≤((2^m:ℕ):ℤ) := by exact_mod_cast hjR.2
    have hiN : i.toNat≤2^m := by omega
    have hjN : j.toNat≤2^m := by omega
    have hei : (i.toNat:ℝ)=(i:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hi0
    have hej : (j.toNat:ℝ)=(j:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hj0
    have he1 : f s=a+(i.toNat:ℝ)*((b-a)/(2^m:ℕ)) := by
      dsimp [f]
      rw [hsc,hei]
      push_cast; ring
    have he2 : f t=a+(j.toNat:ℝ)*((b-a)/(2^m:ℕ)) := by
      dsimp [f]
      rw [htc,hej]
      push_cast; ring
    rw [he1,he2]
    exact midpoint_grid_affine hd a b hab hm (2^m) (by positivity) i.toNat j.toNat hiN hjN
  have hall : ∀ s t : ℝ,s∈Ioo (0:ℝ) 1 → t∈Ioo (0:ℝ) 1 →
      d (f s) (f t)=(d a b/(b-a))*|f t-f s| := by
    apply isClosed_property2 (p := fun s t => s∈Ioo (0:ℝ) 1 → t∈Ioo (0:ℝ) 1 →
      d (f s) (f t)=(d a b/(b-a))*|f t-f s|) dyadicTime_dense
    · apply isClosed_imp (isOpen_Ioo.preimage continuous_fst)
      apply isClosed_imp (isOpen_Ioo.preimage continuous_snd)
      exact isClosed_eq (hc.comp ((hf.comp continuous_fst).prodMk (hf.comp continuous_snd)))
        (continuous_const.mul (((hf.comp continuous_snd).sub (hf.comp continuous_fst)).abs))
    · exact hgrid
  intro x hx y hy
  let s := (x-a)/(b-a)
  let t := (y-a)/(b-a)
  have hs : s∈Ioo (0:ℝ) 1 := ⟨div_pos (sub_pos.mpr hx.1) (sub_pos.mpr hab),
    (div_lt_one (sub_pos.mpr hab)).mpr (by linarith [hx.2])⟩
  have ht : t∈Ioo (0:ℝ) 1 := ⟨div_pos (sub_pos.mpr hy.1) (sub_pos.mpr hab),
    (div_lt_one (sub_pos.mpr hab)).mpr (by linarith [hy.2])⟩
  have hfx : f s=x := by dsimp [f,s]; rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]; ring
  have hfy : f t=y := by dsimp [f,t]; rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]; ring
  simpa only [hfx,hfy] using hall s t hs ht
lemma midpoint_ball_locallyAffine {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (fun p : ℝ × ℝ => d p.1 p.2)) (x r : ℝ) (hr : 0< r)
    (hm : MidpointAffineOn d (ball x r)) : ∃w,LocallyAffineAt d x w := by
  let a := x-r/2
  let b := x+r/2
  have hab : a< b := by dsimp [a,b]; linarith
  have hI : Icc a b⊆ball x r := by
    intro y hy
    rw [mem_ball,Real.dist_eq,abs_lt]
    dsimp [a,b] at hy
    constructor <;> linarith [hy.1,hy.2]
  have hs : MidpointAffineOn d (Icc a b) := fun s hs t ht hst => hm s (hI hs) t (hI ht) hst
  have hh := midpoint_interval_affine hd hc a b hab hs
  refine ⟨d a b/(b-a),r/2,by positivity,?_⟩
  intro u hu v hv
  have hu' : u∈Ioo a b := by simpa only [Real.ball_eq_Ioo] using hu
  have hv' : v∈Ioo a b := by simpa only [Real.ball_eq_Ioo] using hv
  exact hh u hu' v hv'
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalTestDetection
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
lemma local_zero_tests_midpoint (d : DistanceArray) (hu : UnitArray d) (x r : ℝ)
    (hz : ∀ j : ArrayTestIndex,(j.val.1:ℝ)∈ball x r → (j.val.2:ℝ)∈ball x r → arrayTest j d=0) :
    MidpointAffineOn (realArray d) (ball x r) := by
  have hc := continuous_realArray d hu
  have hm : Continuous (fun p : ℝ × ℝ => (p.1+p.2)/2) := (continuous_fst.add continuous_snd).div_const 2
  have hh : ∀s t : ℝ,s∈ball x r → t∈ball x r → s< t →
      realArray d s ((s+t)/2)=realArray d s t/2 ∧
      realArray d ((s+t)/2) t=realArray d s t/2 := by
    apply isClosed_property2 (p := fun s t => s∈ball x r → t∈ball x r → s< t →
      realArray d s ((s+t)/2)=realArray d s t/2 ∧
      realArray d ((s+t)/2) t=realArray d s t/2) dyadicTime_dense
    · apply isClosed_imp (isOpen_ball.preimage continuous_fst)
      apply isClosed_imp (isOpen_ball.preimage continuous_snd)
      apply isClosed_imp (isOpen_lt continuous_fst continuous_snd)
      exact (isClosed_eq (hc.comp (continuous_fst.prodMk hm)) (hc.div_const 2)).inter
        (isClosed_eq (hc.comp (hm.prodMk continuous_snd)) (hc.div_const 2))
    · intro s t hs ht hst
      have hh := array_zero_test_halves s t hst d (hz ⟨(s,t),hst⟩ hs ht)
      change realArray d (s:ℝ) (dyadicMid s t:ℝ)=realArray d (s:ℝ) (t:ℝ)/2 ∧
        realArray d (dyadicMid s t:ℝ) (t:ℝ)=realArray d (s:ℝ) (t:ℝ)/2
      simpa only [realArray_coe d hu] using hh
  exact fun s hs t ht hst => hh s t hs ht hst
lemma local_positive_test (d : DistanceArray) (hu : UnitArray d) (ht : TreeArray d)
    (x : ℝ) (hx : ¬∃w,LocallyAffineAt (realArray d) x w) (r : ℝ) (hr : 0< r) :
    ∃ j : ArrayTestIndex,(j.val.1:ℝ)∈ball x r ∧ (j.val.2:ℝ)∈ball x r ∧ 0< arrayTest j d := by
  by_contra hn
  have hz : ∀j : ArrayTestIndex,(j.val.1:ℝ)∈ball x r → (j.val.2:ℝ)∈ball x r → arrayTest j d=0 := by
    intro j hs ht'
    exact le_antisymm (le_of_not_gt (fun hj => hn ⟨j,hs,ht',hj⟩)) (arrayTest_nonneg j d)
  exact hx (midpoint_ball_locallyAffine (realArray_treeLine d hu ht) (continuous_realArray d hu) x r hr
    (local_zero_tests_midpoint d hu x r hz))
lemma local_positive_shortfall (d : DistanceArray) (hu : UnitArray d)
    (x : ℝ) (hx : ¬LocallyAffineAt (realArray d) x 1) (r : ℝ) (hr : 0< r) :
    ∃j : ArrayTestIndex,(j.val.1:ℝ)∈ball x r ∧ (j.val.2:ℝ)∈ball x r ∧ 0< arrayShortfall j.val.1 j.val.2 d := by
  by_contra hn
  have hz (s t : DyadicTime) (hs : (s:ℝ)∈ball x r) (ht : (t:ℝ)∈ball x r) (hst : (s:ℝ)<(t:ℝ)) :
      d.val s t=(t:ℝ)-(s:ℝ) := by
    have h := le_of_not_gt (fun h : 0< arrayShortfall s t d => hn ⟨⟨(s,t),hst⟩,hs,ht,h⟩)
    have hlow : (t:ℝ)-(s:ℝ)≤ d.val s t := by
      unfold arrayShortfall at h
      have hh : 1≤ d.val s t/((t:ℝ)-(s:ℝ)) := by linarith
      simpa only [one_mul] using (le_div_iff₀ (sub_pos.mpr hst)).mp hh
    have hhigh := hu s t
    rw [abs_of_pos (sub_pos.mpr hst)] at hhigh
    exact le_antisymm hhigh hlow
  have hc := continuous_realArray d hu
  have hall : ∀s t : ℝ,s∈ball x r → t∈ball x r → s< t → realArray d s t=t-s := by
    apply isClosed_property2 (p := fun s t => s∈ball x r → t∈ball x r → s< t → realArray d s t=t-s) dyadicTime_dense
    · apply isClosed_imp (isOpen_ball.preimage continuous_fst)
      apply isClosed_imp (isOpen_ball.preimage continuous_snd)
      apply isClosed_imp (isOpen_lt continuous_fst continuous_snd)
      exact isClosed_eq hc (continuous_snd.sub continuous_fst)
    · intro s t hs ht hst
      simpa only [realArray_coe d hu] using hz s t hs ht hst
  apply hx
  refine ⟨r,hr,?_⟩
  intro s hs t ht
  rw [one_mul]
  rcases lt_trichotomy s t with hst|hst|hst
  · rw [abs_of_pos (sub_pos.mpr hst)]
    exact hall s t hs ht hst
  · subst t; rw [realArray_self d hu,sub_self,abs_zero]
  · rw [realArray_symm d hu,abs_of_neg (sub_neg.mpr hst),hall t s ht hs hst]
    ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RealBridge
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma interval_window_of_near (j : ArrayTestIndex) (u : DyadicTime) (q : ℕ) (x : ℝ)
    (hu : dist (u:ℝ) x<((1:ℝ)/(2:ℝ)^q)/4)
    (hs : (j.val.1:ℝ)∈ball x (((1:ℝ)/(2:ℝ)^q)/4))
    (ht : (j.val.2:ℝ)∈ball x (((1:ℝ)/(2:ℝ)^q)/4)) : intervalInWindow j u q := by
  have h0 : (0:ℝ)<1/(2:ℝ)^q := by positivity
  rw [Real.dist_eq,abs_lt] at hu
  rw [mem_ball,Real.dist_eq,abs_lt] at hs ht
  constructor <;> linarith [hu.1,hu.2,hs.1,hs.2,ht.1,ht.2]
lemma dyadicBridge_real_sorted (d : DistanceArray) (hu : UnitArray d) (ht : TreeArray d)
    (hb : DyadicBridgeExclusions d) (s t : ℝ) (hst : s< t)
    (hpq : ((¬∃w,LocallyAffineAt (realArray d) s w) ∧ ¬LocallyAffineAt (realArray d) t 1) ∨
      ((¬LocallyAffineAt (realArray d) s 1) ∧ ¬∃w,LocallyAffineAt (realArray d) t w)) :
    realArray d s t≤(999/1000:ℝ)*(t-s) := by
  by_contra hn
  have hf : (999/1000:ℝ)*(t-s)< realArray d s t := lt_of_not_ge hn
  have ho : IsOpen {p : ℝ×ℝ | (999/1000:ℝ)*(p.2-p.1)< realArray d p.1 p.2} :=
    isOpen_lt (continuous_const.mul (continuous_snd.sub continuous_fst)) (continuous_realArray d hu)
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp ho (s,t) hf
  have hz : Tendsto (fun q : ℕ => (1:ℝ)/(2:ℝ)^q) atTop (𝓝 0) := by
    simpa only [div_pow,one_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  obtain ⟨q,hqδ,hqgap⟩ := ((hz.eventually (gt_mem_nhds hδ)).and
    (hz.eventually (gt_mem_nhds (show (0:ℝ)<(t-s)/4000 by linarith)))).exists
  let ρ : ℝ := 1/(2:ℝ)^q
  have hρ : 0< ρ := by dsimp [ρ]; positivity
  change ρ< δ at hqδ
  change ρ<(t-s)/4000 at hqgap
  obtain ⟨u,hu'⟩ := denseRange_dyadicTime.exists_dist_lt s (show 0< ρ/4 by positivity)
  obtain ⟨v,hv'⟩ := denseRange_dyadicTime.exists_dist_lt t (show 0< ρ/4 by positivity)
  have hu' : dist (u:ℝ) s< ρ/4 := by rwa [dist_comm]
  have hv' : dist (v:ℝ) t< ρ/4 := by rwa [dist_comm]
  have hfast : (999/1000:ℝ)*((v:ℝ)-(u:ℝ))< d.val u v := by
    have hh := hball (show ((u:ℝ),(v:ℝ))∈ball (s,t) δ by
      rw [mem_ball,Prod.dist_eq,max_lt_iff]
      exact ⟨hu'.trans (by linarith),hv'.trans (by linarith)⟩)
    change (999/1000:ℝ)*((v:ℝ)-(u:ℝ)) < realArray d (u:ℝ) (v:ℝ) at hh
    simpa only [realArray_coe d hu] using hh
  have huabs := abs_lt.mp (show |(u:ℝ)-s|< ρ/4 by simpa only [Real.dist_eq] using hu')
  have hvabs := abs_lt.mp (show |(v:ℝ)-t|< ρ/4 by simpa only [Real.dist_eq] using hv')
  have huv : (u:ℝ)<(v:ℝ) := by linarith [huabs.1,huabs.2,hvabs.1,hvabs.2]
  have hq : (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000 := by
    change ρ≤_
    linarith [huabs.1,huabs.2,hvabs.1,hvabs.2]
  rcases hpq with ⟨hs,ht'⟩|⟨hs,ht'⟩
  · obtain ⟨j,hjs,hjt,hj⟩ := local_positive_test d hu ht s hs (ρ/4) (by positivity)
    obtain ⟨l,hls,hlt,hl⟩ := local_positive_shortfall d hu t ht' (ρ/4) (by positivity)
    have hju := testEndpoint_inWindow j u q (interval_window_of_near j u q s hu' hjs hjt)
    have hlv := shortfallEndpoint_inWindow l v q (interval_window_of_near l v q t hv' hls hlt)
    have hh := hb u v q j l true huv hq hju hlv
      (by simpa only [bridgeLeft,ite_eq_left,testEndpoint_value,clippedTest_unit j d hu] using hj)
      (by simpa only [bridgeRight,ite_eq_left,shortfallEndpoint_value,clippedShortfall_unit d hu _ _ l.property] using hl)
    exact (not_lt_of_ge hh) hfast
  · obtain ⟨l,hls,hlt,hl⟩ := local_positive_shortfall d hu s hs (ρ/4) (by positivity)
    obtain ⟨j,hjs,hjt,hj⟩ := local_positive_test d hu ht t ht' (ρ/4) (by positivity)
    have hlu := shortfallEndpoint_inWindow l u q (interval_window_of_near l u q s hu' hls hlt)
    have hjv := testEndpoint_inWindow j v q (interval_window_of_near j v q t hv' hjs hjt)
    have hh := hb u v q j l false huv hq hlu hjv
      (by simpa only [bridgeLeft,Bool.false_eq_true,ite_false,shortfallEndpoint_value,clippedShortfall_unit d hu _ _ l.property] using hl)
      (by simpa only [bridgeRight,Bool.false_eq_true,ite_false,testEndpoint_value,clippedTest_unit j d hu] using hj)
    exact (not_lt_of_ge hh) hfast
lemma dyadicBridge_real_slowPair (d : DistanceArray) (hu : UnitArray d) (ht : TreeArray d)
    (hb : DyadicBridgeExclusions d) : SlowPair (realArray d) (999/1000) := by
  intro s t hs ht'
  rcases lt_trichotomy s t with hst|hst|hst
  · rw [abs_of_pos (sub_pos.mpr hst)]
    exact dyadicBridge_real_sorted d hu ht hb s t hst (Or.inl ⟨hs,ht'⟩)
  · subst t; simp only [realArray_self d hu,sub_self,abs_zero,mul_zero,le_refl]
  · rw [realArray_symm d hu,abs_sub_comm,abs_of_pos (sub_pos.mpr hst)]
    exact dyadicBridge_real_sorted d hu ht hb t s hst (Or.inr ⟨ht',hs⟩)
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (K : S.LimitLaws)
lemma slowPair_aeterminal_q44_oai : ∀ᵐd ∂K.terminal,SlowPair (realArray d.val) (999/1000) := by
  filter_upwards [S.unit_aeterminal K,S.tree_aeterminal K,S.dyadicBridge_aeselected K false] with d hu ht hb
  exact dyadicBridge_real_slowPair d.val hu ht hb
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.CriticalScaleSequence.slowPair_aeterminal_q44_oai := @OAI.StandardMapEntropy.CriticalScaleSequence.slowPair_aeterminal_q44_oai
