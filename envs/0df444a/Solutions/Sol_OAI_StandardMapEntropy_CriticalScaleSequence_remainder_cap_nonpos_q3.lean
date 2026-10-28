-- Prove2me | solution 1 for OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_nonpos_q3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T04:50:33.020501+00:00
-- url     : https://prove2.me/submissions/bc768937-7139-48ba-a750-fa3e317b9454

import Mathlib
import Definitions.Def_StandardMapLyapunov
import Definitions.Def_OAIQ3St000
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_noCancellation_aemulti_q3
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_remainder_cap_band_q3
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_remainder_dilate_q3
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_remainder_shape_q3
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_remainder_translate_q3
import Theorems.Thm_OAI_StandardMapEntropy_bandMoment_order_q3

section
-- module Solutions.OAIQ3_Std.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

theorem measurePreserving_standardMap (k : ℝ) : MeasurePreserving (standardMap k) area area := by
  unfold area
  have hkick : MeasurePreserving
      (fun z : Torus => (z.1, z.2 + kick k z.1))
        ((volume : Measure Circle).prod volume) (volume.prod volume) := by
    refine (MeasurePreserving.id (volume : Measure Circle)).skew_product
      (g := fun x y : Circle => y + kick k x) ?_ ?_
    · exact measurable_snd.add ((continuous_kick k).measurable.comp measurable_fst)
    · exact Filter.Eventually.of_forall (fun x => map_add_right_eq_self volume (kick k x))
  convert (measurePreserving_add_prod (volume : Measure Circle) volume).comp hkick using 1
  funext z
  simp only [Function.comp_apply, standardMap, kick]
  congr 1
  abel

lemma recurrenceCoordinates_involutive : Function.Involutive recurrenceCoordinates := by
  intro z
  apply Prod.ext <;> simp [recurrenceCoordinates]

lemma standardMap_conjugacy (k : ℝ) (z : Torus) :
    recurrenceCoordinates (standardMap k z) =
      recurrenceMap k (recurrenceCoordinates z) := by
  apply Prod.ext <;> simp only [recurrenceCoordinates, recurrenceMap, standardMap, kick, two_smul]
  · abel
  · abel

open scoped Matrix.Norms.Operator

open Filter
open scoped Topology

open Metric

end StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_PlaneGeometry
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
-- module Solutions.OAIQ3_Std.StandardMap_PlaneTransfer
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
-- module Solutions.OAIQ3_Std.StandardMap_SegmentObservations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma liftShortfall_mem (k : ℝ) (hk : 0 ≤ k) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) (hn : 0 < n) :
    liftShortfall k z a n ∈ Icc 0 1 := by
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hp : 0 < Real.log (growthBase k) := Real.log_pos hM
  have hnp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨hlo,hhi⟩ := liftSegmentTransfer_norm_bounds k hk z a n
  have hlog0 : 0 ≤ Real.log ‖liftSegmentTransfer k z a n‖ := Real.log_nonneg hlo
  have hlog1 : Real.log ‖liftSegmentTransfer k z a n‖ ≤ (n:ℝ)*Real.log (growthBase k) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by linarith) hhi
  unfold liftShortfall
  constructor
  · have := (div_le_one (mul_pos hnp hp)).mpr hlog1; linarith
  · have := div_nonneg hlog0 (mul_pos hnp hp).le; linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_TorusDynamics
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
lemma measurePreserving_torusStep (k : ℝ) : MeasurePreserving (torusStep k) area area := by
  have hh := measurePreserving_recurrenceCoordinates.comp
    ((measurePreserving_standardMap k).comp measurePreserving_recurrenceCoordinates)
  convert hh using 1
  funext z
  simp only [Function.comp_apply,standardMap_conjugacy,torusStep_apply]
  rw [recurrenceCoordinates_involutive z]
lemma measurePreserving_torusStep_symm (k : ℝ) : MeasurePreserving (torusStep k).symm area area :=
  (measurePreserving_torusStep k).symm (torusStep_measurableEquiv k)
lemma measurePreserving_torusIter (k : ℝ) (i : ℤ) : MeasurePreserving (torusIter k i) area area := by
  cases i with
  | ofNat n =>
      change MeasurePreserving (torusIter k (n : ℤ)) area area
      simpa only [torusIter,zpow_natCast,Equiv.Perm.coe_pow] using (measurePreserving_torusStep k).iterate n
  | negSucc n => simpa only [torusIter,zpow_negSucc,← inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow] using
      (measurePreserving_torusStep_symm k).iterate (n+1)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_TorusObservations
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
lemma continuous_torusShortfall (k : ℝ) (hk : 0 ≤ k) (a : ℤ) (n : ℕ) :
    Continuous (fun z => torusShortfall k z a n) := by
  apply continuous_const.sub
  apply Continuous.div_const
  exact (continuous_torusSegmentTransfer k a n).norm.log
    (fun z => by have := (torusSegmentTransfer_norm_bounds k hk z a n).1; linarith)
lemma torusShortfall_mem (k : ℝ) (hk : 0 ≤ k) (z : Torus) (a : ℤ) (n : ℕ) (hn : 0 < n) :
    torusShortfall k z a n ∈ Icc 0 1 := by
  obtain ⟨w,rfl⟩ := liftProjection_surjective z
  rw [torusShortfall_lift]
  exact liftShortfall_mem k hk w a n hn
lemma torusShortfall_shift (k : ℝ) (z : Torus) (a b : ℤ) (n : ℕ) :
    torusShortfall k (torusIter k b z) a n=torusShortfall k z (a+b) n := by
  have he : torusSegmentCoefficient k (torusIter k b z) a=torusSegmentCoefficient k z (a+b) := by
    funext i
    unfold torusSegmentCoefficient
    rw [← torusIter_add]
    congr 3
    ring
  simp only [torusShortfall,torusSegmentTransfer,he]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_FourPoint
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
-- module Solutions.OAIQ3_Std.StandardMap_ProductDistances
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
-- module Solutions.OAIQ3_Std.StandardMap_SmoothCap
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
lemma capSlope_bounds (u : ℝ) : 0≤ capSlope u ∧ capSlope u≤1 := by
  unfold capSlope
  constructor <;> linarith [Real.smoothTransition.le_one (10000*u-1),Real.smoothTransition.nonneg (10000*u-1)]
lemma capSlope_one {u : ℝ} (hu : u≤1/10000) : capSlope u=1 := by
  unfold capSlope
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; ring
lemma capSlope_zero {u : ℝ} (hu : 1/5000≤ u) : capSlope u=0 := by
  unfold capSlope
  rw [Real.smoothTransition.one_of_one_le (by linarith)]; ring
lemma capPrimitive_hasDerivAt (u : ℝ) : HasDerivAt capPrimitive (capSlope u) u := by
  exact intervalIntegral.integral_hasDerivAt_right (capSlope_continuous.intervalIntegrable 0 u)
    (capSlope_continuous.stronglyMeasurableAtFilter volume (𝓝 u)) capSlope_continuous.continuousAt
lemma capPrimitive_deriv : deriv capPrimitive=capSlope := funext (fun u => (capPrimitive_hasDerivAt u).deriv)
lemma capPrimitive_contDiff : ContDiff ℝ 2 capPrimitive := by
  suffices ContDiff ℝ ((1 : WithTop ℕ∞)+1) capPrimitive by (convert this using 1; norm_num)
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun u => (capPrimitive_hasDerivAt u).differentiableAt,?_,?_⟩
  · norm_num
  · rw [capPrimitive_deriv]
    exact capSlope_contDiff.of_le (by norm_num)
lemma capPrimitive_monotone : Monotone capPrimitive := by
  intro x y hxy
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (capSlope_continuous.intervalIntegrable 0 x) (capSlope_continuous.intervalIntegrable x y)
  have h0 := intervalIntegral.integral_nonneg (μ := volume) hxy (fun t _ => (capSlope_bounds t).1)
  change (∫ t in (0:ℝ)..x,capSlope t)≤(∫ t in (0:ℝ)..y,capSlope t)
  linarith
lemma capPrimitive_linear {u : ℝ} (hu : u≤1/10000) : capPrimitive u=u := by
  unfold capPrimitive
  have he : (∫ t in (0:ℝ)..u,capSlope t)=(∫ _t in (0:ℝ)..u,(1:ℝ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply capSlope_one
    rw [mem_uIcc] at ht
    rcases ht with ⟨h0,h1⟩|⟨h0,h1⟩ <;> linarith
  rw [he,intervalIntegral.integral_const]
  simp
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
lemma capBase_bounds : (1/10000:ℝ)≤ capBase ∧ capBase≤1/5000 := by
  constructor
  · have hh := capPrimitive_monotone (by norm_num : (1/10000:ℝ)≤1/5000)
    rwa [capPrimitive_linear (by norm_num : (1/10000:ℝ)≤1/10000)] at hh
  · unfold capBase capPrimitive
    calc
      (∫ t in (0:ℝ)..(1/5000:ℝ),capSlope t)≤∫ _t in (0:ℝ)..(1/5000:ℝ),(1:ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num) (capSlope_continuous.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
        exact fun t _ => (capSlope_bounds t).2
      _=1/5000 := by simp
lemma entropyCap_contDiff (α : ℝ) : ContDiff ℝ 2 (entropyCap α) := by
  unfold entropyCap
  exact (contDiff_const.mul capPrimitive_contDiff).add
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)))
lemma entropyCap_linear {α u : ℝ} (hu : u≤1/10000) : entropyCap α u=α*u := by
  unfold entropyCap
  rw [capPrimitive_linear hu,Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring
lemma entropyCap_one {α u : ℝ} (hu : 3/10000≤ u) : entropyCap α u=1 := by
  unfold entropyCap
  rw [capPrimitive_constant (by linarith),Real.smoothTransition.one_of_one_le (by linarith)]
  ring
lemma entropyCap_monotone {α : ℝ} (hα : 0≤α) (hα1 : α≤1) : Monotone (entropyCap α) := by
  have hc : 0≤1-α*capBase := by nlinarith [capBase_bounds.1,capBase_bounds.2]
  intro x y hxy
  unfold entropyCap
  exact add_le_add (mul_le_mul_of_nonneg_left (capPrimitive_monotone hxy) hα)
    (mul_le_mul_of_nonneg_left (Real.smoothTransition.monotone (by linarith)) hc)
lemma entropyCap_bounds {α u : ℝ} (hα : 0≤α) (hα1 : α≤1) (hu : u∈Icc (0:ℝ) 1) :
    0≤ entropyCap α u ∧ entropyCap α u≤1 := by
  have h0 := entropyCap_monotone hα hα1 hu.1
  have h1 := entropyCap_monotone hα hα1 hu.2
  rw [entropyCap_linear (by norm_num),mul_zero] at h0
  rw [entropyCap_one (u := 1) (by norm_num)] at h1
  exact ⟨h0,h1⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_SmoothControl
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
lemma c2_deriv_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (deriv f) := by
  apply ContDiff.deriv'
  convert! hf using 1
lemma c2_compact_bounds {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (a b : ℝ) :
    ∃C≥0,(∀x∈Icc a b,|deriv f x|≤C) ∧ (∀x∈Icc a b,|deriv (deriv f) x|≤C) := by
  obtain ⟨C1,h1⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuous_deriv (by norm_num)).continuousOn (s := Icc a b)
  obtain ⟨C2,h2⟩ := isCompact_Icc.exists_bound_of_continuousOn ((c2_deriv_contDiff hf).continuous_deriv_one).continuousOn (s := Icc a b)
  refine ⟨max 0 (max C1 C2),le_max_left _ _,?_,?_⟩
  · intro x hx
    exact (h1 x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro x hx
    exact (h2 x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
lemma deriv_bound_lipschitz {f : ℝ → ℝ} (hf : Differentiable ℝ f) {a b C x y : ℝ}
    (hb : ∀u∈Icc a b,|deriv f u|≤C) (hx : x∈Icc a b) (hy : y∈Icc a b) :
    |f y-f x|≤C*|y-x| := by
  exact Convex.norm_image_sub_le_of_norm_deriv_le (fun u _ => hf u) hb (convex_Icc _ _) hx hy
lemma c2_remainder_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b C x z : ℝ} (hC : 0≤C)
    (hb : ∀u∈Icc a b,|deriv (deriv f) u|≤C) (hx : x∈Icc a b) (hz : z∈Icc a b) :
    |f x-f z-deriv f z*(x-z)|≤C*(x-z)^2 := by
  have hsub : uIcc z x⊆Icc a b := by
    intro u hu
    rw [mem_uIcc] at hu
    rcases hu with ⟨hzu,hux⟩|⟨hxu,huz⟩
    · exact ⟨hz.1.trans hzu,hux.trans hx.2⟩
    · exact ⟨hx.1.trans hxu,huz.trans hz.2⟩
  let R : ℝ → ℝ := fun u => f u-f z-deriv f z*(u-z)
  have hd (u : ℝ) : HasDerivAt R (deriv f u-deriv f z) u := by
    convert! (((hf.differentiable (by norm_num) u).hasDerivAt.sub_const (f z)).sub
      (((hasDerivAt_id u).sub_const z).const_mul (deriv f z))) using 1 ; simp
  have hR : ∀u∈uIcc z x,|deriv R u|≤C*|x-z| := by
    intro u hu
    rw [(hd u).deriv]
    have h1 := deriv_bound_lipschitz hf.differentiable_deriv_two hb hz (hsub hu)
    have hu' : |u-z|≤|x-z| := by
      rw [mem_uIcc] at hu
      rcases hu with ⟨hzu,hux⟩|⟨hxu,huz⟩
      · rw [abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]; linarith
    exact h1.trans (mul_le_mul_of_nonneg_left hu' hC)
  have hr := Convex.norm_image_sub_le_of_norm_deriv_le (fun u _ => (hd u).differentiableAt)
    hR (convex_uIcc z x) (left_mem_uIcc) (right_mem_uIcc)
  change |R x-R z|≤(C*|x-z|)*|x-z| at hr
  have he : R z=0 := by dsimp [R]; ring
  rw [he,sub_zero,mul_assoc,←pow_two, sq_abs] at hr
  exact hr
lemma c2_midpoint_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b C x y : ℝ} (hC : 0≤C)
    (hb : ∀u∈Icc a b,|deriv (deriv f) u|≤C) (hx : x∈Icc a b) (hy : y∈Icc a b) :
    |f ((x+y)/2)-(f x+f y)/2|≤(C/4)*(x-y)^2 := by
  have hm : (x+y)/2∈Icc a b := ⟨by linarith [hx.1,hy.1],by linarith [hx.2,hy.2]⟩
  have h1 := c2_remainder_bound hf hC hb hx hm
  have h2 := c2_remainder_bound hf hC hb hy hm
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1,h1.2,h2.1,h2.2]
lemma c2_capped_difference {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b C x y z : ℝ} (hC : 0≤C)
    (h1 : ∀u∈Icc a b,|deriv f u|≤C) (h2 : ∀u∈Icc a b,|deriv (deriv f) u|≤C)
    (hx : x∈Icc a b) (hy : y∈Icc a b) (hz : z∈Icc a b) (hJ : 0≤z-(x+y)/2) :
    |f z-(f x+f y)/2|≤C*((z-(x+y)/2)+(x-y)^2) := by
  have hm : (x+y)/2∈Icc a b := ⟨by linarith [hx.1,hy.1],by linarith [hx.2,hy.2]⟩
  have hh := deriv_bound_lipschitz (hf.differentiable (by norm_num)) h1 hm hz
  rw [abs_of_nonneg hJ] at hh
  have ht := c2_midpoint_bound hf hC h2 hx hy
  have htri := abs_add_le (f z-f ((x+y)/2)) (f ((x+y)/2)-(f x+f y)/2)
  rw [sub_add_sub_cancel] at htri
  nlinarith [mul_nonneg hC (sq_nonneg (x-y))]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_MeanDeficit
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
lemma integral_torusIter (k : ℝ) (a : ℤ) (f : Torus → ℝ) :
    (∫ z, f (torusIter k a z) ∂area)=∫ z, f z ∂area :=
  (measurePreserving_torusIter k a).integral_comp (torusIterMeasurableEquiv k a).measurableEmbedding f
lemma integrable_productDistance (k : ℝ) (hk : 0 ≤ k) (i j : ℤ) :
    Integrable (fun z => productDistance k z i j) area :=
  (continuous_productDistance k hk i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma integral_productDistance_bounds (k : ℝ) (hk : 0 ≤ k) (n : ℕ) :
    0 ≤ (∫ z, productDistance k z 0 (n:ℤ) ∂area) ∧ (∫ z, productDistance k z 0 (n:ℤ) ∂area) ≤ (n:ℝ) := by
  refine ⟨integral_nonneg (fun z => productDistance_nonneg k hk z 0 (n:ℤ)),?_⟩
  have hh := integral_mono (integrable_productDistance k hk 0 (n:ℤ)) (integrable_const (n:ℝ)) (fun z => by simpa using productDistance_le k hk z 0 (n:ℤ))
  simpa only [Int.cast_natCast,Int.cast_zero,sub_zero,Nat.abs_cast,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using hh
lemma meanDeficit_bounds (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0<n) : 0 ≤ meanDeficit k n ∧ meanDeficit k n ≤ 1 := by
  obtain ⟨h0,h1⟩ := integral_productDistance_bounds k hk n
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  have hdiv : (∫ z, productDistance k z 0 (n:ℤ) ∂area)/(n:ℝ) ≤ 1 := (div_le_one hnp).mpr h1
  have hdiv0 := div_nonneg h0 hnp.le
  unfold meanDeficit; constructor <;> linarith
lemma integral_distance_shift (k : ℝ) (i j a : ℤ) :
    (∫ z,productDistance k z (i+a) (j+a) ∂area)=∫ z,productDistance k z i j ∂area := by
  calc
    _ = ∫ z,productDistance k (torusIter k a z) i j ∂area := by simp only [productDistance_shift]
    _ = _ := by convert! integral_torusIter k a (fun z => productDistance k z i j) using 1
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_MeanGrowth
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
lemma meanLoss_nonneg (k : ℝ) (hk : 0 ≤ k) (n : ℕ) : 0 ≤ meanLoss k n :=
  sub_nonneg.mpr (integral_productDistance_bounds k hk n).2
lemma meanLoss_eq (k : ℝ) (n : ℕ) : meanLoss k n=(n:ℝ)*meanDeficit k n := by
  cases n with
  | zero => simp [meanLoss,meanDeficit]
  | succ n => unfold meanLoss meanDeficit; field_simp
lemma meanLoss_superadditive (k : ℝ) (hk : 0 ≤ k) (n m : ℕ) :
    meanLoss k n+meanLoss k m ≤ meanLoss k (n+m) := by
  have hi := integral_mono (integrable_productDistance k hk 0 ((n+m:ℕ):ℤ))
    ((integrable_productDistance k hk 0 (n:ℤ)).add (integrable_productDistance k hk (n:ℤ) ((n+m:ℕ):ℤ)))
    (fun z => productDistance_triangle k hk z 0 (n:ℤ) ((n+m:ℕ):ℤ))
  have he : (∫ z,productDistance k z 0 (n:ℤ)+productDistance k z (n:ℤ) ((n+m:ℕ):ℤ) ∂area)=
      (∫ z,productDistance k z 0 (n:ℤ) ∂area)+(∫ z,productDistance k z 0 (m:ℤ) ∂area) := by
    rw [integral_add (integrable_productDistance k hk 0 _) (integrable_productDistance k hk _ _)]
    congr 1
    simpa only [zero_add,add_zero,Nat.cast_add,add_comm] using integral_distance_shift k 0 (m:ℤ) (n:ℤ)
  simp only [Pi.add_apply] at hi
  rw [he] at hi
  unfold meanLoss
  simp only [Nat.cast_add] at hi ⊢
  linarith
lemma meanLoss_mono (k : ℝ) (hk : 0 ≤ k) : Monotone (meanLoss k) := by
  intro n m hnm
  have hh := meanLoss_superadditive k hk n (m-n)
  rw [Nat.add_sub_of_le hnm] at hh
  linarith [meanLoss_nonneg k hk (m-n)]
lemma meanDeficit_comparison (k : ℝ) (hk : 0 ≤ k) (n m : ℕ) (hnm : n ≤ m) :
    (n:ℝ)*meanDeficit k n ≤ (m:ℝ)*meanDeficit k m := by
  simpa only [← meanLoss_eq] using meanLoss_mono k hk hnm
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_FixedDeficit
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
lemma meanDeficit_eq_integral_shortfall (k : ℝ) (hk : 0≤k) (n : ℕ) :
    meanDeficit k n=∫ z,torusShortfall k z 0 n ∂area := by
  have he (z : Torus) : torusShortfall k z 0 n=1-productDistance k z 0 (n:ℤ)/(n:ℝ) := by
    have hh := productDistance_forward k z 0 n
    simp only [zero_add] at hh
    rw [hh]
    unfold torusShortfall
    ring
  simp_rw [he]
  rw [integral_sub (integrable_const _) ((integrable_productDistance k hk 0 _).div_const _),integral_div]
  simp [meanDeficit]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CriticalSequence
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local
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
-- module Solutions.OAIQ3_Std.StandardMap_ArrayTests
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma continuous_arrayShortfall (s t : DyadicTime) : Continuous (arrayShortfall s t) :=
  continuous_const.sub ((continuous_arrayEval s t).div_const _)
lemma continuous_arrayJ (s t : DyadicTime) : Continuous (arrayJ s t) :=
  (continuous_arrayShortfall s t).sub (((continuous_arrayShortfall s (dyadicMid s t)).add
    (continuous_arrayShortfall (dyadicMid s t) t)).div_const 2)
lemma continuous_arrayV (s t : DyadicTime) : Continuous (arrayV s t) :=
  ((continuous_arrayShortfall s (dyadicMid s t)).sub (continuous_arrayShortfall (dyadicMid s t) t)).pow 2
lemma arrayV_nonneg (s t : DyadicTime) (d : DistanceArray) : 0≤arrayV s t d := sq_nonneg _
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ArrayAffinity
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma continuous_arrayTest (i : ArrayTestIndex) : Continuous (arrayTest i) :=
  (continuous_arrayJ _ _).add (continuous_arrayV _ _)
lemma arrayTest_nonneg (i : ArrayTestIndex) (d : DistanceArray) : 0 ≤ arrayTest i d :=
  add_nonneg (arrayJ_nonneg _ _ i.property d) (arrayV_nonneg _ _ d)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_RescaledArrays
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma rescaledDistance_aligned (k : ℝ) (z : Torus) (n : ℕ) (s t : DyadicTime) (a b : ℤ)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(b:ℝ)) :
    rescaledDistance k z n s t=productDistance k z a b/(n:ℝ) := by
  simp only [rescaledDistance,hs,ht,Int.floor_intCast]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_SampleLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma shortfall_sample_aligned (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) (hn : 0<n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+(m:ℝ)) :
    arrayShortfall s t (sampleArray k hk z n hn)=torusShortfall k z a m := by
  have hni : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hlen : (t:ℝ)-(s:ℝ)=(m:ℝ)/(n:ℝ) := (eq_div_iff hni).mpr (by nlinarith)
  unfold arrayShortfall
  change 1-rescaledDistance k z n s t/((t:ℝ)-(s:ℝ))=_
  rw [rescaledDistance_aligned k z n s t a (a+(m:ℤ)) hs (by simpa only [Int.cast_add,Int.cast_natCast] using ht),hlen,
    productDistance_forward]
  unfold torusShortfall
  field_simp
lemma integral_shortfall_sample (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+(m:ℝ)) :
    (∫ d,arrayShortfall s t d ∂sampleLaw k hk n hn)=meanDeficit k m := by
  rw [integral_sampleLaw k hk n hn _ (continuous_arrayShortfall s t)]
  simp_rw [shortfall_sample_aligned k hk _ n hn s t a m hm hs ht]
  have he (z : Torus) : torusShortfall k z a m=torusShortfall k (torusIter k a z) 0 m := by
    rw [torusShortfall_shift,zero_add]
  simp_rw [he]
  rw [integral_torusIter k a (fun z => torusShortfall k z 0 m),← meanDeficit_eq_integral_shortfall k hk m]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ArrayMoments
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma meanSquareDeficit_bounds (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0 < n) :
    0 ≤ meanSquareDeficit k n ∧ meanSquareDeficit k n ≤ meanDeficit k n := by
  refine ⟨integral_nonneg (fun z => sq_nonneg _),?_⟩
  rw [meanDeficit_eq_integral_shortfall k hk n]
  apply integral_mono
  · exact ((continuous_torusShortfall k hk 0 n).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (continuous_torusShortfall k hk 0 n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro z
    have h := torusShortfall_mem k hk z 0 n hn
    nlinarith [h.1,h.2]
lemma integrable_arrayShortfall (μ : Measure DistanceArray) [IsFiniteMeasure μ] (s t : DyadicTime) :
    Integrable (arrayShortfall s t) μ :=
  (continuous_arrayShortfall s t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma integrable_arrayShortfall_sq (μ : Measure DistanceArray) [IsFiniteMeasure μ] (s t : DyadicTime) :
    Integrable (fun d => (arrayShortfall s t d)^2) μ :=
  ((continuous_arrayShortfall s t).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma integral_shortfall_sq_sample (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0 < n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+(m:ℝ)) :
    (∫ d,(arrayShortfall s t d)^2 ∂sampleLaw k hk n hn)=meanSquareDeficit k m := by
  rw [integral_sampleLaw k hk n hn (fun d => (arrayShortfall s t d)^2) ((continuous_arrayShortfall s t).pow 2)]
  simp_rw [shortfall_sample_aligned k hk _ n hn s t a m hm hs ht]
  have he (z : Torus) : torusShortfall k z a m=torusShortfall k (torusIter k a z) 0 m := by
    rw [torusShortfall_shift,zero_add]
  simp_rw [he]
  exact integral_torusIter k a (fun z => (torusShortfall k z 0 m)^2)
lemma integral_J_sample (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0 < n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ)) :
    (∫ d,arrayJ s t d ∂sampleLaw k hk n hn)=meanDeficit k (m+m)-meanDeficit k m := by
  have hmid : (n:ℝ)*(dyadicMid s t:ℝ)=(a:ℝ)+(m:ℝ) := by rw [dyadicMid_val]; nlinarith
  have hwhole := integral_shortfall_sample k hk n hn s t a (m+m) (by omega) hs (by simpa only [Nat.cast_add,two_mul] using ht)
  have hl := integral_shortfall_sample k hk n hn s (dyadicMid s t) a m hm hs hmid
  have hr := integral_shortfall_sample k hk n hn (dyadicMid s t) t (a+(m:ℤ)) m hm
    (by simpa only [Int.cast_add,Int.cast_natCast] using hmid) (by push_cast; linarith)
  have hadd : (∫ d,arrayShortfall s (dyadicMid s t) d+arrayShortfall (dyadicMid s t) t d ∂sampleLaw k hk n hn)=
      (∫ d,arrayShortfall s (dyadicMid s t) d ∂sampleLaw k hk n hn)+
        (∫ d,arrayShortfall (dyadicMid s t) t d ∂sampleLaw k hk n hn) := by
    convert! integral_add (integrable_arrayShortfall (sampleLaw k hk n hn) s (dyadicMid s t)) (integrable_arrayShortfall (sampleLaw k hk n hn) (dyadicMid s t) t) using 1
  have hsub : (∫ d,arrayJ s t d ∂sampleLaw k hk n hn)=
      (∫ d,arrayShortfall s t d ∂sampleLaw k hk n hn)-
        (∫ d,(arrayShortfall s (dyadicMid s t) d+arrayShortfall (dyadicMid s t) t d)/2 ∂sampleLaw k hk n hn) := by
    convert! integral_sub (integrable_arrayShortfall (sampleLaw k hk n hn) s t)
      (((integrable_arrayShortfall (sampleLaw k hk n hn) s (dyadicMid s t)).add (integrable_arrayShortfall (sampleLaw k hk n hn) (dyadicMid s t) t)).div_const 2) using 1
  rw [hsub,integral_div,hadd,hwhole,hl,hr]
  ring
lemma scalar_variance_test {a b c : ℝ} (ha : a∈Icc 0 1) (hb : b∈Icc 0 1)
    (hc : c∈Icc 0 1) (hJ : 0 ≤ c-(a+b)/2) :
    (a-b)^2/4 ≤ (a^2+b^2)/2-c^2+2*(c-(a+b)/2) ∧ (a-b)^2 ≤ a+b ∧ c-(a+b)/2 ≤ c := by
  have hab : 0 ≤ a*b := mul_nonneg ha.1 hb.1
  have hca : (a+b)/2 ≤ c := by linarith
  have hbar : 0 ≤ (a+b)/2 := by linarith [ha.1,hb.1]
  have hcc : 0 ≤ (c-(a+b)/2)*(2-c-(a+b)/2) := mul_nonneg hJ (by linarith [hc.2])
  refine ⟨by nlinarith,by nlinarith [ha.1,ha.2,hb.1,hb.2],by linarith⟩
lemma integral_V_sample_bound (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0 < n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ)) :
    (∫ d,arrayV s t d ∂sampleLaw k hk n hn)/4 ≤
      meanSquareDeficit k m-meanSquareDeficit k (m+m)+2*(meanDeficit k (m+m)-meanDeficit k m) := by
  let μ := sampleLaw k hk n hn
  have : IsProbabilityMeasure μ := sampleLawProbability k hk n hn
  have hmid : (n:ℝ)*(dyadicMid s t:ℝ)=(a:ℝ)+(m:ℝ) := by rw [dyadicMid_val]; nlinarith
  have hwhole : (n:ℝ)*(t:ℝ)=(a:ℝ)+((m+m:ℕ):ℝ) := by push_cast; linarith
  have hrstart : (n:ℝ)*(dyadicMid s t:ℝ)=((a+(m:ℤ):ℤ):ℝ) := by simpa only [Int.cast_add,Int.cast_natCast] using hmid
  have hrend : (n:ℝ)*(t:ℝ)=((a+(m:ℤ):ℤ):ℝ)+(m:ℝ) := by push_cast; linarith
  have hslt : (s:ℝ) < (t:ℝ) := by
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    have hmR : (0:ℝ) < m := by exact_mod_cast hm
    nlinarith
  let F : DistanceArray → ℝ := fun d =>
    ((arrayShortfall s (dyadicMid s t) d)^2+(arrayShortfall (dyadicMid s t) t d)^2)/2-
      (arrayShortfall s t d)^2+2*arrayJ s t d
  have hF : Continuous F := by
    exact ((((continuous_arrayShortfall s _).pow 2).add ((continuous_arrayShortfall _ t).pow 2)).div_const 2).sub
      ((continuous_arrayShortfall s t).pow 2) |>.add (continuous_const.mul (continuous_arrayJ s t))
  have hb (z : Torus) : arrayV s t (sampleArray k hk z n hn)/4 ≤ F (sampleArray k hk z n hn) := by
    have ha := torusShortfall_mem k hk z a m hm
    have hb := torusShortfall_mem k hk z (a+(m:ℤ)) m hm
    have hcc := torusShortfall_mem k hk z a (m+m) (by omega)
    rw [← shortfall_sample_aligned k hk z n hn s (dyadicMid s t) a m hm hs hmid] at ha
    rw [← shortfall_sample_aligned k hk z n hn (dyadicMid s t) t (a+(m:ℤ)) m hm hrstart hrend] at hb
    rw [← shortfall_sample_aligned k hk z n hn s t a (m+m) (by omega) hs hwhole] at hcc
    exact (scalar_variance_test ha hb hcc (arrayJ_nonneg s t hslt _)).1
  have hi := integral_mono (μ := area)
    (((continuous_arrayV s t).comp (continuous_sampleArray k hk n hn)).div_const 4 |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hF.comp (continuous_sampleArray k hk n hn)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hb
  simp only [Function.comp_apply] at hi
  rw [integral_div,← integral_sampleLaw k hk n hn _ (continuous_arrayV s t),← integral_sampleLaw k hk n hn F hF] at hi
  have hEval : (∫ d,F d ∂μ)=meanSquareDeficit k m-meanSquareDeficit k (m+m)+2*(meanDeficit k (m+m)-meanDeficit k m) := by
    have h1 : (∫ d,F d ∂μ)=
        (∫ d,((arrayShortfall s (dyadicMid s t) d)^2+(arrayShortfall (dyadicMid s t) t d)^2)/2-(arrayShortfall s t d)^2 ∂μ)+
          (∫ d,2*arrayJ s t d ∂μ) := by
      convert! integral_add
        ((((integrable_arrayShortfall_sq μ s (dyadicMid s t)).add (integrable_arrayShortfall_sq μ (dyadicMid s t) t)).div_const 2).sub (integrable_arrayShortfall_sq μ s t))
        (((continuous_arrayJ s t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul 2) using 1
    have h2 : (∫ d,((arrayShortfall s (dyadicMid s t) d)^2+(arrayShortfall (dyadicMid s t) t d)^2)/2-(arrayShortfall s t d)^2 ∂μ)=
        (∫ d,((arrayShortfall s (dyadicMid s t) d)^2+(arrayShortfall (dyadicMid s t) t d)^2)/2 ∂μ)-
          (∫ d,(arrayShortfall s t d)^2 ∂μ) := by
      convert! integral_sub (((integrable_arrayShortfall_sq μ s (dyadicMid s t)).add (integrable_arrayShortfall_sq μ (dyadicMid s t) t)).div_const 2) (integrable_arrayShortfall_sq μ s t) using 1
    have h3 : (∫ d,(arrayShortfall s (dyadicMid s t) d)^2+(arrayShortfall (dyadicMid s t) t d)^2 ∂μ)=
        (∫ d,(arrayShortfall s (dyadicMid s t) d)^2 ∂μ)+(∫ d,(arrayShortfall (dyadicMid s t) t d)^2 ∂μ) := by
      convert! integral_add (integrable_arrayShortfall_sq μ s (dyadicMid s t)) (integrable_arrayShortfall_sq μ (dyadicMid s t) t) using 1
    rw [h1,h2,integral_div,h3,integral_const_mul]
    change ((∫ d,(arrayShortfall s (dyadicMid s t) d)^2 ∂sampleLaw k hk n hn)+
      (∫ d,(arrayShortfall (dyadicMid s t) t d)^2 ∂sampleLaw k hk n hn))/2-
      (∫ d,(arrayShortfall s t d)^2 ∂sampleLaw k hk n hn)+2*(∫ d,arrayJ s t d ∂sampleLaw k hk n hn)=_
    rw [integral_shortfall_sq_sample k hk n hn s (dyadicMid s t) a m hm hs hmid,
      integral_shortfall_sq_sample k hk n hn (dyadicMid s t) t (a+(m:ℤ)) m hm hrstart hrend,
      integral_shortfall_sq_sample k hk n hn s t a (m+m) (by omega) hs hwhole,
      integral_J_sample k hk n hn s t a m hm hs ht]
    ring
  exact hi.trans_eq hEval
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ScaleLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
-- module Solutions.OAIQ3_Std.StandardMap_ScaleTelescopes
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
lemma sum_successive_difference (f : ℕ → ℝ) (p l : ℕ) :
    (∑ i∈Finset.range l,(f (p+i+1)-f (p+i)))=f (p+l)-f p := by
  induction l with
  | zero => simp
  | succ l ih => rw [Finset.sum_range_succ,ih]; simp only [Nat.add_assoc]; ring
lemma sum_variance_telescope (e q J V : ℕ → ℝ) (p l : ℕ)
    (hq0 : ∀ n,0≤q n) (hqe : ∀ n,q n≤e n) (he0 : ∀ n,0≤e n)
    (hJ : ∀ n,J n=e (n+1)-e n)
    (hV : ∀ n,V n/4≤q n-q (n+1)+2*(e (n+1)-e n)) :
    (∑ i∈Finset.range l,(J (p+i)+V (p+i)))≤9*e (p+l) := by
  have hj : (∑ i∈Finset.range l,J (p+i))=e (p+l)-e p := by
    simp_rw [hJ]
    exact sum_successive_difference e p l
  have hv : (∑ i∈Finset.range l,V (p+i))/4≤q p-q (p+l)+2*(e (p+l)-e p) := by
    have hh := Finset.sum_le_sum (s := Finset.range l) (fun i hi => hV (p+i))
    rw [← Finset.sum_div] at hh
    have hr : (∑ i∈Finset.range l,(q (p+i)-q (p+i+1)+2*(e (p+i+1)-e (p+i))))=
        q p-q (p+l)+2*(e (p+l)-e p) := by
      have hrev : (∑ i∈Finset.range l,(q (p+i)-q (p+i+1)))= -(∑ i∈Finset.range l,(q (p+i+1)-q (p+i))) := by
        rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i hi; ring
      rw [Finset.sum_add_distrib,hrev,← Finset.mul_sum,sum_successive_difference,sum_successive_difference]
      ring
    rwa [hr] at hh
  rw [Finset.sum_add_distrib,hj]
  nlinarith [hq0 (p+l),hqe p,he0 p]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ScaleTestBounds
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma dyadic_aligned_eventually (s : DyadicTime) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p₀≤p → ∃ a : ℤ, ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ) := by
  obtain ⟨p₀,a,ha⟩ := dyadicTime_mem s
  refine ⟨p₀,fun p hp => ⟨a*2^(p-p₀),?_⟩⟩
  push_cast
  have he : (2:ℝ)^p=(2:ℝ)^p₀*2^(p-p₀) := by rw [← pow_add,Nat.add_sub_of_le hp]
  rw [ha,he]
  field_simp
lemma dyadic_interval_aligned_eventually (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p₀≤p → ∃ a : ℤ, ∃ m : ℕ, 0 < m ∧
      ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ) ∧ ((2^p:ℕ):ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ) := by
  obtain ⟨p₁,hp₁⟩ := dyadic_aligned_eventually s
  obtain ⟨p₂,hp₂⟩ := dyadic_aligned_eventually (dyadicMid s t)
  refine ⟨max p₁ p₂,?_⟩
  intro p hp
  obtain ⟨a,ha⟩ := hp₁ p ((le_max_left _ _).trans hp)
  obtain ⟨b,hb⟩ := hp₂ p ((le_max_right _ _).trans hp)
  rw [dyadicMid_val] at hb
  have hpR : (0:ℝ)<(2^p:ℕ) := by positivity
  have hab : a<b := by exact_mod_cast (show (a:ℝ)<(b:ℝ) by nlinarith)
  let m := (b-a).toNat
  have hm : 0 < m := by omega
  have he : (m:ℝ)=(b:ℝ)-(a:ℝ) := by
    rw [show (m:ℝ)=((b-a).toNat:ℝ) from rfl,← Int.cast_natCast,Int.toNat_of_nonneg (sub_nonneg.mpr hab.le)]
    push_cast; rfl
  exact ⟨a,m,hm,ha,by rw [he]; nlinarith⟩
lemma aligned_times_scale (p i : ℕ) (s t : DyadicTime) (a : ℤ) (m : ℕ)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ))
    (ht : ((2^p:ℕ):ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ)) :
    ((2^(p+i):ℕ):ℝ)*(s:ℝ)=((a*2^i:ℤ):ℝ) ∧
    ((2^(p+i):ℕ):ℝ)*(t:ℝ)=((a*2^i:ℤ):ℝ)+2*((m*2^i:ℕ):ℝ) := by
  push_cast at hs ht ⊢
  rw [pow_add]
  constructor
  · calc
      _ = (((2:ℝ)^p)*(s:ℝ))*(2:ℝ)^i := by ring
      _ = _ := by rw [hs]
  · calc
      _ = (((2:ℝ)^p)*(t:ℝ))*(2:ℝ)^i := by ring
      _ = _ := by rw [ht]; ring
lemma integral_test_scalelaw (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) (hε : 0<ε)
    (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ)) (ht : ((2^p:ℕ):ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ)) :
    (∫ d,arrayTest ⟨(s,t),hst⟩ d ∂scaleLaw k hk p l ε)≤9*meanDeficit k (m*2^l)/ε := by
  let e : ℕ → ℝ := fun i => meanDeficit k (m*2^i)
  let q : ℕ → ℝ := fun i => meanSquareDeficit k (m*2^i)
  let J : ℕ → ℝ := fun i => ∫ d,arrayJ s t d ∂sampleLaw k hk (2^(p+i)) (by positivity)
  let V : ℕ → ℝ := fun i => ∫ d,arrayV s t d ∂sampleLaw k hk (2^(p+i)) (by positivity)
  have hnext (i : ℕ) : m*2^(i+1)=m*2^i+m*2^i := by rw [pow_succ]; ring
  have hJ (i : ℕ) : J i=e (i+1)-e i := by
    have hal := aligned_times_scale p i s t a m hs ht
    have hh := integral_J_sample k hk (2^(p+i)) (by positivity) s t (a*2^i) (m*2^i) (by positivity) hal.1 hal.2
    exact hh.trans (by rw [← hnext])
  have hV (i : ℕ) : V i/4≤q i-q (i+1)+2*(e (i+1)-e i) := by
    have hal := aligned_times_scale p i s t a m hs ht
    have hh := integral_V_sample_bound k hk (2^(p+i)) (by positivity) s t (a*2^i) (m*2^i) (by positivity) hal.1 hal.2
    simpa only [← hnext] using hh
  have hh := sum_variance_telescope e q J V 0 l
    (fun i => (meanSquareDeficit_bounds k hk (m*2^i) (by positivity)).1)
    (fun i => (meanSquareDeficit_bounds k hk (m*2^i) (by positivity)).2)
    (fun i => (meanDeficit_bounds k hk (m*2^i) (by positivity)).1) hJ hV
  simp only [Nat.zero_add] at hh
  rw [integral_scaleLaw k hk p l ε hε _ (continuous_arrayTest _)]
  apply (div_le_div_iff_of_pos_right hε).mpr
  have hi (i : ℕ) : (∫ d,arrayTest ⟨(s,t),hst⟩ d ∂sampleLaw k hk (2^(p+i)) (by positivity))=J i+V i := by
    convert! integral_add (μ := sampleLaw k hk (2^(p+i)) (by positivity)) ((continuous_arrayJ s t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((continuous_arrayV s t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) using 1
  simp_rw [hi]
  exact hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CriticalLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma meanDeficit_ratio (k : ℝ) (hk : 0≤k) (n m : ℕ) (hn : 0 < n) (hnm : n ≤ m) :
    meanDeficit k n ≤ ((m:ℝ)/(n:ℝ))*meanDeficit k m := by
  have hh := meanDeficit_comparison k hk n m hnm
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show (0:ℝ)<n by exact_mod_cast hn)).mpr
  nlinarith
lemma dyadic_aligned_deficit_bound (k : ℝ) (hk : 0≤k) (p l H : ℕ)
    (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ)) (ht : ((2^p:ℕ):ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ))
    (hH : (t:ℝ)-(s:ℝ)≤2^(H+1)) :
    meanDeficit k (m*2^l) ≤ (2^(H+1)/((t:ℝ)-(s:ℝ)))*meanDeficit k (2^(p+l+H)) := by
  have hlen : ((t:ℝ)-(s:ℝ))*(2:ℝ)^p=2*(m:ℝ) := by push_cast at hs ht; nlinarith
  have hlen0 : 0<(t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  have hratio : (((2^(p+l+H):ℕ):ℝ)/((m*2^l:ℕ):ℝ))=(2:ℝ)^(H+1)/((t:ℝ)-(s:ℝ)) := by
    push_cast
    apply (div_eq_div_iff (by positivity) hlen0.ne').mpr
    rw [pow_add,pow_add,pow_succ]
    nlinarith [congrArg (fun x : ℝ => x*((2:ℝ)^l*(2:ℝ)^H)) hlen]
  have hn : m*2^l≤2^(p+l+H) := by
    have hR : (m:ℝ)*2^l≤2^(p+l+H) := by
      rw [pow_add,pow_add]
      have hh := mul_le_mul_of_nonneg_right hH (show (0:ℝ)≤2^p by positivity)
      rw [pow_succ] at hh
      have hmH : (m:ℝ)≤2^p*2^H := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hmH (show (0:ℝ)≤2^l by positivity)]
    exact_mod_cast hR
  exact (meanDeficit_ratio k hk (m*2^l) (2^(p+l+H)) (by positivity) hn).trans_eq (by rw [hratio])
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
lemma multiLaw_test_bound (j : ArrayTestIndex) :
    ∃ C : ℝ, ∀ᶠ i in atTop, (∫ d,arrayTest j d ∂S.multiLaw i)≤C := by
  rcases j with ⟨⟨s,t⟩,hst⟩
  obtain ⟨p₀,hp₀⟩ := dyadic_interval_aligned_eventually s t hst
  obtain ⟨H,hH⟩ := pow_unbounded_of_one_lt ((t:ℝ)-(s:ℝ)) (by norm_num : (1:ℝ)<2)
  have hH' : (t:ℝ)-(s:ℝ)≤(2:ℝ)^(H+1) := hH.le.trans (by rw [pow_succ]; nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) H])
  let R : ℝ := 2^(H+1)/((t:ℝ)-(s:ℝ))
  have hR : 0<R := div_pos (by positivity) (sub_pos.mpr hst)
  refine ⟨18*R*(2*doublingConstant)^H,?_⟩
  filter_upwards [S.lowerExponent_tendsto.eventually_ge_atTop p₀] with i hi
  obtain ⟨a,m,hm,hs,ht⟩ := hp₀ _ hi
  have hb := integral_test_scalelaw (S.parameter i) (S.positive i).le (criticalLowerExponent S.offset i)
    (S.exponent i-criticalLowerExponent S.offset i) (S.epsilon i) (S.epsilon_pos i) s t hst a m hm hs ht
  have hh := dyadic_aligned_deficit_bound (S.parameter i) (S.positive i).le (criticalLowerExponent S.offset i)
    (S.exponent i-criticalLowerExponent S.offset i) H s t hst a m hm hs ht hH'
  rw [Nat.add_sub_of_le (S.lower_lt i).le] at hh
  have hterm := S.terminal i H
  have heps := S.epsilon_pos i
  change _ ≤ R*meanDeficit (S.parameter i) (2^(S.exponent i+H)) at hh
  have hl := hh.trans (mul_le_mul_of_nonneg_left hterm hR.le)
  apply hb.trans
  apply (div_le_iff₀ heps).mpr
  change 9*meanDeficit (S.parameter i) (m*2^(S.exponent i-criticalLowerExponent S.offset i))≤_
  change _ ≤ R*(2*(2*doublingConstant)^H*S.epsilon i) at hl
  nlinarith
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_NonaffineLimits
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal CompactlySupported Classical
namespace StandardMapEntropy
lemma integral_nonaffinePart_le (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (F : DistanceArray → ℝ) (hF : Continuous F) (hF0 : ∀ d,0≤F d) :
    (∫ d : NonAffineArray,F d.val ∂nonaffinePart μ)≤∫ d,F d ∂μ := by
  have he : (∫ d : NonAffineArray,F d.val ∂nonaffinePart μ)=∫ d in affineLocusᶜ,F d ∂μ := by
    convert! integral_subtype_comap isClosed_affineLocus.isOpen_compl.measurableSet F using 1
  rw [he]
  exact setIntegral_le_integral (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (Filter.Eventually.of_forall hF0)
lemma integrable_nonaffinePart (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (F : DistanceArray → ℝ) (hF : Continuous F) : Integrable (fun d : NonAffineArray => F d.val) (nonaffinePart μ) := by
  have hi := (hF.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)).restrict (s := affineLocusᶜ)
  rw [← map_comap_subtype_coe isClosed_affineLocus.isOpen_compl.measurableSet,
    (MeasurableEmbedding.subtype_coe isClosed_affineLocus.isOpen_compl.measurableSet).integrable_map_iff] at hi
  exact hi
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ArrayActions
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
-- module Solutions.OAIQ3_Std.StandardMap_VagueSupport
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
-- module Solutions.OAIQ3_Std.StandardMap_RealArrays
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
-- module Solutions.OAIQ3_Std.StandardMap_ArrayLimitSupport
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
-- module Solutions.OAIQ3_Std.StandardMap_ArrayHalf
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_VagueBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma lintegral_le_of_cc_le {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X] [RegularSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (f : X → ℝ) (hf : Continuous f)
    (h0 : ∀ x,0 ≤ f x) (C : ℝ)
    (hb : ∀ g : C_c(X,ℝ),(∀ x,0 ≤ g x) → (∀ x,g x ≤ f x) → (∫ x,g x ∂μ) ≤ C) :
    (∫⁻ x,ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  have hcompact (K : Set X) (hK : IsCompact K) : ν K ≤ ENNReal.ofReal C := by
    obtain ⟨⟨b,hbc⟩,hbK,hbZ,hbs,hbr⟩ := exists_continuous_one_zero_of_isCompact
      hK isClosed_empty (disjoint_empty K)
    let g : C_c(X,ℝ) := ⟨⟨fun x => b x*f x,hbc.mul hf⟩,hbs.mul_right⟩
    have hg0 : ∀ x,0 ≤ g x := fun x => mul_nonneg (hbr x).1 (h0 x)
    have hgf : ∀ x,g x ≤ f x := fun x => by
      change b x*f x ≤ f x
      exact mul_le_of_le_one_left (h0 x) (hbr x).2
    have hge : ∀ x∈K,g x=f x := by intro x hx; change b x*f x=f x; have he : b x=1 := hbK hx; rw [he]; simp
    have hm : ν K ≤ ∫⁻ x,ENNReal.ofReal (g x) ∂μ := by
      rw [withDensity_apply _ hK.isClosed.measurableSet]
      rw [← lintegral_indicator hK.isClosed.measurableSet]
      apply lintegral_mono
      intro x
      by_cases hx : x∈K
      · simp only [Set.indicator_of_mem hx,hge x hx,le_refl]
      · simp only [Set.indicator_of_notMem hx]; exact bot_le
    have hi : Integrable (fun x => g x) μ := g.continuous.integrable_of_hasCompactSupport (μ := μ) g.hasCompactSupport
    rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => g x) hi (Eventually.of_forall hg0)] at hm
    exact hm.trans (ENNReal.ofReal_le_ofReal (hb g hg0 hgf))
  let : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => (hcompact K hK).trans_lt ENNReal.ofReal_lt_top⟩
  have hv : ν univ ≤ ENNReal.ofReal C := by
    rw [isOpen_univ.measure_eq_iSup_isCompact ν]
    simp only [iSup_le_iff]
    intro K hKU hK
    exact hcompact K hK
  simpa only [ν,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] using hv
lemma vague_integrable_bound {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X] [RegularSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
    (l : Filter ι) [l.NeBot] (μ : ι → Measure X) [∀ i,IsFiniteMeasureOnCompacts (μ i)]
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (hconv : ∀ g : C_c(X,ℝ), Tendsto (fun i => ∫ x,g x ∂μ i) l (𝓝 (∫ x,g x ∂ν)))
    (f : X → ℝ) (hf : Continuous f) (h0 : ∀ x,0 ≤ f x) (C : ℝ) (hC : 0 ≤ C)
    (hi : ∀ i,Integrable f (μ i)) (hb : ∀ᶠ i in l,(∫ x,f x ∂μ i)≤C) :
    Integrable f ν ∧ (∫ x,f x ∂ν) ≤ C := by
  have hb' : ∀ g : C_c(X,ℝ),(∀ x,0 ≤ g x) → (∀ x,g x ≤ f x) → (∫ x,g x ∂ν) ≤ C := by
    intro g hg hgf
    apply le_of_tendsto (hconv g)
    filter_upwards [hb] with i hiC
    exact (integral_mono (g.continuous.integrable_of_hasCompactSupport (μ := μ i) g.hasCompactSupport)
      (hi i) hgf).trans hiC
  have hbL := lintegral_le_of_cc_le ν f hf h0 C hb'
  have hif : HasFiniteIntegral f ν := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)).mpr
    (hbL.trans_lt ENNReal.ofReal_lt_top)
  have hiv : Integrable f ν := ⟨hf.aestronglyMeasurable,hif⟩
  refine ⟨hiv,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hiv (Eventually.of_forall h0)] at hbL
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hbL
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_LimitMoments
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
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma test_integrable_multi (j : ArrayTestIndex) :
    Integrable (fun d : NonAffineArray => arrayTest j d.val) L.multi := by
  obtain ⟨C,hC⟩ := S.multiLaw_test_bound j
  exact (vague_integrable_bound L.filter (fun i => nonaffinePart (S.multiLaw i)) L.multi L.multi_converges
    _ ((continuous_arrayTest j).comp continuous_subtype_val) (fun d => arrayTest_nonneg j d.val)
    (max C 0) (le_max_right _ _) (fun i => integrable_nonaffinePart _ _ (continuous_arrayTest j))
    (by filter_upwards [L.refines hC] with i hi
        exact (integral_nonaffinePart_le _ _ (continuous_arrayTest j) (arrayTest_nonneg j)).trans
          (hi.trans (le_max_left _ _)))).1
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_RemainderLaws
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
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_TerminalShortfall
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
lemma shortfall_unit_mem (d : DistanceArray) (hu : UnitArray d) (s t : DyadicTime)
    (hst : (s:ℝ)<(t:ℝ)) : arrayShortfall s t d∈Icc (0:ℝ) 1 := by
  have hl : 0<(t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  have hb := hu s t
  rw [abs_of_pos hl] at hb
  have h0 := d.property.1 s t
  unfold arrayShortfall
  constructor
  · have hh := (div_le_one hl).mpr hb; linarith
  · have hh := div_nonneg h0 hl.le; linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CappedTests
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
lemma dyadicMid_zero_two : dyadicMid 0 (dyadicInt 2)=dyadicInt 1 := by
  apply Subtype.ext; norm_num
lemma continuous_capG (α : ℝ) : Continuous (capG α) := by
  unfold capG
  exact ((entropyCap_contDiff α).continuous.comp (continuous_arrayShortfall _ _)).sub
    ((((entropyCap_contDiff α).continuous.comp (continuous_arrayShortfall _ _)).add
      ((entropyCap_contDiff α).continuous.comp (continuous_arrayShortfall _ _))).div_const 2)
lemma shortfall_ambient_mem (d : DistanceArray) (s t : DyadicTime) (hst : 1≤(t:ℝ)-(s:ℝ)) :
    arrayShortfall s t d∈Icc (-2:ℝ) 1 := by
  have hlen : 0<(t:ℝ)-(s:ℝ) := by linarith
  have hh := d.property.2.2.2.2 s t
  rw [abs_of_pos hlen] at hh
  have hl : d.val s t/((t:ℝ)-(s:ℝ))≤3 := (div_le_iff₀ hlen).mpr (by linarith)
  have hu := div_nonneg (d.property.1 s t) hlen.le
  unfold arrayShortfall
  constructor <;> linarith
lemma capG_bound (α : ℝ) : ∃C≥0,∀d:DistanceArray,|capG α d|≤C*arrayTest coreTestIndex d := by
  obtain ⟨C,hC,h1,h2⟩ := c2_compact_bounds (entropyCap_contDiff α) (-2) 1
  refine ⟨C,hC,?_⟩
  intro d
  have hm := arrayJ_nonneg 0 (dyadicInt 2) (by norm_num) d
  simp only [arrayJ,dyadicMid_zero_two] at hm
  have hh := c2_capped_difference (entropyCap_contDiff α) hC h1 h2
    (shortfall_ambient_mem d 0 (dyadicInt 1) (by norm_num))
    (shortfall_ambient_mem d (dyadicInt 1) (dyadicInt 2) (by norm_num))
    (shortfall_ambient_mem d 0 (dyadicInt 2) (by norm_num)) hm
  simpa only [capG,arrayTest,coreTestIndex,arrayJ,arrayV,dyadicMid_zero_two] using hh
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma capG_integrable_multi (α : ℝ) : Integrable (fun d : NonAffineArray => capG α d.val) L.multi := by
  obtain ⟨C,hC,hb⟩ := capG_bound α
  exact ((S.test_integrable_multi L coreTestIndex).const_mul C).mono'
    ((continuous_capG α).comp continuous_subtype_val).aestronglyMeasurable
    (Eventually.of_forall (fun d => by simpa only [Real.norm_eq_abs] using hb d.val))
lemma capG_integrable_remainder (α : ℝ) : Integrable (fun d : NonAffineArray => capG α d.val) (S.remainderLaw L) :=
  (S.capG_integrable_multi L α).mono_measure (S.remainder_le L)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_FineMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace StandardMapEntropy
lemma shortfall_translate (d:DistanceArray) (s t r:DyadicTime) :
    arrayShortfall s t (arrayTranslate r d)=arrayShortfall (s+r) (t+r) d := by
  unfold arrayShortfall
  change 1-d.val (s+r) (t+r)/((t:ℝ)-(s:ℝ))=1-d.val (s+r) (t+r)/(((t:ℝ)+(r:ℝ))-((s:ℝ)+(r:ℝ)))
  rw [add_sub_add_right_eq_sub]
lemma integral_invariant_translation (μ:Measure NonAffineArray) (r:DyadicTime)
    (ht:μ.map (nonaffineTranslation r)=μ) (f:NonAffineArray→ℝ) (hf:Measurable f) :
    (∫d,f (nonaffineTranslation r d) ∂μ)=∫d,f d ∂μ := by
  rw [←integral_map (nonaffineTranslation r).continuous.measurable.aemeasurable hf.aestronglyMeasurable,ht]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_EndpointDefinition
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
    (h : d.val s t≠|(t:ℝ)-(s:ℝ)|) : ((min (s:ℝ) (t:ℝ)):EReal)≤rightEndpoint d := by
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
-- module Solutions.OAIQ3_Std.StandardMap_EndpointShapes
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
    (h : ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t≤c*|(t:ℝ)-(s:ℝ)|) :
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
    (h : ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t≤c*|(t:ℝ)-(s:ℝ)|) :
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
lemma endpoints_slow {d : DistanceArray} {c : ℝ} (hc : c < 1)
    (h : ∀s t:DyadicTime,d.val s t≤c*|(t:ℝ)-(s:ℝ)|) : leftEndpoint d=⊥ ∧ rightEndpoint d=⊤ := by
  constructor
  · apply eq_bot_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,_,hr⟩ := EReal.exists_between_coe_real hh
    exact (not_le_of_gt hr) (leftEndpoint_le_of_slow_interval (a := r) (b := r+1) (by linarith) hc (fun s t _ _ => h s t))
  · apply eq_top_iff.mpr
    apply le_of_not_gt
    intro hh
    obtain ⟨r,hr,_⟩ := EReal.exists_between_coe_real hh
    exact (not_le_of_gt hr) (rightEndpoint_ge_of_slow_interval (a := r-1) (b := r) (by linarith) hc (fun s t _ _ => h s t))
lemma endpoints_left_ray {d : DistanceArray} {a c : ℝ} (hc : c < 1)
    (hl : ∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|)
    (hs : ∀s t:DyadicTime,a≤(s:ℝ) → a≤(t:ℝ) → d.val s t≤c*|(t:ℝ)-(s:ℝ)|) :
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
    (hs : ∀s t:DyadicTime,(s:ℝ)≤b → (t:ℝ)≤b → d.val s t≤c*|(t:ℝ)-(s:ℝ)|) :
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
    (hs : ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t≤c*|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d=(a:EReal) ∧ rightEndpoint d=(b:EReal) :=
  ⟨le_antisymm (leftEndpoint_le_of_slow_interval hab hc hs) (leftEndpoint_lower_ray d hl),
   le_antisymm (rightEndpoint_upper_ray d hr) (rightEndpoint_ge_of_slow_interval hab hc hs)⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_EndpointCovariance
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
lemma endpoints_translate (r : DyadicTime) (d : DistanceArray) :
    leftEndpoint (arrayTranslate r d)=erealOrderIso (OrderIso.addRight (-(r:ℝ))) (leftEndpoint d) ∧
    rightEndpoint (arrayTranslate r d)=erealOrderIso (OrderIso.addRight (-(r:ℝ))) (rightEndpoint d) := by
  apply endpoints_reindex d _ _ (Equiv.addRight (-r))
  · intro s; rfl
  · intro s t
    change d.val (s+-r+r) (t+-r+r)≠|((t:ℝ)+-(r:ℝ))-((s:ℝ)+-(r:ℝ))| ↔ _
    rw [show s+-r+r=s by abel,show t+-r+r=t by abel]
    rw [show ((t:ℝ)+-(r:ℝ))-((s:ℝ)+-(r:ℝ))=(t:ℝ)-(s:ℝ) by ring]
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
-- module Solutions.OAIQ3_Std.StandardMap_EndpointClasses
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
    (∀s t:DyadicTime,d.val s t≤c*|(t:ℝ)-(s:ℝ)|) ∨
    (∃a:ℝ,(∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,a≤(s:ℝ) → a≤(t:ℝ) → d.val s t≤c*|(t:ℝ)-(s:ℝ)|)) ∨
    (∃b:ℝ,(∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,(s:ℝ)≤b → (t:ℝ)≤b → d.val s t≤c*|(t:ℝ)-(s:ℝ)|)) ∨
    (∃a b:ℝ,a<b ∧
      (∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t≤c*|(t:ℝ)-(s:ℝ)|)) := by
  rcases h with hs|⟨a,hl,hs⟩|⟨b,hr,hs⟩|⟨a,b,hab,⟨hl,hr⟩,hs⟩
  · exact Or.inl (fun s t => by simpa only [realArray_coe d hu] using hs s t)
  · exact Or.inr (Or.inl ⟨a,fun s t hp hq => by simpa only [realArray_coe d hu] using hl s hp t hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨b,fun s t hp hq => by simpa only [realArray_coe d hu] using hr s hp t hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a,b,hab,fun s t hp hq => by simpa only [realArray_coe d hu] using hl s t hp hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hr s t hp hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩))
lemma twoRay_properties {d:DistanceArray} {c:ℝ} (hu:UnitArray d) (hc:c<1) (hs:SlowShape (realArray d) c)
    (hd:d∈twoRayClass) : endpointLeft d<endpointRight d ∧
    (∀s t:DyadicTime,(s:ℝ)≤endpointLeft d → (t:ℝ)≤endpointLeft d → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
    (∀s t:DyadicTime,endpointRight d≤(s:ℝ) → endpointRight d≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
    (∀s t:DyadicTime,(s:ℝ)∈Icc (endpointLeft d) (endpointRight d) → (t:ℝ)∈Icc (endpointLeft d) (endpointRight d) → d.val s t≤c*|(t:ℝ)-(s:ℝ)|) := by
  rcases slowShape_dyadic hu hs with hs|⟨a,hl,hs⟩|⟨b,hr,hs⟩|⟨a,b,hab,hl,hr,hs⟩
  · exact (hd.1 (endpoints_slow hc hs).1).elim
  · exact (hd.2.2.2 (endpoints_left_ray hc hl hs).2).elim
  · exact (hd.1 (endpoints_right_ray hc hr hs).1).elim
  · have he := endpoints_two_rays hab hc hl hr hs
    have ha : endpointLeft d=a := by simp only [endpointLeft,he.1,EReal.toReal_coe]
    have hb : endpointRight d=b := by simp only [endpointRight,he.2,EReal.toReal_coe]
    simpa only [ha,hb] using And.intro hab (And.intro hl (And.intro hr hs))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_EndpointActions
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
lemma twoRayClass_translate (r:DyadicTime) (d:DistanceArray) : arrayTranslate r d∈twoRayClass ↔ d∈twoRayClass := by
  change (_≠⊥ ∧ _≠⊤ ∧ _≠⊥ ∧ _≠⊤) ↔ _
  rw [(endpoints_translate r d).1,(endpoints_translate r d).2]
  simp only [ne_eq,erealOrderIso_eq_bot,erealOrderIso_eq_top]
  rfl
lemma twoRayClass_dilate (d:DistanceArray) : arrayDilate d∈twoRayClass ↔ d∈twoRayClass := by
  change (_≠⊥ ∧ _≠⊤ ∧ _≠⊥ ∧ _≠⊤) ↔ _
  rw [(endpoints_dilate d).1,(endpoints_dilate d).2]
  simp only [ne_eq,erealOrderIso_eq_bot,erealOrderIso_eq_top]
  rfl
lemma endpointLeft_translate (r:DyadicTime) (d:DistanceArray) (ht:leftEndpoint d≠⊤) (hb:leftEndpoint d≠⊥) :
    endpointLeft (arrayTranslate r d)=endpointLeft d-(r:ℝ) := by
  unfold endpointLeft
  rw [(endpoints_translate r d).1,←EReal.coe_toReal ht hb,erealOrderIso_coe]
  simp only [EReal.toReal_coe]
  rfl
lemma endpointRight_translate (r:DyadicTime) (d:DistanceArray) (ht:rightEndpoint d≠⊤) (hb:rightEndpoint d≠⊥) :
    endpointRight (arrayTranslate r d)=endpointRight d-(r:ℝ) := by
  unfold endpointRight
  rw [(endpoints_translate r d).2,←EReal.coe_toReal ht hb,erealOrderIso_coe]
  simp only [EReal.toReal_coe]
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
lemma map_restrict_invariant {X:Type*} [MeasurableSpace X] (μ:Measure X) (f:X→X) (hf:Measurable f)
    (hm:μ.map f=μ) (A:Set X) (hA:MeasurableSet A) (hfA:f⁻¹'A=A) : (μ.restrict A).map f=μ.restrict A := by
  rw [←hfA,←Measure.restrict_map hf hA,hm,hfA]
lemma push_invariant {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ:Measure X)
    (f:X→X) (hf:Measurable f) (hm:μ.map f=μ) (e:X→Y) (he:Measurable e) (g:Y→Y) (hg:Measurable g)
    (hc:∀ᵐx ∂μ,g (e x)=e (f x)) : (μ.map e).map g=μ.map e := by
  rw [Measure.map_map hg he]
  calc
    μ.map (g ∘ e)=μ.map (e ∘ f) := Measure.map_congr hc
    _=(μ.map f).map e := (Measure.map_map he hf).symm
    _=μ.map e := by rw [hm]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ScaleAction
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
-- module Solutions.OAIQ3_Std.StandardMap_ScaleEndpoints
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
lemma coreLength_translate (r:DyadicTime) (d:DistanceArray) (hd:d∈twoRayClass) : coreLength (arrayTranslate r d)=coreLength d := by
  unfold coreLength
  rw [endpointRight_translate r d hd.2.2.2 hd.2.2.1,endpointLeft_translate r d hd.2.1 hd.1]
  ring
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
lemma lengthBand_translate (j:ℤ) (r:DyadicTime) : (nonaffineTranslation r)⁻¹'lengthBand j=lengthBand j := by
  ext d
  change (UnitArray (arrayTranslate r d.val) ∧ arrayTranslate r d.val∈twoRayClass ∧ (2:ℝ)^j≤coreLength (arrayTranslate r d.val) ∧ coreLength (arrayTranslate r d.val)<(2:ℝ)^(j+1)) ↔ (UnitArray d.val ∧ d.val∈twoRayClass ∧ (2:ℝ)^j≤coreLength d.val ∧ coreLength d.val<(2:ℝ)^(j+1))
  have hu : UnitArray (arrayTranslate r d.val) ↔ UnitArray d.val := by
    constructor
    · intro h s t
      have hh := h (s-r) (t-r)
      change d.val.val (s-r+r) (t-r+r)≤|(t:ℝ)-(r:ℝ)-((s:ℝ)-(r:ℝ))| at hh
      simpa only [sub_add_cancel,sub_sub_sub_cancel_right] using hh
    · intro h s t
      have hh := h (s+r) (t+r)
      change d.val.val (s+r) (t+r)≤|(t:ℝ)+(r:ℝ)-((s:ℝ)+(r:ℝ))| at hh
      change d.val.val (s+r) (t+r)≤|(t:ℝ)-(s:ℝ)|
      simpa only [add_sub_add_right_eq_sub] using hh
  rw [hu,twoRayClass_translate]
  constructor <;> rintro ⟨hu,hd,hl,hr⟩
  · rw [coreLength_translate r d.val hd] at hl hr; exact ⟨hu,hd,hl,hr⟩
  · exact ⟨hu,hd,by simpa only [coreLength_translate r d.val hd] using hl,by simpa only [coreLength_translate r d.val hd] using hr⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_EndpointCompact
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
lemma separated_secants_compact (p q u v:DyadicTime) (hpq:(p:ℝ)<(q:ℝ)) (huv:(u:ℝ)<(v:ℝ))
    (c:ℝ) (hc:c<1) : IsCompact {d:NonAffineArray | d.val.val p q=(q:ℝ)-(p:ℝ) ∧ d.val.val u v≤c*((v:ℝ)-(u:ℝ))} := by
  let K:Set DistanceArray := {d | d.val p q=(q:ℝ)-(p:ℝ) ∧ d.val u v≤c*((v:ℝ)-(u:ℝ))}
  have hK : IsCompact K := ((isClosed_eq (continuous_arrayEval p q) continuous_const).inter
    (isClosed_le (continuous_arrayEval u v) continuous_const)).isCompact
  have hsub : K⊆(affineLocus)ᶜ := by
    intro d hd ⟨w,hw⟩
    subst d
    have h1 : w.val*((q:ℝ)-(p:ℝ))=(q:ℝ)-(p:ℝ) := by
      simpa only [affineArray,abs_of_pos (sub_pos.mpr hpq)] using hd.1
    have hw1 : w.val=1 := by nlinarith [sub_pos.mpr hpq]
    have h2 : w.val*((v:ℝ)-(u:ℝ))≤c*((v:ℝ)-(u:ℝ)) := by
      simpa only [affineArray,abs_of_pos (sub_pos.mpr huv)] using hd.2
    rw [hw1,one_mul] at h2
    exact (not_le_of_gt (mul_lt_of_lt_one_left (sub_pos.mpr huv) hc)) h2
  have hsub' : K⊆Set.range ((↑):NonAffineArray→DistanceArray) := fun d hd => ⟨⟨d,hsub hd⟩,rfl⟩
  exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hsub'
lemma separated_secants_finite (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (p q u v:DyadicTime) (hpq:(p:ℝ)<(q:ℝ)) (huv:(u:ℝ)<(v:ℝ)) (c:ℝ) (hc:c<1) :
    μ {d:NonAffineArray | d.val.val p q=(q:ℝ)-(p:ℝ) ∧ d.val.val u v≤c*((v:ℝ)-(u:ℝ))}<∞ :=
  (separated_secants_compact p q u v hpq huv c hc).measure_lt_top
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_EndpointIntensity
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
lemma preimage_sub_Ico (a b r:ℝ) : (fun x:ℝ => x-r)⁻¹'Ico a b=Ico (a+r) (b+r) := by
  ext x; simp only [mem_preimage,mem_Ico]; constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
lemma invariant_Ico_translate (μ:Measure ℝ) (r:ℝ) (h:μ.map (fun x:ℝ => x-r)=μ) (a b:ℝ) :
    μ (Ico (a+r) (b+r))=μ (Ico a b) := by
  rw [←preimage_sub_Ico,←Measure.map_apply (show Measurable (fun x:ℝ => x-r) from measurable_id.sub measurable_const) measurableSet_Ico,h]
lemma measure_Ico_split (μ:Measure ℝ) {a b c:ℝ} (hab:a≤b) (hbc:b≤c) :
    μ (Ico a c)=μ (Ico a b)+μ (Ico b c) := by
  have hu : Ico a c=Ico a b∪Ico b c := by
    ext x; simp only [mem_Ico,mem_union]; constructor
    · rintro ⟨ha,hc⟩; by_cases h:x<b
      · exact Or.inl ⟨ha,h⟩
      · exact Or.inr ⟨le_of_not_gt h,hc⟩
    · rintro (⟨ha,hb⟩|⟨hb,hc⟩)
      · exact ⟨ha,hb.trans_le hbc⟩
      · exact ⟨hab.trans hb,hc⟩
  rw [hu,measure_union (by rw [disjoint_left]; intro x hx hy; exact (not_lt_of_ge hy.1) hx.2) measurableSet_Ico]
lemma stationary_Ico_nat (μ:Measure ℝ)
    (ht:∀r:DyadicTime,μ.map (fun x:ℝ => x-(r:ℝ))=μ) (a:ℤ) (n:ℕ) :
    μ (Ico (a:ℝ) ((a:ℝ)+(n:ℝ)))=(n:ℝ≥0∞)*μ (Ico 0 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : μ (Ico ((a:ℝ)+(n:ℝ)) ((a:ℝ)+(n+1:ℕ)))=μ (Ico 0 1) := by
      have hh := invariant_Ico_translate μ (dyadicInt (a+n):ℝ) (ht (dyadicInt (a+n))) 0 1
      convert! hh using 2 ; simp only [dyadicInt_val,Int.cast_add,Int.cast_natCast,Nat.cast_add,Nat.cast_one] ; ring_nf
    rw [show ((a:ℝ)+(n+1:ℕ))=(a:ℝ)+(n:ℝ)+1 by push_cast; ring,
      measure_Ico_split μ (show (a:ℝ)≤(a:ℝ)+(n:ℝ) from le_add_of_nonneg_right (Nat.cast_nonneg n)) (by linarith),ih]
    have he' : μ (Ico ((a:ℝ)+(n:ℝ)) ((a:ℝ)+(n:ℝ)+1))=μ (Ico 0 1) := by convert! he using 2 ; push_cast ; ring_nf
    rw [he',Nat.cast_add,Nat.cast_one,add_mul,one_mul]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BandIntensity
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
lemma bandLaw_translate (μ:Measure NonAffineArray) (ht:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) (r:DyadicTime) : (bandLaw μ).map (nonaffineTranslation r)=bandLaw μ :=
  map_restrict_invariant μ _ (nonaffineTranslation r).continuous.measurable (ht r) _ (measurableSet_lengthBand 0) (lengthBand_translate 0 r)
lemma bandIntensity_translate (μ:Measure NonAffineArray) (ht:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) (r:DyadicTime) : (bandIntensity μ).map (fun x:ℝ => x-(r:ℝ))=bandIntensity μ := by
  apply push_invariant _ _ (nonaffineTranslation r).continuous.measurable (bandLaw_translate μ ht r)
    _ (measurable_endpointLeft.comp measurable_subtype_coe) _ (measurable_id.sub measurable_const)
  exact (ae_restrict_mem (measurableSet_lengthBand 0)).mono (fun d hd => (endpointLeft_translate r d.val hd.2.1.2.1 hd.2.1.1).symm)
lemma bandIntensity_finite (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000)) : bandIntensity μ (Ico 0 1)<∞ := by
  have hbin (x:DyadicTime) (hx:0≤(x:ℝ)) :
      μ {d:NonAffineArray | d∈lengthBand 0 ∧ endpointLeft d.val∈Ico (x:ℝ) ((x:ℝ)+1/2)}<∞ := by
    apply lt_of_le_of_lt (measure_mono_ae ?_) (separated_secants_finite μ (dyadicInt (-1)) 0
      (x+dyadicHalf (dyadicInt 1)) (x+dyadicInt 1) (by norm_num) (by simp only [AddSubgroup.coe_add,dyadicHalf_val,dyadicInt_val,Int.cast_one]; linarith) (999/1000) (by norm_num))
    filter_upwards [hs] with d hsd
    rintro ⟨hd,ha⟩
    obtain ⟨hab,hl,hr,hslow⟩ := twoRay_properties hd.1 (by norm_num) hsd hd.2.1
    have hlen : 1≤endpointRight d.val-endpointLeft d.val := by simpa only [lengthBand,zpow_zero,coreLength] using hd.2.2.1
    refine ⟨?_,?_⟩
    · have hh := hl (dyadicInt (-1)) 0 (by norm_num; linarith [ha.1]) (by change (0:ℝ)≤endpointLeft d.val; linarith [ha.1])
      simpa only [dyadicInt_val,Int.cast_neg,Int.cast_one,ZeroMemClass.coe_zero,sub_neg_eq_add,zero_add,abs_of_pos (by norm_num : (0:ℝ)<1)] using hh
    · have hp : ((x+dyadicHalf (dyadicInt 1):DyadicTime):ℝ)=(x:ℝ)+1/2 := by simp only [AddSubgroup.coe_add,dyadicHalf_val,dyadicInt_val,Int.cast_one]
      have hq : ((x+dyadicInt 1:DyadicTime):ℝ)=(x:ℝ)+1 := by simp only [AddSubgroup.coe_add,dyadicInt_val,Int.cast_one]
      have hh := hslow (x+dyadicHalf (dyadicInt 1)) (x+dyadicInt 1)
        (by rw [hp]; constructor <;> linarith [ha.1,ha.2]) (by rw [hq]; constructor <;> linarith [ha.1,ha.2])
      rw [abs_of_pos (by rw [hp,hq]; linarith)] at hh
      exact hh
  have h0 := hbin 0 (by norm_num)
  have h1 := hbin (dyadicHalf (dyadicInt 1)) (by norm_num)
  change ((bandLaw μ).map (endpointLeft ∘ Subtype.val)) (Ico 0 1)<∞
  rw [Measure.map_apply (measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Ico,bandLaw,Measure.restrict_apply ((measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Ico)]
  apply lt_of_le_of_lt (measure_mono ?_) ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨h0,h1⟩))
  rintro d ⟨ha,hd⟩
  by_cases h: endpointLeft d.val<1/2
  · exact Or.inl ⟨hd,by simpa only [mem_Ico,ZeroMemClass.coe_zero,zero_add,Function.comp_apply] using And.intro ha.1 h⟩
  · exact Or.inr ⟨hd,by simp only [mem_Ico,dyadicHalf_val,dyadicInt_val,Int.cast_one]; constructor; exact le_of_not_gt h; have ha1 : endpointLeft d.val<1 := ha.2; linarith⟩
lemma stationary_Ico_finite (μ:Measure ℝ)
    (ht:∀r:DyadicTime,μ.map (fun x:ℝ => x-(r:ℝ))=μ) (hf:μ (Ico 0 1)<∞) (a b:ℝ) : μ (Icc a b)<∞ := by
  obtain ⟨n,hn⟩ := exists_nat_gt (b-(⌊a⌋:ℤ))
  have he := stationary_Ico_nat μ ht ⌊a⌋ n
  apply lt_of_le_of_lt (measure_mono (t:=Ico (⌊a⌋:ℝ) ((⌊a⌋:ℝ)+n)) ?_) ?_
  · exact fun x hx => ⟨(Int.floor_le a).trans hx.1,by linarith [hx.2]⟩
  · rw [he]; exact ENNReal.mul_lt_top (by simp) hf
lemma bandLaw_endpoint_finite (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (ht:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) (a b:ℝ) :
    bandLaw μ {d:NonAffineArray | endpointLeft d.val∈Icc a b}<∞ := by
  have hh := stationary_Ico_finite (bandIntensity μ) (bandIntensity_translate μ ht) (bandIntensity_finite μ hs) a b
  change ((bandLaw μ).map (endpointLeft ∘ Subtype.val)) (Icc a b)<∞ at hh
  rw [Measure.map_apply (measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Icc] at hh
  exact hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ScaleEvaluation
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
lemma dyadicZoom_val (j:ℤ) (s:DyadicTime) : (dyadicZoom j s:ℝ)=(2:ℝ)^j*(s:ℝ) := by
  cases j with
  | ofNat n => simp only [dyadicZoom,AddSubgroup.coe_nsmul,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,Int.ofNat_eq_natCast,zpow_natCast]
  | negSucc n =>
    rw [dyadicZoom,dyadicFine_val,Int.negSucc_eq,zpow_neg,zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_natCast,zpow_one,pow_succ]
    ring
lemma dyadicZoom_zero (j:ℤ) : dyadicZoom j 0=0 := by apply Subtype.ext; simp only [dyadicZoom_val,ZeroMemClass.coe_zero,mul_zero]
lemma dyadicZoom_add (j:ℤ) (s t:DyadicTime) : dyadicZoom j (s+t)=dyadicZoom j s+dyadicZoom j t := by
  apply Subtype.ext; simp only [dyadicZoom_val,AddSubgroup.coe_add,mul_add]
lemma dyadicZoom_succ (j:ℤ) (s:DyadicTime) : dyadicZoom (j+1) s=dyadicZoom j (s+s) := by
  apply Subtype.ext; simp only [dyadicZoom_val,AddSubgroup.coe_add,zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_one]; ring
lemma dyadicZoom_pred (j:ℤ) (s:DyadicTime) : dyadicZoom (j-1) s=dyadicZoom j (dyadicHalf s) := by
  apply Subtype.ext; simp only [dyadicZoom_val,dyadicHalf_val,zpow_sub₀ (by norm_num : (2:ℝ)≠0),zpow_one]; ring
lemma dyadicZoom_two (j:ℤ) : dyadicZoom j (dyadicInt 2)=dyadicZoom (j+1) (dyadicInt 1) := by
  rw [dyadicZoom_succ]; congr 1; apply Subtype.ext; norm_num
lemma scaleZ_eval (j:ℤ) (d:NonAffineArray) (hu:UnitArray d.val) (s t:DyadicTime) :
    (scaleZ j d).val.val s t=d.val.val (dyadicZoom j s) (dyadicZoom j t)/(2:ℝ)^j := by
  induction j using Int.induction_on generalizing s t with
  | zero => simp only [scaleZ_zero,dyadicZoom,pow_zero,one_nsmul,zpow_zero,div_one]
  | succ j ih =>
    rw [add_comm,scaleZ_add,scaleZ_one,nonaffineDouble,ite_eq_left ((scaleZ_unit j d).mpr hu)]
    change (scaleZ j d).val.val (s+s) (t+t)/2=_
    rw [ih,←dyadicZoom_succ,←dyadicZoom_succ,zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_one]
    ring_nf
  | pred j ih =>
    rw [sub_eq_add_neg,add_comm,scaleZ_add,scaleZ_neg_one,nonaffineHalf,dite_eq_left ((scaleZ_unit (-(j:ℤ)) d).mpr hu)]
    change 2*(scaleZ (-(j:ℤ)) d).val.val (dyadicHalf s) (dyadicHalf t)=_
    rw [ih,←dyadicZoom_pred,←dyadicZoom_pred]
    rw [zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_neg_one]
    ring_nf
lemma scaleZ_shortfall (j:ℤ) (d:NonAffineArray) (hu:UnitArray d.val) (s t:DyadicTime) :
    arrayShortfall s t (scaleZ j d).val=arrayShortfall (dyadicZoom j s) (dyadicZoom j t) d.val := by
  unfold arrayShortfall
  rw [scaleZ_eval j d hu,dyadicZoom_val,dyadicZoom_val,←mul_sub,div_div]
lemma scaleZ_capG (α:ℝ) (j:ℤ) (d:NonAffineArray) (hu:UnitArray d.val) :
    capG α (scaleZ j d).val=entropyCap α (arrayShortfall 0 (dyadicZoom (j+1) (dyadicInt 1)) d.val)-
      (entropyCap α (arrayShortfall 0 (dyadicZoom j (dyadicInt 1)) d.val)+entropyCap α (arrayShortfall (dyadicZoom j (dyadicInt 1)) (dyadicZoom (j+1) (dyadicInt 1)) d.val))/2 := by
  unfold capG
  rw [scaleZ_shortfall j d hu,scaleZ_shortfall j d hu,scaleZ_shortfall j d hu,dyadicZoom_zero,dyadicZoom_two]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BandGeometry
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
lemma band_cap_support (α:ℝ) (d:NonAffineArray) (hd:d∈lengthBand 0)
    (hs:SlowShape (realArray d.val) (999/1000)) (t:DyadicTime) (hp:0<(t:ℝ))
    (he:endpointLeft d.val∉Icc (-2) (t:ℝ)) : entropyCap α (arrayShortfall 0 t d.val)=0 := by
  obtain ⟨hab,hl,hr,hslow⟩ := twoRay_properties hd.1 (by norm_num) hs hd.2.1
  have hlen : endpointRight d.val-endpointLeft d.val<2 := by simpa only [lengthBand,zpow_zero,zero_add,zpow_one,coreLength] using hd.2.2.2
  have hh : d.val.val 0 t=(t:ℝ) := by
    by_cases h:endpointLeft d.val<(t:ℝ)
    · have ha : endpointLeft d.val< -2 := by by_contra hn; exact he ⟨le_of_not_gt hn,h.le⟩
      have hrr := hr 0 t (by change endpointRight d.val≤0; linarith) (by linarith)
      simpa only [ZeroMemClass.coe_zero,sub_zero,abs_of_pos hp] using hrr
    · have hll := hl 0 t (by change (0:ℝ)≤endpointLeft d.val; linarith) (le_of_not_gt h)
      simpa only [ZeroMemClass.coe_zero,sub_zero,abs_of_pos hp] using hll
  have heq : arrayShortfall 0 t d.val=0 := by
    unfold arrayShortfall; rw [hh,ZeroMemClass.coe_zero,sub_zero,div_self hp.ne']; ring
  rw [heq,entropyCap_linear (by norm_num),mul_zero]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BandCap
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
lemma measurable_bandCap (α:ℝ) (t:DyadicTime) : Measurable (bandCap α t) :=
  ((entropyCap_contDiff α).continuous.comp ((continuous_arrayShortfall 0 t).comp continuous_subtype_val)).measurable
lemma bandCap_integrable (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) {α:ℝ} (ha:0≤α) (ha1:α≤1)
    (t:DyadicTime) (ht:0<(t:ℝ)) : Integrable (bandCap α t) (bandLaw μ) := by
  let E:Set NonAffineArray := {d | endpointLeft d.val∈Icc (-2) (t:ℝ)}
  have hE : MeasurableSet E := (measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Icc
  have hf : bandLaw μ E<∞ := bandLaw_endpoint_finite μ hs hT _ _
  have : IsFiniteMeasure ((bandLaw μ).restrict E) := ⟨by simpa only [Measure.restrict_apply_univ] using hf⟩
  have hi : Integrable (E.indicator (fun _ => (1:ℝ))) (bandLaw μ) := IntegrableOn.integrable_indicator (integrable_const (μ:=(bandLaw μ).restrict E) (1:ℝ)) hE
  apply hi.mono' (measurable_bandCap α t).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_lengthBand 0),ae_restrict_of_ae hs] with d hd hsd
  rw [Real.norm_eq_abs,bandCap,abs_of_nonneg ((entropyCap_bounds ha ha1 (shortfall_unit_mem d.val hd.1 0 t (by simpa only [ZeroMemClass.coe_zero]))).1)]
  by_cases he:d∈E
  · rw [indicator_of_mem he]; exact (entropyCap_bounds ha ha1 (shortfall_unit_mem d.val hd.1 0 t (by simpa only [ZeroMemClass.coe_zero]))).2
  · rw [indicator_of_notMem he]
    exact le_of_eq (band_cap_support α d hd hsd t ht he)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BandSeries
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
-- module Solutions.OAIQ3_Std.StandardMap_BandCoboundary
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
lemma zoom_one_pos (j:ℤ) : 0<(dyadicZoom j (dyadicInt 1):ℝ) := by
  rw [dyadicZoom_val,dyadicInt_val,Int.cast_one,mul_one]; positivity
lemma zoom_next (j:ℤ) : dyadicZoom (j+1) (dyadicInt 1)=dyadicZoom j (dyadicInt 1)+dyadicZoom j (dyadicInt 1) := by
  rw [dyadicZoom_succ,dyadicZoom_add]
lemma bandCap_translate (α:ℝ) (t:DyadicTime) (d:NonAffineArray) :
    bandCap α t (nonaffineTranslation t d)=entropyCap α (arrayShortfall t (t+t) d.val) := by
  unfold bandCap
  change entropyCap α (arrayShortfall 0 t (arrayTranslate t d.val))=_
  rw [shortfall_translate,zero_add]
lemma band_coboundary (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) {α:ℝ} (ha:0≤α) (ha1:α≤1) (j:ℤ) :
    (∫d,capG α (scaleZ j d).val ∂bandLaw μ)=bandMoment μ α (j+1)-bandMoment μ α j := by
  let t:=dyadicZoom j (dyadicInt 1)
  let u:=dyadicZoom (j+1) (dyadicInt 1)
  have hi:=bandCap_integrable μ hs hT ha ha1 t (zoom_one_pos j)
  have hj:=bandCap_integrable μ hs hT ha ha1 u (zoom_one_pos (j+1))
  have ht:Integrable (fun d => bandCap α t (nonaffineTranslation t d)) (bandLaw μ) := by
    apply (integrable_map_measure (measurable_bandCap α t).aestronglyMeasurable (nonaffineTranslation t).continuous.measurable.aemeasurable).mp
    rw [bandLaw_translate μ hT]; exact hi
  have he : (fun d:NonAffineArray => capG α (scaleZ j d).val)=ᵐ[bandLaw μ]
      (fun d => bandCap α u d-(bandCap α t d+bandCap α t (nonaffineTranslation t d))/2) := by
    filter_upwards [ae_restrict_mem (measurableSet_lengthBand 0)] with d hd
    rw [scaleZ_capG α j d hd.1,bandCap_translate]
    simp only [bandCap,u,t,zoom_next]
  have hsum : Integrable (fun d => (bandCap α t d+bandCap α t (nonaffineTranslation t d))/2) (bandLaw μ) := (hi.add ht).div_const 2
  rw [integral_congr_ae he,integral_sub hj hsum,integral_div,integral_add hi ht]
  rw [integral_invariant_translation _ _ (bandLaw_translate μ hT t) _ (measurable_bandCap α t)]
  change bandMoment μ α (j+1)-(bandMoment μ α j+bandMoment μ α j)/2=_
  ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_OneRayZero
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
-- module Solutions.OAIQ3_Std.StandardMap_RemainderCap
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
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma remainder_cap_nonpos_q3_oai {α:ℝ} (ha:0≤α) (ha1:α≤1) (hasmall:α*1200000004≤1/16) :
    (∫d:NonAffineArray,capG α d.val ∂S.remainderLaw L)≤0 := by
  have:=S.remainder_local L
  have hser:=band_integral_series (S.remainderLaw L) (S.remainder_unit L) (S.remainder_dilate_q3 L)
    (fun d => capG α d.val) (S.capG_integrable_remainder L α)
  simp_rw [band_coboundary _ (S.remainder_shape_q3 L) (S.remainder_translate_q3 L) ha ha1] at hser
  rw [←S.remainder_cap_band_q3 L α] at hser
  apply bilateral_coboundary_nonpos _ _ hser
  exact bandMoment_order_q3 _ (S.remainder_shape_q3 L) (S.remainder_translate_q3 L)
    (ae_mono (S.remainder_le L) (S.tree_aemulti L))
    (ae_mono (S.remainder_le L) (S.noCancellation_aemulti_q3 L)) ha ha1 hasmall
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_nonpos_q3_oai := @OAI.StandardMapEntropy.CriticalScaleSequence.remainder_cap_nonpos_q3_oai
