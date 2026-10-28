-- Prove2me | solution 1 for OAI.StandardMapEntropy.CriticalScaleSequence.weight_affine_null_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:35:48.157171+00:00
-- url     : https://prove2.me/submissions/efe3edc8-7f33-44e2-b38d-8a32ff8196a1

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_middle_weight_tendsto_q44

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
  all_goals try with_reducible_and_instances rfl
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
-- module Solutions.OAIQ44_CM.StandardMap_SegmentObservations
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
-- module Solutions.OAIQ44_CM.StandardMap_TorusDynamics
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
lemma measurePreserving_recurrenceCoordinates : MeasurePreserving recurrenceCoordinates area area := by
  unfold area
  apply (MeasurePreserving.id (volume : Measure Circle)).skew_product
  · exact measurable_fst.sub measurable_snd
  · exact Eventually.of_forall fun x => (Measure.measurePreserving_sub_left (volume : Measure Circle) x).map_eq
lemma measurePreserving_torusStep (k : ℝ) : MeasurePreserving (torusStep k) area area := by
  have hh := measurePreserving_recurrenceCoordinates.comp
    ((measurePreserving_standardMap k).comp measurePreserving_recurrenceCoordinates)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
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
-- module Solutions.OAIQ44_CM.StandardMap_TorusObservations
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
-- module Solutions.OAIQ44_CM.StandardMap_ScaleTruncation
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

lemma min_tree_chain {a b c x y e : ℝ} (he : 0≤e)
    (hx : min a b-e≤x) (hy : min x c-e≤y) : min a (min b c)-2*e≤y := by
  have ha : min a (min b c)≤a := min_le_left _ _
  have hb : min a (min b c)≤b := (min_le_right _ _).trans (min_le_left _ _)
  have hc : min a (min b c) ≤ c := (min_le_right _ _).trans (min_le_right _ _)
  have h1 : min a (min b c)-e≤x := by have := le_min ha hb; linarith
  have h2 : min a (min b c)-e≤ min x c := le_min h1 (by linarith)
  linarith
lemma productDistance_cut_wings (k : ℝ) (hk : 0≤k) (z : Torus) (i : ℤ)
    (n s : ℕ) (hsn : s≤n) :
    let D := (n:ℝ)-min (productDistance k z i (i-(n:ℤ))) (productDistance k z i (i+(n:ℤ)))
    (s:ℝ)-D≤productDistance k z i (i-(s:ℤ)) ∧
      (s:ℝ)-D≤productDistance k z i (i+(s:ℤ)) := by
  dsimp only
  have hns : (s:ℝ)≤n := by exact_mod_cast hsn
  have hL := productDistance_triangle k hk z i (i-(s:ℤ)) (i-(n:ℤ))
  have hR := productDistance_triangle k hk z i (i+(s:ℤ)) (i+(n:ℤ))
  have bL := productDistance_le k hk z (i-(s:ℤ)) (i-(n:ℤ))
  have bR := productDistance_le k hk z (i+(s:ℤ)) (i+(n:ℤ))
  simp only [Int.cast_add,Int.cast_sub,Int.cast_natCast] at bL bR
  rw [show (i:ℝ)-n-((i:ℝ)-s)=(s:ℝ)-n by ring,abs_of_nonpos (by linarith)] at bL
  rw [show (i:ℝ)+n-((i:ℝ)+s)=(n:ℝ)-s by ring,abs_of_nonneg (by linarith)] at bR
  have hminL := min_le_left (productDistance k z i (i-(n:ℤ))) (productDistance k z i (i+(n:ℤ)))
  have hminR := min_le_right (productDistance k z i (i-(n:ℤ))) (productDistance k z i (i+(n:ℤ)))
  constructor <;> linarith
lemma productDistance_truncation (k : ℝ) (hk : 0≤k) (z : Torus) (i : ℤ)
    (n s : ℕ) (hsn : s≤n) :
    let g := productDistance k z
    let D := (n:ℝ)-min (g i (i-(n:ℤ))) (g i (i+(n:ℤ)))
    let loss := g i (i-(n:ℤ))+g i (i+(n:ℤ))-g (i-(n:ℤ)) (i+(n:ℤ))
    min loss (2*(s:ℝ)-2*D)-6≤g i (i-(s:ℤ))+g i (i+(s:ℤ))-g (i-(s:ℤ)) (i+(s:ℤ)) := by
  let g := productDistance k z
  let D := (n:ℝ)-min (g i (i-(n:ℤ))) (g i (i+(n:ℤ)))
  let B := fun u v => g i u+g i v-g u v
  change min (B (i-(n:ℤ)) (i+(n:ℤ))) (2*(s:ℝ)-2*D)-6≤B (i-(s:ℤ)) (i+(s:ℤ))
  have ht (u v w : ℤ) : min (B u v) (B v w)-3≤B u w := productDistance_tree k hk z i u v w
  have hns : (s:ℝ)≤n := by exact_mod_cast hsn
  obtain ⟨hcL,hcR⟩ := productDistance_cut_wings k hk z i n s hsn
  have hwL : (n:ℝ)-D≤g i (i-(n:ℤ)) := by
    dsimp only [D]; have := min_le_left (g i (i-(n:ℤ))) (g i (i+(n:ℤ))); linarith
  have hwR : (n:ℝ)-D≤g i (i+(n:ℤ)) := by
    dsimp only [D]; have := min_le_right (g i (i-(n:ℤ))) (g i (i+(n:ℤ))); linarith
  have hbL : g (i-(s:ℤ)) (i-(n:ℤ))≤(n:ℝ)-s := by
    have hh := productDistance_le k hk z (i-(s:ℤ)) (i-(n:ℤ))
    simp only [Int.cast_sub,Int.cast_natCast] at hh
    rw [show (i:ℝ)-n-((i:ℝ)-s)=(s:ℝ)-n by ring,abs_of_nonpos (by linarith)] at hh
    linarith
  have hbR : g (i+(n:ℤ)) (i+(s:ℤ))≤(n:ℝ)-s := by
    have hh := productDistance_le k hk z (i+(n:ℤ)) (i+(s:ℤ))
    simp only [Int.cast_add,Int.cast_natCast] at hh
    rw [show (i:ℝ)+s-((i:ℝ)+n)=(s:ℝ)-n by ring,abs_of_nonpos (by linarith)] at hh
    linarith
  have hBL : 2*(s:ℝ)-2*D≤B (i-(s:ℤ)) (i-(n:ℤ)) := by
    change (s:ℝ)-D≤g i (i-(s:ℤ)) at hcL
    dsimp only [B]; linarith
  have hBR : 2*(s:ℝ)-2*D≤B (i+(n:ℤ)) (i+(s:ℤ)) := by
    change (s:ℝ)-D≤g i (i+(s:ℤ)) at hcR
    dsimp only [B]; linarith
  have hh := min_tree_chain (by norm_num : (0:ℝ)≤3)
    (ht (i-(s:ℤ)) (i-(n:ℤ)) (i+(n:ℤ)))
    (ht (i-(s:ℤ)) (i+(n:ℤ)) (i+(s:ℤ)))
  have hmin : min (B (i-(n:ℤ)) (i+(n:ℤ))) (2*(s:ℝ)-2*D) ≤
      min (B (i-(s:ℤ)) (i-(n:ℤ))) (min (B (i-(n:ℤ)) (i+(n:ℤ))) (B (i+(n:ℤ)) (i+(s:ℤ)))) := by
    exact le_min ((min_le_right _ _).trans hBL)
      (le_min (min_le_left _ _) ((min_le_right _ _).trans hBR))
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
lemma capSlope_one {u : ℝ} (hu : u≤1/10000) : capSlope u=1 := by
  unfold capSlope
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; ring
lemma capSlope_zero {u : ℝ} (hu : 1/5000≤ u) : capSlope u=0 := by
  unfold capSlope
  rw [Real.smoothTransition.one_of_one_le (by linarith)]; ring
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
lemma entropyCap_linear {α u : ℝ} (hu : u≤1/10000) : entropyCap α u=α*u := by
  unfold entropyCap
  rw [capPrimitive_linear hu,Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring
lemma entropyCap_one {α u : ℝ} (hu : 3/10000≤ u) : entropyCap α u=1 := by
  unfold entropyCap
  rw [capPrimitive_constant (by linarith),Real.smoothTransition.one_of_one_le (by linarith)]
  ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_DoublingPointwise
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
lemma cancellationLoss_bounds (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    0 ≤ cancellationLoss k z n ∧ cancellationLoss k z n ≤ 2*(n:ℝ) := by
  have htri := productDistance_triangle k hk z (-(n:ℤ)) 0 (n:ℤ)
  rw [productDistance_symm k z (-(n:ℤ)) 0] at htri
  have hL := productDistance_le k hk z 0 (-(n:ℤ))
  have hR := productDistance_le k hk z 0 (n:ℤ)
  simp only [Int.cast_neg,Int.cast_natCast,Int.cast_zero,sub_zero,abs_neg,Nat.abs_cast] at hL hR
  have hn := productDistance_nonneg k hk z (-(n:ℤ)) (n:ℤ)
  unfold cancellationLoss
  constructor  <;> linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MeanDeficit
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
lemma integral_wing_left (k : ℝ) (n : ℕ) :
    (∫ z, productDistance k z 0 (-(n:ℤ)) ∂area)=∫ z, productDistance k z 0 (n:ℤ) ∂area := by
  simp_rw [productDistance_symm k _ 0 (-(n:ℤ))]
  convert integral_distance_shift k 0 (n:ℤ) (-(n:ℤ)) using 1 ; simp
lemma integral_cancellationLoss (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0<n) :
    (∫ z,cancellationLoss k z n ∂area)=2*(n:ℝ)*(meanDeficit k (n+n)-meanDeficit k n) := by
  have hL := integrable_productDistance k hk 0 (-(n:ℤ))
  have hR := integrable_productDistance k hk 0 (n:ℤ)
  have hT := integrable_productDistance k hk (-(n:ℤ)) (n:ℤ)
  have ht : (∫ z,productDistance k z (-(n:ℤ)) (n:ℤ) ∂area)=∫ z,productDistance k z 0 ((n+n:ℕ):ℤ) ∂area := by
    convert integral_distance_shift k 0 ((n+n:ℕ):ℤ) (-(n:ℤ)) using 1 ; push_cast ; ring_nf
  have hsum : (∫ z,productDistance k z 0 (-(n:ℤ))+productDistance k z 0 (n:ℤ) ∂area)=
      (∫ z,productDistance k z 0 (-(n:ℤ)) ∂area)+(∫ z,productDistance k z 0 (n:ℤ) ∂area) := by
    convert! integral_add hL hR using 1
    all_goals try with_reducible_and_instances rfl
  have hsub : (∫ z,cancellationLoss k z n ∂area)=
      (∫ z,productDistance k z 0 (-(n:ℤ))+productDistance k z 0 (n:ℤ) ∂area)-(∫ z,productDistance k z (-(n:ℤ)) (n:ℤ) ∂area) := by
    convert! integral_sub (hL.add hR) hT using 1
    all_goals try with_reducible_and_instances rfl
  rw [hsub,hsum,integral_wing_left,ht]
  unfold meanDeficit
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp [hn0]; ring
lemma meanDeficit_doubling_mono (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0<n) :
    meanDeficit k n ≤ meanDeficit k (n+n) := by
  have hh : 0 ≤ ∫ z,cancellationLoss k z n ∂area := integral_nonneg fun z => (cancellationLoss_bounds k hk z n).1
  rw [integral_cancellationLoss k hk n hn] at hh
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  nlinarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MeanGrowth
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
lemma meanDeficit_pow_mono (k : ℝ) (hk : 0 ≤ k) : Monotone (fun j : ℕ => meanDeficit k (2^j)) := by
  apply monotone_nat_of_le_succ
  intro j
  have hh := meanDeficit_doubling_mono k hk (2^j) (by positivity)
  simpa only [pow_succ,Nat.mul_two] using hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_FixedDeficit
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
lemma criticalTheta_square (r i : ℕ) :
    1/((2^(criticalLowerExponent r i):ℕ):ℝ)=(criticalTheta r i)^2 := by
  unfold criticalLowerExponent criticalTheta
  push_cast
  simp only [div_pow,one_pow,← pow_mul]
  rw [Nat.mul_comm 2]
lemma criticalTheta_tendsto (r : ℕ) : Tendsto (criticalTheta r) atTop (𝓝 0) := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have he (i : ℕ) : criticalTheta r i=(1/2:ℝ)^i*(1/2:ℝ)^(r+1) := by
    unfold criticalTheta
    rw [← pow_add]
    congr 1
  have heq : criticalTheta r=(fun i => (1/2:ℝ)^i*(1/2:ℝ)^(r+1)) := funext he
  rw [heq]
  simpa only [zero_mul] using ht.mul_const ((1/2:ℝ)^(r+1))
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
lemma continuous_arrayTest (i : ArrayTestIndex) : Continuous (arrayTest i) :=
  (continuous_arrayJ _ _).add (continuous_arrayV _ _)
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
lemma rescaledDistance_aligned (k : ℝ) (z : Torus) (n : ℕ) (s t : DyadicTime) (a b : ℤ)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(b:ℝ)) :
    rescaledDistance k z n s t=productDistance k z a b/(n:ℝ) := by
  simp only [rescaledDistance,hs,ht,Int.floor_intCast]
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
-- module Solutions.OAIQ44_CM.StandardMap_ArrayMoments
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
    all_goals try with_reducible_and_instances rfl
  have hsub : (∫ d,arrayJ s t d ∂sampleLaw k hk n hn)=
      (∫ d,arrayShortfall s t d ∂sampleLaw k hk n hn)-
        (∫ d,(arrayShortfall s (dyadicMid s t) d+arrayShortfall (dyadicMid s t) t d)/2 ∂sampleLaw k hk n hn) := by
    convert! integral_sub (integrable_arrayShortfall (sampleLaw k hk n hn) s t)
      (((integrable_arrayShortfall (sampleLaw k hk n hn) s (dyadicMid s t)).add (integrable_arrayShortfall (sampleLaw k hk n hn) (dyadicMid s t) t)).div_const 2) using 1
    all_goals try with_reducible_and_instances rfl
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
      all_goals try with_reducible_and_instances rfl
    have h2 : (∫ d,((arrayShortfall s (dyadicMid s t) d)^2+(arrayShortfall (dyadicMid s t) t d)^2)/2-(arrayShortfall s t d)^2 ∂μ)=
        (∫ d,((arrayShortfall s (dyadicMid s t) d)^2+(arrayShortfall (dyadicMid s t) t d)^2)/2 ∂μ)-
          (∫ d,(arrayShortfall s t d)^2 ∂μ) := by
      convert! integral_sub (((integrable_arrayShortfall_sq μ s (dyadicMid s t)).add (integrable_arrayShortfall_sq μ (dyadicMid s t) t)).div_const 2) (integrable_arrayShortfall_sq μ s t) using 1
      all_goals try with_reducible_and_instances rfl
    have h3 : (∫ d,(arrayShortfall s (dyadicMid s t) d)^2+(arrayShortfall (dyadicMid s t) t d)^2 ∂μ)=
        (∫ d,(arrayShortfall s (dyadicMid s t) d)^2 ∂μ)+(∫ d,(arrayShortfall (dyadicMid s t) t d)^2 ∂μ) := by
      convert! integral_add (integrable_arrayShortfall_sq μ s (dyadicMid s t)) (integrable_arrayShortfall_sq μ (dyadicMid s t) t) using 1
      all_goals try with_reducible_and_instances rfl
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
-- module Solutions.OAIQ44_CM.StandardMap_ScaleTelescopes
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
-- module Solutions.OAIQ44_CM.StandardMap_ScaleTestBounds
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
    all_goals try with_reducible_and_instances rfl
  simp_rw [hi]
  exact hh
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ScaleCancellation
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
lemma sum_scaled_inverse (m l : ℕ) (hm : 0 < m) :
    (∑ j∈Finset.range l,1/((m*2^j:ℕ):ℝ)) ≤ 2/(m:ℝ) := by
  have he (j : ℕ) : 1/((m*2^j:ℕ):ℝ)=(1/(m:ℝ))*(1/2:ℝ)^j := by push_cast; rw [div_pow]; ring
  simp_rw [he]
  rw [←Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (sum_geometric_two_le l) (by positivity : 0≤1/(m:ℝ))
  norm_num only [one_div] at *
  simpa only [mul_comm,div_eq_mul_inv] using hh
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
lemma continuous_clippedShortfall (s t : DyadicTime) : Continuous (clippedShortfall s t) :=
  unitClip_lipschitz.continuous.comp (continuous_arrayShortfall s t)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_LimitCancellation
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
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma inverse_scale_epsilon_bound (i p : ℕ) (hp : criticalLowerExponent S.offset i ≤ p) :
    1/(((2^p:ℕ):ℝ)*S.epsilon i) ≤ criticalTheta S.offset i := by
  have hpow : (1:ℝ)/((2^p:ℕ):ℝ) ≤ 1/((2^(criticalLowerExponent S.offset i):ℕ):ℝ) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hp
  rw [criticalTheta_square] at hpow
  rw [←div_div]
  apply (div_le_iff₀ (S.epsilon_pos i)).mpr
  have ht : criticalTheta S.offset i ≤ S.epsilon i := (S.threshold i).le
  exact hpow.trans (by nlinarith [mul_le_mul_of_nonneg_left ht (criticalTheta_pos S.offset i).le])
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
lemma dyadicMid_zero_two : dyadicMid 0 (dyadicInt 2)=dyadicInt 1 := by
  apply Subtype.ext; norm_num
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TruncationArrays
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
lemma continuous_unitDefect : Continuous unitDefect :=
  ((continuous_arrayShortfall _ _).max (continuous_arrayShortfall _ _)).add (continuous_arrayJ _ _)
lemma cut_mid (b:ℕ) : dyadicMid (cutLeft b) (cutRight b)=dyadicInt 1 := by
  apply Subtype.ext
  simp only [dyadicMid_val,cutLeft_val,cutRight_val,dyadicInt_val,Int.cast_one]; ring
lemma sample_eval_int (k:ℝ) (hk:0≤k) (z:Torus) (n:ℕ) (hn:0<n) (a b:ℤ) :
    (sampleArray k hk z n hn).val (dyadicInt a) (dyadicInt b)=productDistance k z ((n:ℤ)*a) ((n:ℤ)*b)/(n:ℝ) := by
  exact rescaledDistance_aligned k z n _ _ _ _ (by simp) (by simp)
lemma truncation_array_bound (k:ℝ) (hk:0≤k) (z:Torus) (p b:ℕ) (hb:b≤p)
    (hx:unitDefect (sampleArray k hk z (2^p) (by positivity))<1/(2:ℝ)^b) :
    arrayJ 0 (dyadicInt 2) (sampleArray k hk z (2^p) (by positivity))≤
      (1/(2:ℝ)^b)*arrayJ (cutLeft b) (cutRight b) (sampleArray k hk z (2^p) (by positivity))+3/(2:ℝ)^p := by
  let n:ℕ:=2^p
  let s:ℕ:=2^(p-b)
  let d:=sampleArray k hk z n (by dsimp [n]; positivity)
  have hn:(0:ℝ)<n := by dsimp [n]; positivity
  have hs:(0:ℝ) < s := by dsimp [s]; positivity
  have hsn:s≤n := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have he:(n:ℝ)/(2:ℝ)^b=s := by
    dsimp [n,s]; push_cast
    rw [div_eq_mul_inv,← pow_sub₀ (2:ℝ) (by norm_num) hb]
  have he':(n:ℝ)*(1/(2:ℝ)^b)=s := by simpa [div_eq_mul_inv] using he
  have hz : dyadicInt 0 = (0:DyadicTime) := by apply Subtype.ext; norm_num
  have he0:d.val 0 (dyadicInt 1)=productDistance k z 0 n/n := by simpa [hz] using sample_eval_int k hk z n (by dsimp [n]; positivity) 0 1
  have he1:d.val (dyadicInt 1) (dyadicInt 2)=productDistance k z n (2*n)/n := by simpa [mul_comm,hz] using sample_eval_int k hk z n (by dsimp [n]; positivity) 1 2
  have he2:d.val 0 (dyadicInt 2)=productDistance k z 0 (2*n)/n := by simpa [mul_comm,hz] using sample_eval_int k hk z n (by dsimp [n]; positivity) 0 2
  have hA:arrayShortfall 0 (dyadicInt 1) d=1-productDistance k z 0 n/n := by simp only [arrayShortfall,he0,dyadicInt_val,Int.cast_one,ZeroMemClass.coe_zero,sub_zero,div_one]
  have hB:arrayShortfall (dyadicInt 1) (dyadicInt 2) d=1-productDistance k z n (2*n)/n := by simp only [arrayShortfall,he1,dyadicInt_val]; norm_num
  have hJ:arrayJ 0 (dyadicInt 2) d=(productDistance k z 0 n+productDistance k z n (2*n)-productDistance k z 0 (2*n))/(2*n) := by
    rw [arrayJ_eq _ _ (by norm_num),dyadicMid_zero_two,he0,he1,he2]
    norm_num; ring
  have hL:d.val (cutLeft b) (dyadicInt 1)=productDistance k z ((n:ℤ)-s) n/n := by
    apply rescaledDistance_aligned
    · rw [cutLeft_val,Int.cast_sub,Int.cast_natCast,Int.cast_natCast,mul_sub,mul_one,he']
    · simp
  have hR:d.val (dyadicInt 1) (cutRight b)=productDistance k z n ((n:ℤ)+s)/n := by
    apply rescaledDistance_aligned
    · simp
    · rw [cutRight_val,Int.cast_add,Int.cast_natCast,Int.cast_natCast,mul_add,mul_one,he']
  have hLR:d.val (cutLeft b) (cutRight b)=productDistance k z ((n:ℤ)-s) ((n:ℤ)+s)/n := by
    apply rescaledDistance_aligned
    · rw [cutLeft_val,Int.cast_sub,Int.cast_natCast,Int.cast_natCast,mul_sub,mul_one,he']
    · rw [cutRight_val,Int.cast_add,Int.cast_natCast,Int.cast_natCast,mul_add,mul_one,he']
  have hCJ:arrayJ (cutLeft b) (cutRight b) d=(productDistance k z ((n:ℤ)-s) n+productDistance k z n ((n:ℤ)+s)-productDistance k z ((n:ℤ)-s) ((n:ℤ)+s))/(2*s) := by
    rw [arrayJ_eq _ _ (cut_order b),cut_mid,hL,hR,hLR,cutLeft_val,cutRight_val]
    have hnB:(n:ℝ)=s*(2:ℝ)^b := (div_eq_iff (by positivity)).mp he
    rw [hnB]; field_simp; ring
  have hu:unitDefect d=max (1-productDistance k z 0 n/n) (1-productDistance k z n (2*n)/n)+arrayJ 0 (dyadicInt 2) d := by rw [unitDefect,hA,hB]
  have hD:(n:ℝ)-min (productDistance k z n 0) (productDistance k z n (2*n))=
      n*max (1-productDistance k z 0 n/n) (1-productDistance k z n (2*n)/n) := by
    rw [productDistance_symm k z n 0]
    rcases le_total (productDistance k z 0 n) (productDistance k z n (2*n)) with h|h
    · rw [min_eq_left h,max_eq_left (by linarith [div_le_div_of_nonneg_right h hn.le])]; field_simp
    · rw [min_eq_right h,max_eq_right (by linarith [div_le_div_of_nonneg_right h hn.le])]; field_simp
  have ht:=productDistance_truncation k hk z (n:ℤ) n s hsn
  simp only [sub_self,show (n:ℤ)+(n:ℤ)=2*n by ring,productDistance_symm k z (n:ℤ) 0] at ht
  have hbound:productDistance k z 0 n+productDistance k z n (2*n)-productDistance k z 0 (2*n)≤
      2*(s:ℝ)-2*((n:ℝ)-min (productDistance k z n 0) (productDistance k z n (2*n))) := by
    rw [hD]
    have hx':max (1-productDistance k z 0 n/n) (1-productDistance k z n (2*n)/n)+arrayJ 0 (dyadicInt 2) d<1/(2:ℝ)^b := by rwa [←hu]
    have hmul:=mul_lt_mul_of_pos_left hx' hn
    have hjmul:(2*n)*arrayJ 0 (dyadicInt 2) d=productDistance k z 0 n+productDistance k z n (2*n)-productDistance k z 0 (2*n) := by rw [hJ]; field_simp
    rw [he'] at hmul; nlinarith
  rw [productDistance_symm k z n 0] at hbound
  rw [min_eq_left hbound] at ht
  rw [productDistance_symm k z n ((n:ℤ)-s)] at ht
  have hncast : (n:ℝ) = (2:ℝ)^p := by simp [n]
  rw [←hncast]
  change arrayJ 0 (dyadicInt 2) d≤(1/(2:ℝ)^b)*arrayJ (cutLeft b) (cutRight b) d+3/(n:ℝ)
  rw [hJ,hCJ]
  have hqi:1/(2:ℝ)^b=(s:ℝ)/n := (eq_div_iff hn.ne').mpr (by simpa [mul_comm] using he')
  rw [hqi]
  field_simp
  nlinarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_WeightTruncation
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
lemma capG_linear_near_unit {α q:ℝ} {d:DistanceArray} (hx:unitDefect d<q) (hq:q≤1/10000) :
    capG α d=α*arrayJ 0 (dyadicInt 2) d := by
  have hj:=arrayJ_nonneg 0 (dyadicInt 2) (by norm_num) d
  have hm: max (arrayShortfall 0 (dyadicInt 1) d) (arrayShortfall (dyadicInt 1) (dyadicInt 2) d)+arrayJ 0 (dyadicInt 2) d<q := hx
  have h1:arrayShortfall 0 (dyadicInt 1) d≤1/10000 := by linarith [le_max_left (arrayShortfall 0 (dyadicInt 1) d) (arrayShortfall (dyadicInt 1) (dyadicInt 2) d)]
  have h2:arrayShortfall (dyadicInt 1) (dyadicInt 2) d≤1/10000 := by linarith [le_max_right (arrayShortfall 0 (dyadicInt 1) d) (arrayShortfall (dyadicInt 1) (dyadicInt 2) d)]
  have h3:arrayShortfall 0 (dyadicInt 2) d≤1/10000 := by
    simp only [arrayJ,dyadicMid_zero_two] at hm
    linarith [le_max_left (arrayShortfall 0 (dyadicInt 1) d) (arrayShortfall (dyadicInt 1) (dyadicInt 2) d),le_max_right (arrayShortfall 0 (dyadicInt 1) d) (arrayShortfall (dyadicInt 1) (dyadicInt 2) d)]
  simp only [capG,entropyCap_linear h1,entropyCap_linear h2,entropyCap_linear h3,arrayJ,dyadicMid_zero_two]
  ring
lemma cut_alignment (p b:ℕ) (hb:b≤p) :
    ((2^p:ℕ):ℝ)*(cutLeft b:ℝ)=(((2^p:ℤ)-2^(p-b)):ℝ) ∧
    ((2^p:ℕ):ℝ)*(cutRight b:ℝ)=(((2^p:ℤ)-2^(p-b)):ℝ)+2*((2^(p-b):ℕ):ℝ) := by
  have he:(2:ℝ)^p/(2:ℝ)^b=(2:ℝ)^(p-b) := by rw [div_eq_mul_inv,←pow_sub₀ (2:ℝ) (by norm_num) hb]
  rw [cutLeft_val,cutRight_val]
  push_cast
  constructor
  · rw [mul_sub,mul_one,mul_one_div,he]
  · rw [mul_add,mul_one,mul_one_div,he]; ring
lemma integral_cut_test (k:ℝ) (hk:0≤k) (p b l:ℕ) (hb:b≤p) (ε:ℝ) (hε:0<ε) :
    (∫d,arrayTest ⟨(cutLeft b,cutRight b),cut_order b⟩ d ∂scaleLaw k hk p l ε)≤9*meanDeficit k (2^(p-b+l))/ε := by
  have h:=integral_test_scalelaw k hk p l ε hε (cutLeft b) (cutRight b) (cut_order b)
    ((2^p:ℤ)-2^(p-b)) (2^(p-b)) (by positivity) (by simpa only [Int.cast_sub,Int.cast_pow,Int.cast_ofNat] using (cut_alignment p b hb).1) (by simpa only [Int.cast_sub,Int.cast_pow,Int.cast_ofNat] using (cut_alignment p b hb).2)
  simpa only [pow_add] using h
lemma weight_unit_scale_bound (k:ℝ) (hk:0≤k) (p b l:ℕ) (hb:b≤p) (ε:ℝ) (hε:0<ε)
    {α:ℝ} (hα:0≤α) (hq:1/(2:ℝ)^b≤1/10000) (F:DistanceArray→ℝ) (hF:Continuous F)
    (hFB:∀d,F d≤|capG α d|) (hz:∀d,¬unitDefect d<1/(2:ℝ)^b → F d=0) :
    (∫d,F d ∂scaleLaw k hk p l ε)≤
      α*((1/(2:ℝ)^b)*(9*meanDeficit k (2^(p-b+l))/ε)+6/(((2^p:ℕ):ℝ)*ε)) := by
  let Jc:DistanceArray→ℝ:=arrayJ (cutLeft b) (cutRight b)
  have hB (j:ℕ) (z:Torus):F (sampleArray k hk z (2^(p+j)) (by positivity))≤
      α*((1/(2:ℝ)^b)*Jc (sampleArray k hk z (2^(p+j)) (by positivity))+3/(2:ℝ)^(p+j)) := by
    let d:=sampleArray k hk z (2^(p+j)) (by positivity)
    by_cases hx:unitDefect d<1/(2:ℝ)^b
    · have ht:=truncation_array_bound k hk z (p+j) b (by omega) hx
      have hg:|capG α d|=α*arrayJ 0 (dyadicInt 2) d := by
        rw [capG_linear_near_unit hx hq,abs_of_nonneg (mul_nonneg hα (arrayJ_nonneg _ _ (by norm_num) d))]
      exact (hFB d).trans (hg.le.trans (mul_le_mul_of_nonneg_left ht hα))
    · rw [hz d hx]
      exact mul_nonneg hα (add_nonneg (mul_nonneg (by positivity) (arrayJ_nonneg _ _ (cut_order b) d)) (by positivity))
  have hsamp (j:ℕ):(∫d,F d ∂sampleLaw k hk (2^(p+j)) (by positivity))≤
      α*((1/(2:ℝ)^b)*(∫d,Jc d ∂sampleLaw k hk (2^(p+j)) (by positivity))+3/(2:ℝ)^(p+j)) := by
    rw [integral_sampleLaw _ _ _ _ _ hF,integral_sampleLaw _ _ _ _ _ (continuous_arrayJ _ _)]
    have hc:Continuous (fun z:Torus => Jc (sampleArray k hk z (2^(p+j)) (by positivity))) :=
      (continuous_arrayJ _ _).comp (continuous_sampleArray _ _ _ _)
    have h:=integral_mono (μ:=area) ((hF.comp (continuous_sampleArray _ _ _ _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (((hc.const_mul _).add continuous_const).const_mul α |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (hB j)
    have hi : Integrable (fun z:Torus => Jc (sampleArray k hk z (2^(p+j)) (by positivity))) area := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simp only [Function.comp_apply,Pi.add_apply] at h
    simpa [integral_const_mul,integral_add (hi.const_mul _) (integrable_const _)] using h
  have hsum: (∑j∈Finset.range l,∫d,F d ∂sampleLaw k hk (2^(p+j)) (by positivity)) ≤
      α*((1/(2:ℝ)^b)*(∑j∈Finset.range l,∫d,Jc d ∂sampleLaw k hk (2^(p+j)) (by positivity))+6/((2^p:ℕ):ℝ)) := by
    have h:=Finset.sum_le_sum (fun j (_:j∈Finset.range l) => hsamp j)
    simp only [Finset.sum_add_distrib,←Finset.mul_sum] at h
    have herr:(∑j∈Finset.range l,3/(2:ℝ)^(p+j))≤6/((2^p:ℕ):ℝ) := by
      have he:∀j:ℕ,3/(2:ℝ)^(p+j)=3*(1/(((2^p)*2^j:ℕ):ℝ)) := by intro j; push_cast; rw [pow_add]; ring
      simp_rw [he]; rw [←Finset.mul_sum]
      have h:=sum_scaled_inverse (2^p) l (by positivity)
      convert! mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤3) using 1 ; ring
    exact h.trans (mul_le_mul_of_nonneg_left (add_le_add_right herr _) hα)
  rw [integral_scaleLaw _ _ _ _ _ hε F hF]
  have hJ : (∫d,Jc d ∂scaleLaw k hk p l ε)≤9*meanDeficit k (2^(p-b+l))/ε := by
    refine (integral_mono ((continuous_arrayJ _ _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((continuous_arrayTest _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (fun d => ?_)).trans (integral_cut_test k hk p b l hb ε hε)
    exact le_add_of_nonneg_right (arrayV_nonneg _ _ d)
  rw [integral_scaleLaw _ _ _ _ _ hε Jc (continuous_arrayJ _ _)] at hJ
  have hh:=div_le_div_of_nonneg_right hsum hε.le
  apply hh.trans
  have hmul:=mul_le_mul_of_nonneg_left hJ (mul_nonneg hα (by positivity : 0≤1/(2:ℝ)^b))
  calc
    _ = α*(1/(2:ℝ)^b)*((∑j∈Finset.range l,∫d,Jc d ∂sampleLaw k hk (2^(p+j)) (by positivity))/ε)+α*(6/(((2^p:ℕ):ℝ)*ε)) := by ring
    _ ≤ _ := by nlinarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_WeightedCompact
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
lemma open_measure_le_of_integral_bound {X:Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [RegularSpace X]
    (μ:Measure X) [μ.Regular] {U:Set X} (hU:IsOpen U) (C:ℝ)
    (hb:∀g:C_c(X,ℝ),(∀x,0≤g x) → (∀x,g x≤1) → (∀x∉U,g x=0) → ∫x,g x ∂μ≤C) :
    μ U≤ENNReal.ofReal C := by
  rw [hU.measure_eq_iSup_isCompact μ]
  simp only [iSup_le_iff]
  intro K hKU hK
  obtain ⟨⟨f,hfc⟩,hfK,hfU,hfs,hfr⟩:=exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKU)
  let g:C_c(X,ℝ):=⟨⟨f,hfc⟩,hfs⟩
  have hh:=hb g (fun x => (hfr x).1) (fun x => (hfr x).2) (fun x hx => hfU hx)
  have hμ:μ K≤ENNReal.ofReal (∫x,g x ∂μ) := (hfc.integrable_of_hasCompactSupport hfs).measure_le_integral (Eventually.of_forall (fun x => (hfr x).1)) (fun x hx => (hfK hx).ge)
  exact hμ.trans (ENNReal.ofReal_le_ofReal hh)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_WeightSlow
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
lemma isOpen_slowCapOpen : IsOpen slowCapOpen :=
  isOpen_lt continuous_const ((continuous_arrayShortfall _ _).min (continuous_arrayShortfall _ _))
lemma capG_zero_slowOpen {α:ℝ} {d:DistanceArray} (hd:d∈slowCapOpen) : capG α d=0 := by
  have h1 : 3/10000 < arrayShortfall 0 (dyadicInt 1) d := hd.trans_le (min_le_left _ _)
  have h2 : 3/10000 < arrayShortfall (dyadicInt 1) (dyadicInt 2) d := hd.trans_le (min_le_right _ _)
  have hj:=arrayJ_nonneg 0 (dyadicInt 2) (by norm_num) d
  simp only [arrayJ,dyadicMid_zero_two] at hj
  have h3 : 3/10000 ≤ arrayShortfall 0 (dyadicInt 2) d := by linarith
  simp only [capG,entropyCap_one h1.le,entropyCap_one h2.le,entropyCap_one h3]
  norm_num
lemma affine_shortfall (w:Icc (0:ℝ) 1) (s t:DyadicTime) (hst:(s:ℝ)<(t:ℝ)) :
    arrayShortfall s t (affineArray w)=1-w.val := by
  change 1-w.val*|(t:ℝ)-(s:ℝ)|/((t:ℝ)-(s:ℝ))=1-w.val
  rw [abs_of_pos (sub_pos.mpr hst),mul_div_cancel_right₀ _ (sub_ne_zero.mpr hst.ne')]
lemma affine_mem_slowOpen (w:Icc (0:ℝ) 1) (hw:w.val≤999/1000) : affineArray w∈slowCapOpen := by
  change (3/10000:ℝ) < min _ _
  rw [affine_shortfall _ _ _ (by norm_num),affine_shortfall _ _ _ (by norm_num),min_self]
  linarith
namespace CompactWeightLimit
variable {ι:Type*} {l:Filter ι} [l.NeBot] {μ:ι→Measure DistanceArray} {f:DistanceArray→ℝ}
variable (Q:CompactWeightLimit l μ f)
lemma open_null {U:Set DistanceArray} (hU:IsOpen U)
    (hconv:∀g:C_c(DistanceArray,ℝ),(∀d,0≤g d) → (∀d∉U,g d=0) →
      Tendsto (fun i => ∫d,g d*f d ∂μ i) l (𝓝 0)) : Q.law U=0 := by
  have:=Q.regular
  apply open_null_of_integral_zero Q.law hU
  intro g h0 hz
  exact tendsto_nhds_unique (Q.converges g.toContinuousMap) (hconv g h0 hz)
lemma slow_null {α:ℝ} (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) : Q.law slowCapOpen=0 := by
  apply Q.open_null isOpen_slowCapOpen
  intro g hg hz
  have he:∀d,g d*f d=0 := by
    intro d
    by_cases hd:d∈slowCapOpen
    · have hf:f d=0 := le_antisymm (by simpa [capG_zero_slowOpen hd] using hb d) (h0 d)
      rw [hf,mul_zero]
    · rw [hz d hd,zero_mul]
  simp only [he,integral_zero]
  exact tendsto_const_nhds
end CompactWeightLimit
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_WeightUnit
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
lemma isOpen_unitCapOpen (b:ℕ) : IsOpen (unitCapOpen b) :=
  isOpen_lt continuous_unitDefect continuous_const
lemma unitAffine_mem_unitCapOpen (b:ℕ) : unitAffine∈unitCapOpen b := by
  change unitDefect (affineArray _) < _
  simp only [unitDefect,arrayJ,dyadicMid_zero_two]
  rw [affine_shortfall _ _ _ (by norm_num),affine_shortfall _ _ _ (by norm_num),affine_shortfall _ _ _ (by norm_num)]
  norm_num
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma weight_unit_integral_bound {α:ℝ} (hα:0≤α) (f:DistanceArray→ℝ) (hf:Continuous f)
    (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) (Q:CompactWeightLimit (L.filter:Filter ℕ) S.multiLaw f)
    (b:ℕ) (hsmall:1/(2:ℝ)^b≤1/10000) (g:C_c(DistanceArray,ℝ))
    (_hg:∀d,0≤g d) (hg1:∀d,g d≤1) (hz:∀d∉unitCapOpen b,g d=0) :
    (∫d,g d ∂Q.law)≤9*α/(2:ℝ)^b := by
  let F:DistanceArray→ℝ:=fun d=>g d*f d
  have hFB:∀d,F d≤|capG α d| := fun d => (mul_le_of_le_one_left (h0 d) (hg1 d)).trans (hb d)
  have hFz:∀d,¬unitDefect d<1/(2:ℝ)^b → F d=0 := by
    intro d hd; dsimp only [F]; rw [hz d hd,zero_mul]
  have hu:∀ᶠi in atTop,(∫d,F d ∂S.multiLaw i)≤α*((1/(2:ℝ)^b)*9+6*criticalTheta S.offset i) := by
    filter_upwards [S.lowerExponent_tendsto.eventually_ge_atTop b] with i hi
    have h:=weight_unit_scale_bound (S.parameter i) (S.positive i).le
      (criticalLowerExponent S.offset i) b (S.exponent i-criticalLowerExponent S.offset i) hi
      (S.epsilon i) (S.epsilon_pos i) hα hsmall F (g.continuous.mul hf) hFB hFz
    apply h.trans
    have hm:meanDeficit (S.parameter i) (2^(criticalLowerExponent S.offset i-b+(S.exponent i-criticalLowerExponent S.offset i)))≤S.epsilon i := by
      exact meanDeficit_pow_mono _ (S.positive i).le (by have := S.lower_lt i; omega)
    have hr:9*meanDeficit (S.parameter i) (2^(criticalLowerExponent S.offset i-b+(S.exponent i-criticalLowerExponent S.offset i)))/S.epsilon i≤9 := by
      apply (div_le_iff₀ (S.epsilon_pos i)).mpr; linarith
    have hE:=mul_le_mul_of_nonneg_left (S.inverse_scale_epsilon_bound i _ le_rfl) (by norm_num : (0:ℝ)≤6)
    apply mul_le_mul_of_nonneg_left _ hα
    apply add_le_add (mul_le_mul_of_nonneg_left hr (by positivity))
    convert hE using 1 <;> first | rfl | ring
  have ht:Tendsto (fun i => α*((1/(2:ℝ)^b)*9+6*criticalTheta S.offset i)) (L.filter:Filter ℕ) (𝓝 (9*α/(2:ℝ)^b)) := by
    convert! (((criticalTheta_tendsto S.offset).const_mul 6).const_add ((1/(2:ℝ)^b)*9)).const_mul α |>.mono_left L.refines using 1 ; ring_nf
  exact le_of_tendsto_of_tendsto (Q.converges g.toContinuousMap) ht (hu.filter_mono L.refines)
lemma weight_unit_open_bound {α:ℝ} (hα:0≤α) (f:DistanceArray→ℝ) (hf:Continuous f)
    (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) (Q:CompactWeightLimit (L.filter:Filter ℕ) S.multiLaw f)
    (b:ℕ) (hsmall:1/(2:ℝ)^b≤1/10000) : Q.law (unitCapOpen b)≤ENNReal.ofReal (9*α/(2:ℝ)^b) := by
  have:=Q.regular
  have:=Q.finite
  apply open_measure_le_of_integral_bound Q.law (isOpen_unitCapOpen b) _
  exact S.weight_unit_integral_bound L hα f hf h0 hb Q b hsmall
lemma weight_unit_null {α:ℝ} (hα:0≤α) (f:DistanceArray→ℝ) (hf:Continuous f)
    (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) (Q:CompactWeightLimit (L.filter:Filter ℕ) S.multiLaw f) :
    Q.law {unitAffine}=0 := by
  have ht:Tendsto (fun b:ℕ => 1/(2:ℝ)^b) atTop (𝓝 0) := by
    simpa only [div_pow,one_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have hh:∀ᶠb:ℕ in atTop,Q.law {unitAffine}≤ENNReal.ofReal (9*α/(2:ℝ)^b) := by
    filter_upwards [ht.eventually_le_const (by norm_num : (0:ℝ)<1/10000)] with b hb'
    exact (measure_mono (singleton_subset_iff.mpr (unitAffine_mem_unitCapOpen b))).trans (S.weight_unit_open_bound L hα f hf h0 hb Q b hb')
  have he:Tendsto (fun b:ℕ => ENNReal.ofReal (9*α/(2:ℝ)^b)) atTop (𝓝 0) := by
    have h:=ENNReal.continuous_ofReal.continuousAt.tendsto.comp (ht.const_mul (9*α))
    convert! h using 1 <;> simp [div_eq_mul_inv,Function.comp_def]
  exact le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds he hh) bot_le
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_WeightBridge
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
lemma isOpen_middleCapOpen (η:ℝ) : IsOpen (middleCapOpen η) :=
  (isOpen_lt continuous_const (continuous_arrayEval (dyadicInt 1) (dyadicInt 4097))).inter
    ((isOpen_lt continuous_const (continuous_clippedShortfall _ _)).inter
      ((isOpen_lt continuous_const (continuous_arrayShortfall _ _)).inter (isOpen_lt continuous_const (continuous_arrayShortfall _ _))))
lemma affine_mem_middleOpen (w:Icc (0:ℝ) 1) {η:ℝ} (hw:999/1000<w.val) (he:η<1-w.val) (hw1:w.val<1) :
    affineArray w∈middleCapOpen η := by
  have h0 : 0≤1-w.val := by linarith [w.property.2]
  have h1 : 1-w.val≤1 := by linarith [w.property.1]
  change _ ∧ η < unitClip (arrayShortfall _ _ _) ∧ _
  rw [affine_shortfall _ _ _ (by norm_num),unitClip_eq ⟨h0,h1⟩,
    affine_shortfall _ _ _ (by norm_num),affine_shortfall _ _ _ (by norm_num)]
  refine ⟨?_,he,by linarith,by linarith⟩
  change (999/1000:ℝ)*4096 < w.val*|(dyadicInt 4097:ℝ)-(dyadicInt 1:ℝ)|
  norm_num; nlinarith
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence)
lemma weight_middle_null (L:S.LimitLaws) {α:ℝ} (f:DistanceArray→ℝ) (hf:Continuous f)
    (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) (Q:CompactWeightLimit (L.filter:Filter ℕ) S.multiLaw f)
    {η:ℝ} (hη:0<η) : Q.law (middleCapOpen η)=0 := by
  apply Q.open_null (isOpen_middleCapOpen η)
  intro g hg hz
  exact (S.middle_weight_tendsto_q44 hη f hf h0 hb g hg hz).mono_left L.refines
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_WeightBalance
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
lemma affine_cap_cover : affineLocus ⊆ slowCapOpen∪(⋃q:{q:ℚ // 0<q},middleCapOpen (q.val:ℝ))∪{unitAffine} := by
  rintro d ⟨w,rfl⟩
  by_cases hw:w.val≤999/1000
  · exact Or.inl (Or.inl (affine_mem_slowOpen w hw))
  by_cases hw1:w.val<1
  · obtain ⟨q,hq,hqw⟩:=exists_rat_btwn (sub_pos.mpr hw1)
    have hq':0<q := by exact_mod_cast hq
    exact Or.inl (Or.inr (mem_iUnion.mpr ⟨⟨q,hq'⟩,affine_mem_middleOpen w (lt_of_not_ge hw) hqw hw1⟩))
  · have he:w=⟨1,by norm_num⟩ := Subtype.ext (le_antisymm w.property.2 (le_of_not_gt hw1))
    exact Or.inr (by rw [he]; rfl)
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma weight_affine_null_q44_oai {α:ℝ} (hα:0≤α) (f:DistanceArray→ℝ) (hf:Continuous f)
    (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) (Q:CompactWeightLimit (L.filter:Filter ℕ) S.multiLaw f) :
    Q.law affineLocus=0 := by
  apply measure_mono_null affine_cap_cover
  apply measure_union_null
  · apply measure_union_null (Q.slow_null h0 hb)
    apply measure_iUnion_null
    intro q
    exact S.weight_middle_null L f hf h0 hb Q (by exact_mod_cast q.property)
  · exact S.weight_unit_null L hα f hf h0 hb Q
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.CriticalScaleSequence.weight_affine_null_q44_oai := @OAI.StandardMapEntropy.CriticalScaleSequence.weight_affine_null_q44_oai
