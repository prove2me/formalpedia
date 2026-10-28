-- Prove2me | solution 1 for OAI.StandardMapEntropy.CriticalScaleSequence.terminal_event_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T00:24:33.826318+00:00
-- url     : https://prove2.me/submissions/aa9c047c-e6f8-49cd-a682-e054d6af0897

import Mathlib
import Definitions.Def_StandardMapEntropy
import Definitions.Def_OAIQ2St000
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_dyadicBridge_aeselected
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_noCancellation_aeterminal

section
-- module Solutions.OAIQ2_Std.StandardMap_LocalScarcity
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
-- module Solutions.OAIQ2_Std.StandardMap_PlaneGeometry
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
-- module Solutions.OAIQ2_Std.StandardMap_PlaneTransfer
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
-- module Solutions.OAIQ2_Std.StandardMap_ObservationTransport
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
lemma transferStep_difference_bound (v w : ℝ) : ‖transferStep v-transferStep w‖ ≤ |v-w| := by
  apply (transferStep v-transferStep w).opNorm_le_bound (abs_nonneg _)
  intro z
  have he : (transferStep v-transferStep w) z=((v-w)*z.re : ℝ) := by
    apply Complex.ext <;> simp only [sub_apply,Complex.sub_re,Complex.sub_im,
      transferStep_re,transferStep_im,Complex.ofReal_re,Complex.ofReal_im] <;> ring
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg _)

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_SegmentObservations
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
-- module Solutions.OAIQ2_Std.StandardMap_TorusDynamics
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
lemma torusIter_add (k : ℝ) (i j : ℤ) (z : Torus) :
    torusIter k (i+j) z=torusIter k i (torusIter k j z) := by
  simp only [torusIter,zpow_add,Equiv.Perm.coe_mul,Function.comp_apply]
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
-- module Solutions.OAIQ2_Std.StandardMap_ClosedEligibility
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

lemma continuous_transferStep : Continuous transferStep := by
  apply Metric.continuous_iff.mpr
  intro v ε hε
  refine ⟨ε,hε,?_⟩
  intro w hw
  rw [dist_eq_norm]
  exact (transferStep_difference_bound w v).trans_lt (by simpa only [Real.dist_eq] using hw)

lemma continuous_transferProduct_params {α : Type*} [TopologicalSpace α]
    (v : α → ℕ → ℝ) (hv : ∀ n, Continuous (fun x => v x n)) (n : ℕ) :
    Continuous (fun x => transferProduct (v x) n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (continuous_transferStep.comp (hv (n+1))).clm_comp ih

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TorusObservations
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
lemma continuous_cosine : Continuous cosine := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  change Continuous (fun x : ℝ => cosine (x : Circle))
  simpa only [cosine_coe,Function.comp_def,Pi.mul_apply,id_eq] using
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))
lemma continuous_torusPotential (k : ℝ) : Continuous (torusPotential k) :=
  continuous_const.add (continuous_const.mul continuous_cosine)
lemma continuous_torusSegmentCoefficient (k : ℝ) (a : ℤ) (i : ℕ) :
    Continuous (fun z => torusSegmentCoefficient k z a i) :=
  (continuous_torusPotential k).comp (continuous_fst.comp (continuous_torusIter k _))
lemma continuous_torusSegmentTransfer (k : ℝ) (a : ℤ) (n : ℕ) :
    Continuous (fun z => torusSegmentTransfer k z a n) :=
  continuous_transferProduct_params (fun z i => torusSegmentCoefficient k z a i)
    (fun i => continuous_torusSegmentCoefficient k a i) n
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
-- module Solutions.OAIQ2_Std.StandardMap_CocycleAlgebra
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
lemma torusSegmentTransfer_shift (k : ℝ) (z : Torus) (a b : ℤ) (n : ℕ) :
    torusSegmentTransfer k (torusIter k b z) a n=torusSegmentTransfer k z (a+b) n := by
  unfold torusSegmentTransfer
  congr 1
  funext i
  unfold torusSegmentCoefficient
  rw [← torusIter_add]
  congr 3
  ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_FourPoint
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
-- module Solutions.OAIQ2_Std.StandardMap_ProductDistances
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
lemma productDistance_forward (k : ℝ) (z : Torus) (i : ℤ) (n : ℕ) :
    productDistance k z i (i+(n:ℤ))=Real.log ‖torusSegmentTransfer k z i n‖/Real.log (growthBase k) := by
  simp only [productDistance,torusTransfer_forward]
lemma productDistance_shift (k : ℝ) (z : Torus) (i j a : ℤ) :
    productDistance k (torusIter k a z) i j=productDistance k z (i+a) (j+a) := by
  wlog hij : i≤j generalizing i j
  · rw [productDistance_symm k _ i j,productDistance_symm k _ (i+a) (j+a)]
    exact this j i (le_of_not_ge hij)
  have hn : i+((j-i).toNat:ℤ)=j := by rw [Int.toNat_of_nonneg (sub_nonneg.mpr hij)]; ring
  have hn' : i+a+((j-i).toNat:ℤ)=j+a := by omega
  rw [← hn,productDistance_forward]
  conv_rhs => rw [show i+((j-i).toNat:ℤ)+a=i+a+((j-i).toNat:ℤ) by ring]
  rw [productDistance_forward,torusSegmentTransfer_shift]
lemma continuous_productDistance (k : ℝ) (hk : 0≤k) (i j : ℤ) :
    Continuous (fun z => productDistance k z i j) := by
  wlog hij : i≤j generalizing i j
  · have hh := this j i (le_of_not_ge hij)
    simpa only [productDistance_symm k _ j i] using hh
  have hn : i+((j-i).toNat:ℤ)=j := by rw [Int.toNat_of_nonneg (sub_nonneg.mpr hij)]; ring
  rw [← hn]
  simp only [productDistance_forward]
  apply Continuous.div_const
  exact (continuous_torusSegmentTransfer k i _).norm.log (fun z => by
    have := (torusSegmentTransfer_norm_bounds k hk z i (j-i).toNat).1; linarith)
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
-- module Solutions.OAIQ2_Std.StandardMap_SmoothCap
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
-- module Solutions.OAIQ2_Std.StandardMap_SmoothControl
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
lemma entropyCap_upper {α : ℝ} (hα : 0≤α) (hα1 : α≤1) :
    ∃C>0,∀u∈Icc (0:ℝ) 1,entropyCap α u≤C*u := by
  obtain ⟨C,hC,h1,_⟩ := c2_compact_bounds (entropyCap_contDiff α) 0 1
  refine ⟨C+1,by linarith,?_⟩
  intro u hu
  have hh := deriv_bound_lipschitz ((entropyCap_contDiff α).differentiable (by norm_num)) h1
    (by constructor <;> norm_num : (0:ℝ)∈Icc 0 1) hu
  rw [entropyCap_linear (u := 0) (by norm_num),mul_zero,sub_zero,sub_zero,abs_of_nonneg hu.1,
    abs_of_nonneg (entropyCap_bounds hα hα1 hu).1] at hh
  nlinarith [hu.1]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_MeanDeficit
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_FixedDeficit
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
-- module Solutions.OAIQ2_Std.StandardMap_CriticalSequence
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
-- module Solutions.OAIQ2_Std.StandardMap_ArrayTests
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
-- module Solutions.OAIQ2_Std.StandardMap_ArrayGrid
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
lemma dyadic_zsmul_val (i : ℤ) (h : DyadicTime) : ((i • h : DyadicTime):ℝ)=(i:ℝ)*(h:ℝ) := by
  simp only [AddSubgroup.coe_zsmul,zsmul_eq_mul]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ArrayAffinity
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
-- module Solutions.OAIQ2_Std.StandardMap_RescaledArrays
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
lemma sampleArray_translate (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) (hn : 0<n)
    (r : DyadicTime) (a : ℤ) (ha : (n:ℝ)*(r:ℝ)=(a:ℝ)) :
    arrayTranslate r (sampleArray k hk z n hn)=sampleArray k hk (torusIter k a z) n hn := by
  apply Subtype.ext
  funext s t
  change productDistance k z ⌊(n:ℝ)*(↑(s+r):ℝ)⌋ ⌊(n:ℝ)*(↑(t+r):ℝ)⌋/(n:ℝ)=
    productDistance k (torusIter k a z) ⌊(n:ℝ)*(s:ℝ)⌋ ⌊(n:ℝ)*(t:ℝ)⌋/(n:ℝ)
  rw [productDistance_shift]
  simp only [AddSubgroup.coe_add,mul_add,ha,Int.floor_add_intCast]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_SampleLaws
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
lemma sampleLaw_translate (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n)
    (r : DyadicTime) (a : ℤ) (ha : (n:ℝ)*(r:ℝ)=(a:ℝ)) :
    (sampleLaw k hk n hn).map (arrayTranslate r)=sampleLaw k hk n hn := by
  unfold sampleLaw
  rw [Measure.map_map (continuous_arrayTranslate r).measurable (continuous_sampleArray k hk n hn).measurable]
  have he : (arrayTranslate r) ∘ (fun z => sampleArray k hk z n hn)=
      (fun z => sampleArray k hk z n hn) ∘ (torusIter k a) := by
    funext z; exact sampleArray_translate k hk z n hn r a ha
  rw [he,← Measure.map_map (continuous_sampleArray k hk n hn).measurable (continuous_torusIter k a).measurable,
    (measurePreserving_torusIter k a).map_eq]
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
-- module Solutions.OAIQ2_Std.StandardMap_ScaleLaws
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
lemma scaleLaw_translate (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) (r : DyadicTime)
    (a : ℤ) (ha : ((2^p:ℕ):ℝ)*(r:ℝ)=(a:ℝ)) :
    (scaleLaw k hk p l ε).map (arrayTranslate r)=scaleLaw k hk p l ε := by
  unfold scaleLaw
  rw [Measure.map_smul,Measure.map_finset_sum (continuous_arrayTranslate r).measurable.aemeasurable]

  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply sampleLaw_translate k hk _ _ r (a*2^i)
  push_cast at ha ⊢
  rw [pow_add]
  calc
    _ = (((2:ℝ)^p)*(r:ℝ))*(2:ℝ)^i := by ring
    _ = _ := by rw [ha]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ScaleTestBounds
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_CriticalLaws
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
-- module Solutions.OAIQ2_Std.StandardMap_NonaffineLimits
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
-- module Solutions.OAIQ2_Std.StandardMap_ArrayActions
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
-- module Solutions.OAIQ2_Std.StandardMap_LimitActions
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma arrayTestExtend_translate (g : C_c(NonAffineArray,ℝ)) (r : DyadicTime) (d : DistanceArray) :
    arrayTestExtend (g.comp (nonaffineTranslation r).toCocompactMap) d=
      arrayTestExtend g (arrayTranslate r d) := by
  by_cases hd : d∈affineLocus
  · rw [arrayTestExtend_affine _ d hd,arrayTestExtend_affine _ _ ((arrayTranslate_mem_affine_iff r d).mpr hd)]
  · exact (arrayTestExtend_apply _ ⟨d,hd⟩).trans (arrayTestExtend_apply g (nonaffineTranslation r ⟨d,hd⟩)).symm
lemma integral_translate_nonaffine (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (r : DyadicTime) (hμ : μ.map (arrayTranslate r)=μ) (g : C_c(NonAffineArray,ℝ)) :
    (∫ d,(g.comp (nonaffineTranslation r).toCocompactMap) d ∂nonaffinePart μ)=
      ∫ d,g d ∂nonaffinePart μ := by
  rw [← integral_arrayTestExtend,← integral_arrayTestExtend]
  simp_rw [arrayTestExtend_translate]
  rw [← integral_map (f := fun d => arrayTestExtend g d) (continuous_arrayTranslate r).measurable.aemeasurable (arrayTestExtend g).continuous.aestronglyMeasurable,hμ]
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma terminalLaw_translate_eventually (r : DyadicTime) :
    ∀ᶠ i in atTop, (S.terminalLaw i).map (arrayTranslate r)=S.terminalLaw i := by
  obtain ⟨p,hp⟩ := dyadic_aligned_eventually r
  filter_upwards [S.exponent_tendsto.eventually_ge_atTop p] with i hi
  obtain ⟨a,ha⟩ := hp _ hi
  exact scaleLaw_translate _ _ _ _ _ r a ha
lemma terminal_integral_translate (r : DyadicTime) (g : C_c(NonAffineArray,ℝ)) :
    (∫ d,g (nonaffineTranslation r d) ∂L.terminal)=∫ d,g d ∂L.terminal := by
  have hh : (fun i => ∫ d,(g.comp (nonaffineTranslation r).toCocompactMap) d ∂nonaffinePart (S.terminalLaw i))
      =ᶠ[L.filter] (fun i => ∫ d,g d ∂nonaffinePart (S.terminalLaw i)) := by
    filter_upwards [L.refines (S.terminalLaw_translate_eventually r)] with i hi
    exact integral_translate_nonaffine (S.terminalLaw i) r hi g
  exact tendsto_nhds_unique (L.terminal_converges (g.comp (nonaffineTranslation r).toCocompactMap))
    ((L.terminal_converges g).congr' hh.symm)
lemma terminal_translate (r : DyadicTime) : L.terminal.map (nonaffineTranslation r)=L.terminal := by
  let := Measure.Regular.map (μ := L.terminal) (nonaffineTranslation r)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  rw [integral_map (f := fun d => g d) (nonaffineTranslation r).continuous.measurable.aemeasurable g.continuous.aestronglyMeasurable]
  exact S.terminal_integral_translate L r g
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_VagueSupport
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
-- module Solutions.OAIQ2_Std.StandardMap_RealArrays
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
-- module Solutions.OAIQ2_Std.StandardMap_ArrayLimitSupport
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
-- module Solutions.OAIQ2_Std.StandardMap_HalfDecomposition
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
lemma map_iterate_succ {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → X) (hf : Measurable f) (n : ℕ) :
    (μ.map (f^[n])).map f=μ.map (f^[n+1]) := by
  rw [Measure.map_map hf (hf.iterate n)]
  congr 1
  exact funext (fun x => (Function.iterate_succ_apply' f n x).symm)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TreeLine
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

lemma matched_ray_distance {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {a b u v s : ℝ}
    (_hab : a ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s)
    (hsu : s ≤ u) (hsv : s ≤ v) (hr : ExteriorUnitRays d a b)
    (hmatch : d (a-u) (b+v)=u+v-d a b-2*s) :
    d (a-s) (b+s) ≤ 3*d a b := by
  have hu0 : d a (a-u)=u := by rw [hr.1 _ _ (le_refl _) (by linarith)]; rw [abs_of_nonpos (by linarith)]; ring
  have hs0 : d a (a-s)=s := by rw [hr.1 _ _ (le_refl _) (by linarith)]; rw [abs_of_nonpos (by linarith)]; ring
  have hus : d (a-u) (a-s)=u-s := by rw [hr.1 _ _ (by linarith) (by linarith)]; rw [abs_of_nonneg (by linarith)]; ring
  have hv0 : d b (b+v)=v := by rw [hr.2 _ _ (le_refl _) (by linarith)]; rw [abs_of_nonneg (by linarith)]; ring
  have hs1 : d b (b+s)=s := by rw [hr.2 _ _ (le_refl _) (by linarith)]; rw [abs_of_nonneg (by linarith)]; ring
  have hvs : d (b+v) (b+s)=v-s := by rw [hr.2 _ _ (by linarith) (by linarith)]; rw [abs_of_nonpos (by linarith)]; ring
  have hvlow : v-d a b ≤ d a (b+v) := by
    have h := hd.triangle b a (b+v)
    rw [hv0,hd.symm b a] at h
    linarith
  have hslow : s-d a b ≤ d a (b+s) := by
    have h := hd.triangle b a (b+s)
    rw [hs1,hd.symm b a] at h
    linarith
  have hshigh : d a (b+s) ≤ d a b+s := by simpa only [hs1] using hd.triangle a b (b+s)
  have hB1 : 2*s ≤ lineB d a (a-s) (a-u) := by
    rw [hd.b_symm a (a-s) (a-u)]
    simp only [lineB,hu0,hs0,hus]; linarith
  have hB2 : 2*s ≤ lineB d a (a-u) (b+v) := by simp only [lineB,hu0,hmatch]; linarith
  have hB3 : 2*s-2*d a b ≤ lineB d a (b+v) (b+s) := by simp only [lineB,hvs]; linarith
  have hB4 : 2*s ≤ lineB d a (a-s) (b+v) :=
    (le_min hB1 hB2).trans (hd.min_b a (a-s) (a-u) (b+v))
  have hB5 : 2*s-2*d a b ≤ lineB d a (a-s) (b+s) :=
    (le_min (by linarith [hd.nonneg a b]) hB3).trans (hd.min_b a (a-s) (b+v) (b+s))
  simp only [lineB,hs0] at hB5
  linarith
lemma crossing_excess_bound {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {a b u v δ : ℝ}
    (hab : a ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v) (hδ : 0 < δ)
    (hr : ExteriorUnitRays d a b) (hc : NoFastCancellation d δ) :
    (u+v-d a b-d (a-u) (b+v))/2 ≤ 3*(b-a)/δ := by
  let s := (u+v-d a b-d (a-u) (b+v))/2
  have hD : d a b ≤ b-a := by simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hd.unit a b
  by_contra hn
  have hbad : 3*(b-a)/δ < s := lt_of_not_ge hn
  have hs : 0 < s := lt_of_le_of_lt (div_nonneg (by linarith) hδ.le) hbad
  have hv0 : d b (b+v)=v := by rw [hr.2 _ _ (le_refl _) (by linarith),abs_of_nonneg (by linarith)]; ring
  have hu0 : d (a-u) a=u := by rw [hr.1 _ _ (by linarith) (le_refl _),abs_of_nonneg (by linarith)]; ring
  have hlowu : u-d a b-v ≤ d (a-u) (b+v) := by
    have h1 := hd.triangle (a-u) (b+v) a
    have h2 := hd.triangle (b+v) b a
    rw [hu0] at h1
    rw [hd.symm (b+v) b,hv0,hd.symm b a] at h2
    linarith
  have hlowv : v-d a b-u ≤ d (a-u) (b+v) := by
    have h1 := hd.triangle b (a-u) (b+v)
    have h2 := hd.triangle b a (a-u)
    rw [hv0] at h1
    rw [hd.symm b a,hd.symm a (a-u),hu0] at h2
    linarith
  have hsu : s ≤ u := by dsimp [s]; linarith
  have hsv : s ≤ v := by dsimp [s]; linarith
  have hmatch : d (a-u) (b+v)=u+v-d a b-2*s := by dsimp [s]; ring
  have hm := matched_ray_distance hd hab hu hv hs.le hsu hsv hr hmatch
  let m := (a+b)/2
  let t := s+(b-a)/2
  have ht : 0 < t := by dsimp [t]; linarith
  have hxl : m-t=a-s := by dsimp [m,t]; ring
  have hxr : m+t=b+s := by dsimp [m,t]; ring
  have hsa : d (a-s) a=s := by rw [hr.1 _ _ (by linarith) (le_refl _),abs_of_nonneg (by linarith)]; ring
  have hbs : d b (b+s)=s := by rw [hr.2 _ _ (le_refl _) (by linarith),abs_of_nonneg (by linarith)]; ring
  have hma : d m a ≤ (b-a)/2 := by
    have h := hd.unit m a
    rw [abs_of_nonpos (by dsimp [m]; linarith)] at h
    dsimp [m] at h; linarith
  have hmb : d m b ≤ (b-a)/2 := by
    have h := hd.unit m b
    rw [abs_of_nonneg (by dsimp [m]; linarith)] at h
    dsimp [m] at h; linarith
  have hl := hd.triangle (a-s) m a
  have hh := hd.triangle b m (b+s)
  rw [hsa] at hl
  rw [hbs,hd.symm b m] at hh
  have hprod : 3*(b-a) < δ*s := by simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hbad
  apply hc m t ht
  rw [hxl,hxr]
  refine ⟨?_,?_,?_⟩
  · dsimp [t]; nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hab)]
  · dsimp [t]; nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hab)]
  · dsimp [t]; nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hab)]
lemma exterior_ray_crossloss {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hr : ExteriorUnitRays d a b) (hc : NoFastCancellation d δ)
    (x y : ℝ) (hxy : x ≤ y) :
    0 ≤ (y-x)-d x y ∧ (y-x)-d x y ≤ (2+6/δ)*(b-a) := by
  have hL : 0 ≤ b-a := sub_nonneg.mpr hab
  have hC : 2*(b-a) ≤ (2+6/δ)*(b-a) := by
    have hz : 0 ≤ 6/δ := by positivity
    nlinarith
  have hunit : d x y ≤ y-x := by simpa only [abs_of_nonneg (sub_nonneg.mpr hxy)] using hd.unit x y
  refine ⟨by linarith,?_⟩
  by_cases hya : y ≤ a
  · rw [hr.1 x y (hxy.trans hya) hya,abs_of_nonneg (sub_nonneg.mpr hxy)]
    nlinarith
  by_cases hbx : b ≤ x
  · rw [hr.2 x y hbx (hbx.trans hxy),abs_of_nonneg (sub_nonneg.mpr hxy)]
    nlinarith
  have hay : a ≤ y := le_of_lt (lt_of_not_ge hya)
  have hxb : x ≤ b := le_of_lt (lt_of_not_ge hbx)
  by_cases hxa : x ≤ a
  · by_cases hby : b ≤ y
    · have hh := crossing_excess_bound hd hab (sub_nonneg.mpr hxa) (sub_nonneg.mpr hby) hδ hr hc
      rw [show a-(a-x)=x by ring,show b+(y-b)=y by ring] at hh
      have hD : d a b ≤ b-a := by simpa only [abs_of_nonneg hL] using hd.unit a b
      have he : 6*(b-a)/δ=(6/δ)*(b-a) := by ring
      have he3 : 2*(3*(b-a)/δ)=6*(b-a)/δ := by ring
      nlinarith
    · have hyb : y ≤ b := le_of_lt (lt_of_not_ge hby)
      have hxaD : d x a=a-x := by rw [hr.1 x a hxa (le_refl _),abs_of_nonneg (sub_nonneg.mpr hxa)]
      have hyaD : d y a ≤ y-a := by
        have hh := hd.unit y a
        rw [abs_of_nonpos (by linarith)] at hh
        linarith
      have hh := hd.triangle x y a
      rw [hxaD] at hh
      linarith
  · have hax : a ≤ x := le_of_lt (lt_of_not_ge hxa)
    by_cases hby : b ≤ y
    · have hbyD : d b y=y-b := by rw [hr.2 b y (le_refl _) hby,abs_of_nonneg (sub_nonneg.mpr hby)]
      have hbxD : d b x ≤ b-x := by
        have hh := hd.unit b x
        rw [abs_of_nonpos (by linarith)] at hh
        linarith
      have hh := hd.triangle b x y
      rw [hbyD] at hh
      linarith
    · have hyb : y ≤ b := le_of_lt (lt_of_not_ge hby)
      linarith [hd.nonneg x y]
lemma exterior_rays_nondegenerate {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hr : ExteriorUnitRays d a b) (hc : NoFastCancellation d δ)
    (hne : ¬ ∀ x y : ℝ, d x y=|y-x|) : a < b := by
  by_contra h
  have he : b=a := by linarith
  apply hne
  intro x y
  by_cases hxy : x ≤ y
  · have hh := exterior_ray_crossloss hd hab hδ hr hc x y hxy
    rw [he,sub_self,mul_zero,abs_of_nonneg (sub_nonneg.mpr hxy)] at *
    linarith [hh.1,hh.2]
  · have hyx : y ≤ x := le_of_lt (lt_of_not_ge hxy)
    have hh := exterior_ray_crossloss hd hab hδ hr hc y x hyx
    rw [he,sub_self,mul_zero] at hh
    rw [hd.symm x y,abs_of_nonpos (by linarith)]
    linarith [hh.1,hh.2]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TreeAffine
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
-- module Solutions.OAIQ2_Std.StandardMap_TreeLocalAffine
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
lemma locallyAffine_speed_unique {d : ℝ → ℝ → ℝ} {x w v : ℝ}
    (hw : LocallyAffineAt d x w) (hv : LocallyAffineAt d x v) : w=v := by
  obtain ⟨r,hr,hw⟩ := hw
  obtain ⟨s,hs,hv⟩ := hv
  let a := min r s/2
  have ha : 0 < a := by dsimp [a]; positivity
  have har : a < r := by dsimp [a]; linarith [min_le_left r s]
  have has : a < s := by dsimp [a]; linarith [min_le_right r s]
  have hd1 := hw x (mem_ball_self hr) (x+a) (by rw [mem_ball,Real.dist_eq,add_sub_cancel_left,abs_of_pos ha]; exact har)
  have hd2 := hv x (mem_ball_self hs) (x+a) (by rw [mem_ball,Real.dist_eq,add_sub_cancel_left,abs_of_pos ha]; exact has)
  rw [add_sub_cancel_left,abs_of_pos ha] at hd1 hd2
  nlinarith
lemma locallyAffine_on_ball {d : ℝ → ℝ → ℝ} {x w r : ℝ} (h : ∀ u∈ball x r,∀ v∈ball x r,d u v=w*|v-u|)
    {y : ℝ} (hy : y∈ball x r) : LocallyAffineAt d y w := by
  obtain ⟨s,hs,hsr⟩ := Metric.isOpen_iff.mp isOpen_ball y hy
  exact ⟨s,hs,fun u hu v hv => h u (hsr hu) v (hsr hv)⟩
lemma locallyAffine_speed_bounds {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {x w : ℝ}
    (hw : LocallyAffineAt d x w) : 0 ≤ w ∧ w ≤ 1 := by
  obtain ⟨r,hr,hw⟩ := hw
  have he := hw x (mem_ball_self hr) (x+r/2) (by rw [mem_ball,Real.dist_eq,add_sub_cancel_left,abs_of_pos (by positivity)]; linarith)
  rw [add_sub_cancel_left,abs_of_pos (by positivity)] at he
  have h0 := hd.nonneg x (x+r/2)
  have h1 := hd.unit x (x+r/2)
  rw [add_sub_cancel_left,abs_of_pos (by positivity),he] at h1
  rw [he] at h0
  constructor  <;> nlinarith
lemma connected_local_speed {d : ℝ → ℝ → ℝ} (U : Set ℝ) (hU : IsPreconnected U) (x : U)
    (hl : ∀ y : U, ∃ w : ℝ, LocallyAffineAt d y.val w) :
    ∃ w : ℝ, ∀ y : U, LocallyAffineAt d y.val w := by
  choose w hw using hl
  have hc : IsLocallyConstant w := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro y
    obtain ⟨r,hr,hh⟩ := hw y
    have hn : {z : U | z.val∈ball y.val r}∈𝓝 y :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr)
    filter_upwards [hn] with z hz
    exact locallyAffine_speed_unique (hw z) (locallyAffine_on_ball hh hz)
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU
  exact ⟨w x,fun y => (hc.apply_eq_of_preconnectedSpace y x) ▸ hw y⟩
lemma tree_affine_of_fixed_local_speed {d : ℝ → ℝ → ℝ} (hd : TreeLine d) (a b w : ℝ)
    (hab : a < b) (hw : 0 ≤ w) (hl : ∀ x∈Icc a b,LocallyAffineAt d x w) : d a b=w*(b-a) := by
  choose r hr hloc using (fun x : Icc a b => hl x x.property)
  let c : Icc a b → Set ℝ := fun x => ball x.val (r x)
  obtain ⟨δ,hδ,hcover⟩ := lebesgue_number_lemma_of_metric (s := Icc a b) (c := c) isCompact_Icc
    (fun x => isOpen_ball) (by intro x hx; exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (hr ⟨x,hx⟩)⟩)
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (2*(b-a)/δ))
  have hNR : (0:ℝ) < N := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hN)
  have hN0 : 0 < N := by exact_mod_cast hNR
  let step : ℝ := (b-a)/(N:ℝ)
  let x : ℕ → ℝ := fun i => a+(i:ℝ)*step
  have hstep : 0 < step := div_pos (sub_pos.mpr hab) hNR
  have hstepδ : 2*step < δ := by
    have hn' : 2*(b-a)/δ < (N:ℝ) := (le_max_right _ _).trans_lt hN
    have hmul := (div_lt_iff₀ hδ).mp hn'
    dsimp [step]
    apply (mul_div_assoc 2 (b-a) (N:ℝ)).symm ▸ ((div_lt_iff₀ hNR).mpr _)
    nlinarith
  have hxt : x N=b := by dsimp [x,step]; field_simp; ring
  have hx0 : x 0=a := by simp [x]
  have hdiff (i j : ℕ) : x (i+j)-x i=(j:ℝ)*step := by dsimp [x]; push_cast; ring
  have hxmem (i : ℕ) (hi : i ≤ N) : x i∈Icc a b := by
    have hiR : (i:ℝ) ≤ N := by exact_mod_cast hi
    have hmul := mul_le_mul_of_nonneg_right hiR hstep.le
    constructor
    · dsimp [x]; nlinarith [mul_nonneg (Nat.cast_nonneg i : (0:ℝ) ≤ i) hstep.le]
    · change a+(i:ℝ)*step ≤ b
      change a+(N:ℝ)*step=b at hxt
      linarith
  have hball (i j : ℕ) (hj : j ≤ 2) : x (i+j)∈ball (x i) δ := by
    rw [mem_ball,Real.dist_eq,hdiff,abs_of_nonneg (by positivity)]
    have hjR : (j:ℝ) ≤ 2 := by exact_mod_cast hj
    nlinarith
  have hedge (i : ℕ) (hi : i < N) : d (x i) (x (i+1))=w*(x (i+1)-x i) := by
    obtain ⟨z,hz⟩ := hcover (x i) (hxmem i hi.le)
    have hh := hloc z (x i) (hz (mem_ball_self hδ)) (x (i+1)) (hz (hball i 1 (by omega)))
    rw [abs_of_pos (by rw [hdiff]; simpa only [Nat.cast_one,one_mul] using hstep)] at hh
    exact hh
  have htriple (i : ℕ) (hi : i+1 < N) : d (x i) (x (i+2))=w*(x (i+2)-x i) := by
    obtain ⟨z,hz⟩ := hcover (x i) (hxmem i (by omega))
    have hh := hloc z (x i) (hz (mem_ball_self hδ)) (x (i+2)) (hz (hball i 2 le_rfl))
    rw [abs_of_pos (by rw [hdiff]; positivity)] at hh
    exact hh
  have hh := tree_chain_affine hd x N w hw (fun i hi => by have he := hdiff i 1; push_cast at he; linarith) hedge htriple
  simpa only [hx0,hxt] using hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ShapeTopology
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
lemma isOpen_locallyAffineSet (d : ℝ → ℝ → ℝ) : IsOpen (locallyAffineSet d) := by
  rw [Metric.isOpen_iff]
  rintro x ⟨w,r,hr,hh⟩
  exact ⟨r,hr,fun y hy => ⟨w,locallyAffine_on_ball hh hy⟩⟩
lemma isOpen_locallyUnitSet (d : ℝ → ℝ → ℝ) : IsOpen (locallyUnitSet d) := by
  rw [Metric.isOpen_iff]
  rintro x ⟨r,hr,hh⟩
  exact ⟨r,hr,fun y hy => locallyAffine_on_ball hh hy⟩
lemma affineOn_closure {d : ℝ → ℝ → ℝ} (hc : Continuous (Function.uncurry d))
    (U : Set ℝ) (w : ℝ) (ha : ∀x∈U,∀y∈U,d x y=w*|y-x|) :
    ∀x∈closure U,∀y∈closure U,d x y=w*|y-x| := by
  have h1 (x : ℝ) (hx : x∈U) : ∀y∈closure U,d x y=w*|y-x| := by
    apply closure_minimal (ha x hx)
    exact isClosed_eq (hc.comp (continuous_const.prodMk continuous_id))
      (continuous_const.mul ((continuous_id.sub continuous_const).abs))
  intro x hx y hy
  apply closure_minimal (fun z hz => h1 z hz y hy) _ hx
  exact isClosed_eq (hc.comp (continuous_id.prodMk continuous_const))
    (continuous_const.mul ((continuous_const.sub continuous_id).abs))
lemma closure_component_inter_open {F : Set ℝ} (hF : IsOpen F) {x z : ℝ} (hx : x∈F)
    (hz : z∈closure (connectedComponentIn F x)) (hzF : z∈F) : z∈connectedComponentIn F x := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hF z hzF
  obtain ⟨y,hy,hyz⟩ := Metric.mem_closure_iff.mp hz r hr
  have hyb : y∈ball z r := by simpa only [mem_ball,dist_comm] using hyz
  have hp : IsPreconnected (connectedComponentIn F x ∪ ball z r) :=
    IsPreconnected.union y hy hyb isPreconnected_connectedComponentIn (convex_ball z r).isPreconnected
  exact hp.subset_connectedComponentIn (Or.inl (mem_connectedComponentIn hx))
    (union_subset (connectedComponentIn_subset F x) hball) (Or.inr (mem_ball_self hr))
lemma frontier_component_not_mem {F : Set ℝ} (hF : IsOpen F) {x z : ℝ} (hx : x∈F)
    (hz : z∈frontier (connectedComponentIn F x)) : z∉F := by
  intro hzF
  have hm := closure_component_inter_open hF hx hz.1 hzF
  exact hz.2 (by simpa only [hF.connectedComponentIn.interior_eq] using hm)
lemma open_nonempty_inf_frontier {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hb : BddBelow U) : sInf U∈frontier U := by
  refine ⟨csInf_mem_closure hne hb,?_⟩
  rw [hU.interior_eq]
  intro hh
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU (sInf U) hh
  have hy : sInf U-r/2∈U := hball (by rw [mem_ball,Real.dist_eq]; rw [show sInf U-r/2-sInf U= -r/2 by ring,abs_div,abs_neg,abs_of_pos hr]; norm_num; linarith)
  have hi := csInf_le hb hy
  linarith
lemma open_nonempty_sup_frontier {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hb : BddAbove U) : sSup U∈frontier U := by
  refine ⟨csSup_mem_closure hne hb,?_⟩
  rw [hU.interior_eq]
  intro hh
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU (sSup U) hh
  have hy : sSup U+r/2∈U := hball (by rw [mem_ball,Real.dist_eq,add_sub_cancel_left,abs_of_pos (by positivity)]; linarith)
  have hi := le_csSup hb hy
  linarith
lemma open_inf_lt_mem {U : Set ℝ} (hU : IsOpen U) (hb : BddBelow U) {x : ℝ} (hx : x∈U) : sInf U< x := by
  have hh := csInf_le hb hx
  apply lt_of_le_of_ne hh
  intro he
  have hf := open_nonempty_inf_frontier hU ⟨x,hx⟩ hb
  exact hf.2 (by simpa only [hU.interior_eq,he] using hx)
lemma open_mem_lt_sup {U : Set ℝ} (hU : IsOpen U) (hb : BddAbove U) {x : ℝ} (hx : x∈U) : x< sSup U := by
  have hh := le_csSup hb hx
  apply lt_of_le_of_ne hh
  intro he
  have hf := open_nonempty_sup_frontier hU ⟨x,hx⟩ hb
  exact hf.2 (by simpa only [hU.interior_eq,←he] using hx)
lemma ordConnected_eq_univ_of_unbounded {U : Set ℝ} (hU : OrdConnected U)
    (hlo : ¬BddBelow U) (hhi : ¬BddAbove U) : U=univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨y,hy,hyx⟩ := not_bddBelow_iff.mp hlo x
  obtain ⟨z,hz,hxz⟩ := not_bddAbove_iff.mp hhi x
  exact hU.out hy hz ⟨hyx.le,hxz.le⟩
lemma open_ordConnected_eq_Ioi {U : Set ℝ} (hU : IsOpen U) (hC : OrdConnected U)
    (hne : U.Nonempty) (hlo : BddBelow U) (hhi : ¬BddAbove U) : U=Ioi (sInf U) := by
  ext x; constructor
  · exact open_inf_lt_mem hU hlo
  · intro hx
    obtain ⟨y,hy,hyx⟩ := (csInf_lt_iff hlo hne).mp hx
    obtain ⟨z,hz,hxz⟩ := not_bddAbove_iff.mp hhi x
    exact hC.out hy hz ⟨hyx.le,hxz.le⟩
lemma open_ordConnected_eq_Iio {U : Set ℝ} (hU : IsOpen U) (hC : OrdConnected U)
    (hne : U.Nonempty) (hlo : ¬BddBelow U) (hhi : BddAbove U) : U=Iio (sSup U) := by
  ext x; constructor
  · exact open_mem_lt_sup hU hhi
  · intro hx
    obtain ⟨y,hy,hyx⟩ := not_bddBelow_iff.mp hlo x
    obtain ⟨z,hz,hxz⟩ := (lt_csSup_iff hhi hne).mp hx
    exact hC.out hy hz ⟨hyx.le,hxz.le⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TestObservations
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
-- module Solutions.OAIQ2_Std.StandardMap_ClippedTests
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
-- module Solutions.OAIQ2_Std.StandardMap_VagueBounds
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
-- module Solutions.OAIQ2_Std.StandardMap_EndpointObservations
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
-- module Solutions.OAIQ2_Std.StandardMap_LocalMidpointGrid
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
-- module Solutions.OAIQ2_Std.StandardMap_LocalMidpointAffine
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
-- module Solutions.OAIQ2_Std.StandardMap_LocalTestDetection
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
-- module Solutions.OAIQ2_Std.StandardMap_RealBridge
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
    change (999/1000:ℝ)*((v:ℝ)-(u:ℝ))<realArray d (u:ℝ) (v:ℝ) at hh
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
lemma slowPair_aeterminal : ∀ᵐd ∂K.terminal,SlowPair (realArray d.val) (999/1000) := by
  filter_upwards [S.unit_aeterminal K,S.tree_aeterminal K,S.dyadicBridge_aeselected K false] with d hu ht hb
  exact dyadicBridge_real_slowPair d.val hu ht hb
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ShapeComponents
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
lemma nonaffine_realArray (d : NonAffineArray) (hu : UnitArray d.val) : NonaffineLine (realArray d.val) := by
  rintro ⟨w,hw⟩
  have hb : w∈Icc (0:ℝ) 1 := by
    have h0 := realArray_nonneg d.val hu 0 1
    have h1 := realArray_le d.val hu 0 1
    rw [hw] at h0 h1
    norm_num at h0 h1
    exact ⟨h0,h1⟩
  apply d.property
  refine ⟨⟨w,hb⟩,?_⟩
  apply Subtype.ext
  funext s t
  change w*|(t:ℝ)-(s:ℝ)|=d.val.val s t
  simpa only [realArray_coe d.val hu] using (hw s t).symm
lemma connected_affine_full {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (U : Set ℝ) (hU : IsPreconnected U) (x : U)
    (hl : ∀y∈U,∃w,LocallyAffineAt d y w) :
    ∃w:ℝ,0≤ w ∧ w≤1 ∧ (∀y∈U,LocallyAffineAt d y w) ∧ (∀a∈U,∀b∈U,d a b=w*|b-a|) := by
  obtain ⟨w,hw⟩ := connected_local_speed U hU x (fun y => hl y y.property)
  have hb := locallyAffine_speed_bounds hd (hw x)
  refine ⟨w,hb.1,hb.2,fun y hy => hw ⟨y,hy⟩,?_⟩
  intro a ha b hb'
  rcases lt_trichotomy a b with hab|rfl|hab
  · rw [abs_of_pos (sub_pos.mpr hab)]
    exact tree_affine_of_fixed_local_speed hd a b w hab hb.1
      (fun y hy => hw ⟨y,hU.ordConnected.out ha hb' hy⟩)
  · simp only [hd.self,sub_self,abs_zero,mul_zero]
  · rw [hd.symm,abs_sub_comm,abs_of_pos (sub_pos.mpr hab)]
    exact tree_affine_of_fixed_local_speed hd b a w hab hb.1
      (fun y hy => hw ⟨y,hU.ordConnected.out hb' ha hy⟩)
lemma affine_component_data {d : ℝ → ℝ → ℝ} (hd : TreeLine d) (hn : NonaffineLine d)
    {x : ℝ} (hx : x∈locallyAffineSet d) :
    ∃w:ℝ,0≤ w ∧ w≤1 ∧
      (∀y∈connectedComponentIn (locallyAffineSet d) x,LocallyAffineAt d y w) ∧
      (∀a∈connectedComponentIn (locallyAffineSet d) x,∀b∈connectedComponentIn (locallyAffineSet d) x,d a b=w*|b-a|) ∧
      connectedComponentIn (locallyAffineSet d) x≠univ := by
  obtain ⟨w,hw0,hw1,hl,ha⟩ := connected_affine_full hd _ isPreconnected_connectedComponentIn
    ⟨x,mem_connectedComponentIn hx⟩ (fun y hy => connectedComponentIn_subset (locallyAffineSet d) x hy)
  refine ⟨w,hw0,hw1,hl,ha,?_⟩
  intro he
  exact hn ⟨w,fun a b => ha a (by rw [he]; trivial) b (by rw [he]; trivial)⟩
lemma fast_component_speed_one {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c x w : ℝ}
    (hp : SlowPair d c) (hw : LocallyAffineAt d x w) (hfast : c< w) : w=1 := by
  have hx : x∈locallyAffineSet d := ⟨w,hw⟩
  let U := connectedComponentIn (locallyAffineSet d) x
  have ho : IsOpen U := (isOpen_locallyAffineSet d).connectedComponentIn
  have hxm : x∈U := mem_connectedComponentIn hx
  obtain ⟨v,hv0,hv1,hl,ha,hne⟩ := affine_component_data hd hn hx
  have hvw : v=w := locallyAffine_speed_unique (hl x hxm) hw
  subst v
  have hcl := affineOn_closure hc U w ha
  obtain ⟨z,hz⟩ := nonempty_frontier_iff.mpr ⟨⟨x,hxm⟩,hne⟩
  have hzp : ¬∃v,LocallyAffineAt d z v := frontier_component_not_mem (isOpen_locallyAffineSet d) hx hz
  have hzx : z≠x := by
    intro he; subst z
    apply hz.2
    rwa [ho.interior_eq]
  by_contra hn1
  have hxq : ¬LocallyAffineAt d x 1 := fun h => hn1 (locallyAffine_speed_unique hw h)
  have hh := hp z x hzp hxq
  rw [hcl z hz.1 x (subset_closure hxm)] at hh
  have habs : 0 < |x-z| := abs_pos.mpr (sub_ne_zero.mpr hzx.symm)
  nlinarith
lemma fast_local_ray {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c x w : ℝ}
    (hp : SlowPair d c) (hc1 : c<1) (hw : LocallyAffineAt d x w) (hfast : c< w) :
    (∃a:ℝ,x< a ∧ (¬∃v,LocallyAffineAt d a v) ∧ ∀s≤ a,∀t≤ a,d s t=|t-s|) ∨
    (∃a:ℝ,a< x ∧ (¬∃v,LocallyAffineAt d a v) ∧ ∀s≥a,∀t≥a,d s t=|t-s|) := by
  have hx : x∈locallyAffineSet d := ⟨w,hw⟩
  have hw1 := fast_component_speed_one hd hc hn hp hw hfast
  let U := connectedComponentIn (locallyAffineSet d) x
  have ho : IsOpen U := (isOpen_locallyAffineSet d).connectedComponentIn
  have hxm : x∈U := mem_connectedComponentIn hx
  have hU : IsPreconnected U := isPreconnected_connectedComponentIn
  obtain ⟨v,hv0,hv1,hl,ha,hne⟩ := affine_component_data hd hn hx
  have hvw : v=w := locallyAffine_speed_unique (hl x hxm) hw
  have hvone : v=1 := hvw.trans hw1
  rw [hvone] at ha
  have hcl := affineOn_closure hc U 1 ha
  have hfront (a b : ℝ) (ha : a∈frontier U) (hb : b∈frontier U) : a=b := by
    have hpa : ¬∃v,LocallyAffineAt d a v := frontier_component_not_mem (isOpen_locallyAffineSet d) hx ha
    have hpb : ¬∃v,LocallyAffineAt d b v := frontier_component_not_mem (isOpen_locallyAffineSet d) hx hb
    have hh := hp a b hpa (fun h => hpb ⟨1,h⟩)
    rw [hcl a ha.1 b hb.1,one_mul] at hh
    have he : |b-a|=0 := by nlinarith [abs_nonneg (b-a)]
    exact (sub_eq_zero.mp (abs_eq_zero.mp he)).symm
  by_cases hlo : BddBelow U
  · have hinf := open_nonempty_inf_frontier ho ⟨x,hxm⟩ hlo
    have hhi : ¬BddAbove U := by
      intro hhi
      have he := hfront _ _ hinf (open_nonempty_sup_frontier ho ⟨x,hxm⟩ hhi)
      have h1 := open_inf_lt_mem ho hlo hxm
      have h2 := open_mem_lt_sup ho hhi hxm
      linarith
    have he := open_ordConnected_eq_Ioi ho hU.ordConnected ⟨x,hxm⟩ hlo hhi
    refine Or.inr ⟨sInf U,open_inf_lt_mem ho hlo hxm,frontier_component_not_mem (isOpen_locallyAffineSet d) hx hinf,?_⟩
    intro s hs t ht
    have hclosure : closure U=Ici (sInf U) := (congrArg closure he).trans (closure_Ioi _)
    simpa only [one_mul] using hcl s (by rw [hclosure]; exact hs) t (by rw [hclosure]; exact ht)
  · have hhi : BddAbove U := by
      by_contra hh
      exact hne (ordConnected_eq_univ_of_unbounded hU.ordConnected hlo hh)
    have hsup := open_nonempty_sup_frontier ho ⟨x,hxm⟩ hhi
    have he := open_ordConnected_eq_Iio ho hU.ordConnected ⟨x,hxm⟩ hlo hhi
    refine Or.inl ⟨sSup U,open_mem_lt_sup ho hhi hxm,frontier_component_not_mem (isOpen_locallyAffineSet d) hx hsup,?_⟩
    intro s hs t ht
    have hclosure : closure U=Iic (sSup U) := (congrArg closure he).trans (closure_Iio _)
    simpa only [one_mul] using hcl s (by rw [hclosure]; exact hs) t (by rw [hclosure]; exact ht)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ShapeCore
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
lemma isClosed_slowCore (d : ℝ → ℝ → ℝ) : IsClosed (slowCore d) := (isOpen_locallyUnitSet d).isClosed_compl
lemma unit_Iic_local {d : ℝ → ℝ → ℝ} {a x : ℝ} (h : ∀s≤ a,∀t≤ a,d s t=|t-s|) (hx : x< a) :
    LocallyAffineAt d x 1 := by
  refine ⟨(a-x)/2,by linarith,?_⟩
  intro s hs t ht
  rw [mem_ball,Real.dist_eq,abs_lt] at hs ht
  simpa only [one_mul] using h s (by linarith [hs.2]) t (by linarith [ht.2])
lemma unit_Ici_local {d : ℝ → ℝ → ℝ} {a x : ℝ} (h : ∀s≥a,∀t≥a,d s t=|t-s|) (hx : a< x) :
    LocallyAffineAt d x 1 := by
  refine ⟨(x-a)/2,by linarith,?_⟩
  intro s hs t ht
  rw [mem_ball,Real.dist_eq,abs_lt] at hs ht
  simpa only [one_mul] using h s (by linarith [hs.1]) t (by linarith [ht.1])
lemma nonaffine_has_nonlocal {d : ℝ → ℝ → ℝ} (hd : TreeLine d) (hn : NonaffineLine d) :
    ∃x:ℝ,¬∃w,LocallyAffineAt d x w := by
  by_contra h
  push Not at h
  have hh : ∀x∈(univ:Set ℝ),∃w,LocallyAffineAt d x w := fun x _ => h x
  obtain ⟨w,_,_,_,ha⟩ := connected_affine_full hd univ isPreconnected_univ ⟨0,mem_univ _⟩ hh
  exact hn ⟨w,fun x y => ha x (mem_univ _) y (mem_univ _)⟩
lemma slowCore_nonempty {d : ℝ → ℝ → ℝ} (hd : TreeLine d) (hn : NonaffineLine d) : (slowCore d).Nonempty := by
  obtain ⟨x,hx⟩ := nonaffine_has_nonlocal hd hn
  exact ⟨x,fun h => hx ⟨1,h⟩⟩
lemma slowCore_ordConnected {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c : ℝ}
    (hp : SlowPair d c) (hc1 : c<1) : OrdConnected (slowCore d) := by
  constructor
  intro x hx y hy z hz
  by_contra hz'
  have hzu : LocallyAffineAt d z 1 := not_not.mp hz'
  rcases fast_local_ray hd hc hn hp hc1 hzu hc1 with ⟨a,hza,_,ha⟩|⟨a,haz,_,ha⟩
  · exact hx (unit_Iic_local ha (lt_of_le_of_lt hz.1 hza))
  · exact hy (unit_Ici_local ha (lt_of_lt_of_le haz hz.2))
lemma slowCore_local_speed {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c x w : ℝ}
    (hp : SlowPair d c) (hx : x∈slowCore d) (hw : LocallyAffineAt d x w) : w≤ c := by
  by_contra hh
  have he := fast_component_speed_one hd hc hn hp hw (lt_of_not_ge hh)
  rw [he] at hw
  exact hx hw
lemma slow_affine_prefix {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c a b : ℝ}
    (hp : SlowPair d c) (hab : a< b) (ha : a∈slowCore d)
    (hlocal : ∀x∈Ico a b,∃w,LocallyAffineAt d x w) : d a b≤ c*(b-a) := by
  obtain ⟨w,_,_,hl,he⟩ := connected_affine_full hd (Ico a b) isPreconnected_Ico ⟨a,⟨le_rfl,hab⟩⟩ hlocal
  have hw := slowCore_local_speed hd hc hn hp ha (hl a ⟨le_rfl,hab⟩)
  have hcl := affineOn_closure hc (Ico a b) w he
  rw [closure_Ico hab.ne] at hcl
  have heq := hcl a ⟨le_rfl,hab.le⟩ b ⟨hab.le,le_rfl⟩
  rw [abs_of_pos (sub_pos.mpr hab)] at heq
  rw [heq]
  exact mul_le_mul_of_nonneg_right hw (sub_nonneg.mpr hab.le)
lemma slow_affine_suffix {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c a b : ℝ}
    (hp : SlowPair d c) (hab : a< b) (hb : b∈slowCore d)
    (hlocal : ∀x∈Ioc a b,∃w,LocallyAffineAt d x w) : d a b≤ c*(b-a) := by
  obtain ⟨w,_,_,hl,he⟩ := connected_affine_full hd (Ioc a b) isPreconnected_Ioc ⟨b,⟨hab,le_rfl⟩⟩ hlocal
  have hw := slowCore_local_speed hd hc hn hp hb (hl b ⟨hab,le_rfl⟩)
  have hcl := affineOn_closure hc (Ioc a b) w he
  rw [closure_Ioc hab.ne] at hcl
  have heq := hcl a ⟨le_rfl,hab.le⟩ b ⟨hab.le,le_rfl⟩
  rw [abs_of_pos (sub_pos.mpr hab)] at heq
  rw [heq]
  exact mul_le_mul_of_nonneg_right hw (sub_nonneg.mpr hab.le)
lemma slowCore_secant_sorted {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c x y : ℝ}
    (hp : SlowPair d c) (hxy : x< y) (hx : x∈slowCore d) (hy : y∈slowCore d) :
    d x y≤ c*(y-x) := by
  let C : Set ℝ := Icc x y ∩ (locallyAffineSet d)ᶜ
  have hC : IsCompact C := isCompact_Icc.inter_right (isOpen_locallyAffineSet d).isClosed_compl
  by_cases hne : C.Nonempty
  · let p := sInf C
    let q := sSup C
    have hpC : p∈C := hC.sInf_mem hne
    have hqC : q∈C := hC.sSup_mem hne
    have hxp : x≤ p := hpC.1.1
    have hqy : q≤ y := hqC.1.2
    have hpq : p≤ q := csInf_le hC.bddBelow hqC
    have hleft : d x p≤ c*(p-x) := by
      rcases lt_or_eq_of_le hxp with h|h
      · apply slow_affine_prefix hd hc hn hp h hx
        intro z hz
        by_contra hz'
        have hzC : z∈C := ⟨⟨hz.1,hz.2.le.trans hpC.1.2⟩,hz'⟩
        have hmin := csInf_le hC.bddBelow hzC
        change p≤ z at hmin
        linarith [hz.2]
      · rw [←h]; simp only [hd.self,sub_self,mul_zero,le_refl]
    have hright : d q y≤ c*(y-q) := by
      rcases lt_or_eq_of_le hqy with h|h
      · apply slow_affine_suffix hd hc hn hp h hy
        intro z hz
        by_contra hz'
        have hzC : z∈C := ⟨⟨hqC.1.1.trans hz.1.le,hz.2⟩,hz'⟩
        have hmax := le_csSup hC.bddAbove hzC
        change z≤ q at hmax
        linarith [hz.1]
      · rw [h]; simp only [hd.self,sub_self,mul_zero,le_refl]
    have hmid := hp p q hpC.2 (fun h => hqC.2 ⟨1,h⟩)
    rw [abs_of_nonneg (sub_nonneg.mpr hpq)] at hmid
    have h1 := hd.triangle x p y
    have h2 := hd.triangle p q y
    nlinarith
  · have hlocal : ∀z∈Icc x y,∃w,LocallyAffineAt d z w := by
      intro z hz
      by_contra hh
      exact hne ⟨z,hz,hh⟩
    obtain ⟨w,_,_,hl,he⟩ := connected_affine_full hd (Icc x y) isPreconnected_Icc ⟨x,⟨le_rfl,hxy.le⟩⟩ hlocal
    have hw := slowCore_local_speed hd hc hn hp hx (hl x ⟨le_rfl,hxy.le⟩)
    rw [he x ⟨le_rfl,hxy.le⟩ y ⟨hxy.le,le_rfl⟩,abs_of_pos (sub_pos.mpr hxy)]
    exact mul_le_mul_of_nonneg_right hw (sub_nonneg.mpr hxy.le)
lemma slowCore_secant {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c x y : ℝ}
    (hp : SlowPair d c) (hx : x∈slowCore d) (hy : y∈slowCore d) : d x y≤ c*|y-x| := by
  rcases lt_trichotomy x y with h|rfl|h
  · rw [abs_of_pos (sub_pos.mpr h)]; exact slowCore_secant_sorted hd hc hn hp h hx hy
  · simp only [hd.self,sub_self,abs_zero,mul_zero,le_refl]
  · rw [hd.symm,abs_sub_comm,abs_of_pos (sub_pos.mpr h)]; exact slowCore_secant_sorted hd hc hn hp h hy hx
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ShapeClassification
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
lemma localUnit_affineOn {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {U : Set ℝ}
    (hU : IsPreconnected U) (hl : ∀x∈U,LocallyAffineAt d x 1) :
    ∀a∈U,∀b∈U,d a b=|b-a| := by
  intro a ha b hb
  rcases lt_trichotomy a b with hab|rfl|hab
  · rw [abs_of_pos (sub_pos.mpr hab)]
    simpa only [one_mul] using tree_affine_of_fixed_local_speed hd a b 1 hab (by norm_num)
      (fun y hy => hl y (hU.ordConnected.out ha hb hy))
  · simp only [hd.self,sub_self,abs_zero]
  · rw [hd.symm,abs_sub_comm,abs_of_pos (sub_pos.mpr hab)]
    simpa only [one_mul] using tree_affine_of_fixed_local_speed hd b a 1 hab (by norm_num)
      (fun y hy => hl y (hU.ordConnected.out hb ha hy))
lemma slowCore_left_unit {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hb : BddBelow (slowCore d)) :
    ∀x≤ sInf (slowCore d),∀y≤ sInf (slowCore d),d x y=|y-x| := by
  have hl : ∀x∈Iio (sInf (slowCore d)),LocallyAffineAt d x 1 := by
    intro x hx
    by_contra hh
    have hh' : x∈slowCore d := hh
    exact (not_le_of_gt hx) (csInf_le hb hh')
  have ha := localUnit_affineOn hd isPreconnected_Iio hl
  have he := affineOn_closure hc (Iio (sInf (slowCore d))) 1 (by simpa only [one_mul] using ha)
  rw [closure_Iio] at he
  simpa only [one_mul, mem_Iic, mem_Ici] using he
lemma slowCore_right_unit {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hb : BddAbove (slowCore d)) :
    ∀x≥ sSup (slowCore d),∀y≥ sSup (slowCore d),d x y=|y-x| := by
  have hl : ∀x∈Ioi (sSup (slowCore d)),LocallyAffineAt d x 1 := by
    intro x hx
    by_contra hh
    have hh' : x∈slowCore d := hh
    exact (not_le_of_gt hx) (le_csSup hb hh')
  have ha := localUnit_affineOn hd isPreconnected_Ioi hl
  have he := affineOn_closure hc (Ioi (sSup (slowCore d))) 1 (by simpa only [one_mul] using ha)
  rw [closure_Ioi] at he
  simpa only [one_mul, mem_Iic, mem_Ici] using he
lemma closed_ordConnected_bounded {U : Set ℝ} (hc : IsClosed U) (hU : OrdConnected U)
    (hne : U.Nonempty) (hlo : BddBelow U) (hhi : BddAbove U) : U=Icc (sInf U) (sSup U) := by
  have ha := hc.csInf_mem hne hlo
  have hb := hc.csSup_mem hne hhi
  ext x
  exact ⟨fun hx => ⟨csInf_le hlo hx,le_csSup hhi hx⟩,fun hx => hU.out ha hb hx⟩
lemma closed_ordConnected_left_bounded {U : Set ℝ} (hc : IsClosed U) (hU : OrdConnected U)
    (hne : U.Nonempty) (hlo : BddBelow U) (hhi : ¬BddAbove U) : U=Ici (sInf U) := by
  have ha := hc.csInf_mem hne hlo
  ext x; constructor
  · exact csInf_le hlo
  · intro hx
    obtain ⟨y,hy,hxy⟩ := not_bddAbove_iff.mp hhi x
    exact hU.out ha hy ⟨hx,hxy.le⟩
lemma closed_ordConnected_right_bounded {U : Set ℝ} (hc : IsClosed U) (hU : OrdConnected U)
    (hne : U.Nonempty) (hlo : ¬BddBelow U) (hhi : BddAbove U) : U=Iic (sSup U) := by
  have hb := hc.csSup_mem hne hhi
  ext x; constructor
  · exact le_csSup hhi
  · intro hx
    obtain ⟨y,hy,hyx⟩ := not_bddBelow_iff.mp hlo x
    exact hU.out hy hb ⟨hyx.le,hx⟩

lemma slowShape_of_exclusions {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c δ : ℝ}
    (hp : SlowPair d c) (hc1 : c<1) (hδ : 0<δ) (hf : NoFastCancellation d δ) : SlowShape d c := by
  have hne := slowCore_nonempty hd hn
  have hcl := isClosed_slowCore d
  have hU := slowCore_ordConnected hd hc hn hp hc1
  by_cases hlo : BddBelow (slowCore d)
  · have hl := slowCore_left_unit hd hc hlo
    by_cases hhi : BddAbove (slowCore d)
    · have hr := slowCore_right_unit hd hc hhi
      have he := closed_ordConnected_bounded hcl hU hne hlo hhi
      have hab : sInf (slowCore d)≤ sSup (slowCore d) := csInf_le hlo (hcl.csSup_mem hne hhi)
      have hrays : ExteriorUnitRays d (sInf (slowCore d)) (sSup (slowCore d)) :=
        ⟨fun x y hx hy => hl x hx y hy,fun x y hx hy => hr x hx y hy⟩
      have hlt := exterior_rays_nondegenerate hd hab hδ hrays hf (fun h => hn ⟨1,by simpa only [one_mul] using h⟩)
      refine Or.inr (Or.inr (Or.inr ⟨_,_,hlt,hrays,?_⟩))
      intro x hx y hy
      exact slowCore_secant hd hc hn hp (by rwa [he]) (by rwa [he])
    · have he := closed_ordConnected_left_bounded hcl hU hne hlo hhi
      refine Or.inr (Or.inl ⟨_,hl,?_⟩)
      intro x hx y hy
      apply slowCore_secant hd hc hn hp <;> rwa [he]
  · by_cases hhi : BddAbove (slowCore d)
    · have hr := slowCore_right_unit hd hc hhi
      have he := closed_ordConnected_right_bounded hcl hU hne hlo hhi
      refine Or.inr (Or.inr (Or.inl ⟨_,hr,?_⟩))
      intro x hx y hy
      apply slowCore_secant hd hc hn hp <;> rwa [he]
    · have he := ordConnected_eq_univ_of_unbounded hU hlo hhi
      refine Or.inl (fun x y => slowCore_secant hd hc hn hp ?_ ?_) <;> rw [he] <;> trivial
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ShapeLimit
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
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma shape_aeterminal : ∀ᵐd ∂L.terminal,SlowShape (realArray d.val) (999/1000) := by
  filter_upwards [S.unit_aeterminal L,S.tree_aeterminal L,S.slowPair_aeterminal L,S.noCancellation_aeterminal L] with d hu ht hp hf
  exact slowShape_of_exclusions (realArray_treeLine d.val hu ht) (continuous_realArray d.val hu)
    (nonaffine_realArray d hu) hp (by norm_num) (by norm_num) hf
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_RemainderLaws
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
lemma arrayTranslate_unit (r : DyadicTime) (d : DistanceArray) (hu : UnitArray d) : UnitArray (arrayTranslate r d) := by
  intro s t
  change d.val (s+r) (t+r)≤|(t:ℝ)-(s:ℝ)|
  have hh := hu (s+r) (t+r)
  change d.val (s+r) (t+r)≤|((t:ℝ)+(r:ℝ))-((s:ℝ)+(r:ℝ))| at hh
  simpa only [add_sub_add_right_eq_sub] using hh
lemma dyadicHalf_add (s t : DyadicTime) : dyadicHalf (s+t)=dyadicHalf s+dyadicHalf t := by
  apply Subtype.ext; change ((s:ℝ)+(t:ℝ))/2=(s:ℝ)/2+(t:ℝ)/2; ring
lemma half_translate (r : DyadicTime) (d : NonAffineArray) (hu : UnitArray d.val) :
    nonaffineTranslation r (nonaffineHalf d)=nonaffineHalf (nonaffineTranslation (dyadicHalf r) d) := by
  have hu' : UnitArray (nonaffineTranslation (dyadicHalf r) d).val := arrayTranslate_unit _ _ hu
  rw [nonaffineHalf,dite_eq_left hu,nonaffineHalf,dite_eq_left hu']
  apply Subtype.ext; apply Subtype.ext; funext s t
  change 2*d.val.val (dyadicHalf (s+r)) (dyadicHalf (t+r))=
    2*d.val.val (dyadicHalf s+dyadicHalf r) (dyadicHalf t+dyadicHalf r)
  rw [dyadicHalf_add,dyadicHalf_add]
lemma unit_half_map (μ : Measure NonAffineArray) (hu : ∀ᵐd ∂μ,UnitArray d.val) :
    ∀ᵐd ∂μ.map nonaffineHalf,UnitArray d.val := by
  apply (ae_map_iff measurable_nonaffineHalf.aemeasurable
    ((isClosed_unitArray.preimage continuous_subtype_val).measurableSet)).mpr
  exact hu.mono (fun d hd => nonaffineHalf_unit d hd)
lemma half_map_translation_invariant (μ : Measure NonAffineArray) (hu : ∀ᵐd ∂μ,UnitArray d.val)
    (ht : ∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) (r : DyadicTime) :
    (μ.map nonaffineHalf).map (nonaffineTranslation r)=μ.map nonaffineHalf := by
  rw [Measure.map_map (nonaffineTranslation r).continuous.measurable measurable_nonaffineHalf]
  calc
    μ.map (nonaffineTranslation r ∘ nonaffineHalf)=μ.map (nonaffineHalf ∘ nonaffineTranslation (dyadicHalf r)) :=
      Measure.map_congr (hu.mono (fun d hd => half_translate r d hd))
    _=(μ.map (nonaffineTranslation (dyadicHalf r))).map nonaffineHalf := by
      rw [Measure.map_map measurable_nonaffineHalf (nonaffineTranslation _).continuous.measurable]
    _=μ.map nonaffineHalf := by rw [ht]
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma backwardLaw_zero : S.backwardLaw L 0=L.terminal := by simp [backwardLaw]
lemma backwardLaw_succ (n : ℕ) : S.backwardLaw L (n+1)=(S.backwardLaw L n).map nonaffineHalf :=
  (map_iterate_succ L.terminal nonaffineHalf measurable_nonaffineHalf n).symm
lemma backwardLaw_unit (n : ℕ) : ∀ᵐd ∂S.backwardLaw L n,UnitArray d.val := by
  induction n with
  | zero => rw [S.backwardLaw_zero L]; exact S.unit_aeterminal L
  | succ n ih => rw [S.backwardLaw_succ L]; exact unit_half_map _ ih
lemma backwardLaw_translate (n : ℕ) (r : DyadicTime) : (S.backwardLaw L n).map (nonaffineTranslation r)=S.backwardLaw L n := by
  induction n generalizing r with
  | zero => rw [S.backwardLaw_zero L]; exact S.terminal_translate L r
  | succ n ih => rw [S.backwardLaw_succ L]; exact half_map_translation_invariant _ (S.backwardLaw_unit L n) ih r
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TerminalShortfall
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
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma terminal_shortfall_max_integral (i : ℕ) :
    (∫ d,max (arrayShortfall 0 (dyadicInt 1) d) 0 ∂S.terminalLaw i)=1 := by
  rw [terminalLaw,integral_scaleLaw _ _ _ _ _ (S.epsilon_pos i) _
    ((continuous_arrayShortfall 0 (dyadicInt 1)).max continuous_const)]
  simp only [Finset.range_one,Finset.sum_singleton,Nat.add_zero]
  let n := 2^(S.exponent i)
  have hn : 0<n := by dsimp [n]; positivity
  have hs : (n:ℝ)*(0:DyadicTime)=((0:ℤ):ℝ) := by simp
  have ht : (n:ℝ)*(dyadicInt 1:ℝ)=((0:ℤ):ℝ)+(n:ℝ) := by simp
  have he : (∫ d,max (arrayShortfall 0 (dyadicInt 1) d) 0 ∂sampleLaw (S.parameter i) (S.positive i).le n hn)=
      ∫ d,arrayShortfall 0 (dyadicInt 1) d ∂sampleLaw (S.parameter i) (S.positive i).le n hn := by
    rw [integral_sampleLaw _ _ _ _ _ ((continuous_arrayShortfall 0 (dyadicInt 1)).max continuous_const),
      integral_sampleLaw _ _ _ _ _ (continuous_arrayShortfall 0 (dyadicInt 1))]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    dsimp only
    rw [shortfall_sample_aligned _ _ _ n hn 0 (dyadicInt 1) 0 n hn hs ht]
    exact max_eq_left (torusShortfall_mem _ (S.positive i).le z 0 n hn).1
  rw [he,integral_shortfall_sample _ _ n hn 0 (dyadicInt 1) 0 n hn hs ht]
  exact div_self (S.epsilon_pos i).ne'
lemma terminal_shortfall_integrable_bound :
    Integrable (fun d : NonAffineArray => arrayShortfall 0 (dyadicInt 1) d.val) L.terminal ∧
      (∫ d,arrayShortfall 0 (dyadicInt 1) d.val ∂L.terminal) ≤ 1 := by
  let F : DistanceArray → ℝ := fun d => max (arrayShortfall 0 (dyadicInt 1) d) 0
  have hF : Continuous F := (continuous_arrayShortfall 0 (dyadicInt 1)).max continuous_const
  obtain ⟨hi,hb⟩ := vague_integrable_bound L.filter (fun i => nonaffinePart (S.terminalLaw i)) L.terminal L.terminal_converges
    (fun d => F d.val) (hF.comp continuous_subtype_val) (fun d => le_max_right _ _) 1 (by norm_num)
    (fun i => integrable_nonaffinePart _ F hF) (Eventually.of_forall (fun i => by
      exact (integral_nonaffinePart_le _ F hF (fun d => le_max_right _ _)).trans (S.terminal_shortfall_max_integral i).le))
  have he : (fun d : NonAffineArray => F d.val)=ᵐ[L.terminal] (fun d => arrayShortfall 0 (dyadicInt 1) d.val) := by
    filter_upwards [S.unit_aeterminal L] with d hd
    exact max_eq_left (shortfall_unit_mem d.val hd 0 (dyadicInt 1) (by norm_num)).1
  exact ⟨hi.congr he,by rw [←integral_congr_ae he]; exact hb⟩
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_CappedTests
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
-- module Solutions.OAIQ2_Std.StandardMap_FineArrays
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
lemma dyadicFine_zero (n : ℕ) : dyadicFine n 0=0 := by
  apply Subtype.ext
  simp only [dyadicFine_val,ZeroMemClass.coe_zero,zero_div]
lemma halfIterate_unit (n : ℕ) (d : NonAffineArray) (hu : UnitArray d.val) : UnitArray ((nonaffineHalf^[n]) d).val := by
  induction n with
  | zero => exact hu
  | succ n ih => simpa only [Function.iterate_succ_apply'] using nonaffineHalf_unit _ ih
lemma halfIterate_eval (n : ℕ) (d : NonAffineArray) (hu : UnitArray d.val) (s t : DyadicTime) :
    ((nonaffineHalf^[n]) d).val.val s t=(2:ℝ)^n*d.val.val (dyadicFine n s) (dyadicFine n t) := by
  induction n generalizing s t with
  | zero => simp [dyadicFine]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rw [nonaffineHalf,dite_eq_left (halfIterate_unit n d hu)]
    change 2*((nonaffineHalf^[n]) d).val.val (dyadicHalf s) (dyadicHalf t)=_
    rw [ih,pow_succ]
    have he (s:DyadicTime) : dyadicFine n (dyadicHalf s)=dyadicFine (n+1) s := by
      exact (Function.iterate_succ_apply _ _ _).symm
    rw [he,he]
    ring
lemma halfIterate_shortfall (n : ℕ) (d : NonAffineArray) (hu : UnitArray d.val) (s t : DyadicTime) :
    arrayShortfall s t ((nonaffineHalf^[n]) d).val=arrayShortfall (dyadicFine n s) (dyadicFine n t) d.val := by
  unfold arrayShortfall
  rw [halfIterate_eval n d hu,dyadicFine_val,dyadicFine_val,←sub_div]
  congr 1
  rw [div_div_eq_mul_div,mul_comm]
lemma shortfall_half_bound (d : NonAffineArray) (hu : UnitArray d.val) :
    arrayShortfall 0 (dyadicInt 1) (nonaffineHalf d).val≤2*arrayShortfall 0 (dyadicInt 1) d.val := by
  have hj := arrayJ_nonneg 0 (dyadicInt 2) (by norm_num) (nonaffineHalf d).val
  have hz := (shortfall_unit_mem (nonaffineHalf d).val (nonaffineHalf_unit d hu) (dyadicInt 1) (dyadicInt 2) (by norm_num)).1
  have he : arrayShortfall 0 (dyadicInt 2) (nonaffineHalf d).val=arrayShortfall 0 (dyadicInt 1) d.val := by
    rw [nonaffineHalf,dite_eq_left hu]
    dsimp only [arrayShortfall,nonaffineHalfOn,arrayHalf]
    simp only [dyadicInt_val,ZeroMemClass.coe_zero,Int.cast_one,Int.cast_ofNat,sub_zero]
    have h0 : dyadicHalf 0=0 := by apply Subtype.ext; norm_num
    have h1 : dyadicHalf (dyadicInt 2)=dyadicInt 1 := by apply Subtype.ext; norm_num
    rw [h0,h1]; ring
  simp only [arrayJ,dyadicMid_zero_two,he] at hj
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TerminalCap
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
lemma continuous_capF (α : ℝ) : Continuous (capF α) := (entropyCap_contDiff α).continuous.comp (continuous_arrayShortfall _ _)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_FineMoments
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
lemma shortfall_dilate (d:DistanceArray) (s t:DyadicTime) :
    arrayShortfall s t (arrayDilate d)=arrayShortfall (s+s) (t+t) d := by
  unfold arrayShortfall
  change 1-(d.val (s+s) (t+t)/2)/((t:ℝ)-(s:ℝ))=1-d.val (s+s) (t+t)/(((t:ℝ)+(t:ℝ))-((s:ℝ)+(s:ℝ)))
  congr 1
  rw [div_div]
  congr 1
  ring
lemma integral_invariant_translation (μ:Measure NonAffineArray) (r:DyadicTime)
    (ht:μ.map (nonaffineTranslation r)=μ) (f:NonAffineArray→ℝ) (hf:Measurable f) :
    (∫d,f (nonaffineTranslation r d) ∂μ)=∫d,f d ∂μ := by
  rw [←integral_map (nonaffineTranslation r).continuous.measurable.aemeasurable hf.aestronglyMeasurable,ht]
lemma half_shortfall_average (d:NonAffineArray) (hu:UnitArray d.val) :
    (arrayShortfall 0 (dyadicInt 1) (nonaffineHalf d).val+
      arrayShortfall 0 (dyadicInt 1) (nonaffineHalf (nonaffineTranslation (dyadicHalf (dyadicInt 1)) d)).val)/2≤arrayShortfall 0 (dyadicInt 1) d.val := by
  have hj := arrayJ_nonneg 0 (dyadicInt 2) (by norm_num) (nonaffineHalf d).val
  have hs : arrayShortfall 0 (dyadicInt 2) (nonaffineHalf d).val=arrayShortfall 0 (dyadicInt 1) d.val := by
    have he := shortfall_dilate (nonaffineHalf d).val 0 (dyadicInt 1)
    rw [show (0:DyadicTime)+0=0 by simp,show dyadicInt 1+dyadicInt 1=dyadicInt 2 by apply Subtype.ext; norm_num] at he
    rw [show arrayDilate (nonaffineHalf d).val=d.val from congrArg Subtype.val (nonaffineDilate_half d hu)] at he
    exact he.symm
  have ht : arrayShortfall (dyadicInt 1) (dyadicInt 2) (nonaffineHalf d).val=
      arrayShortfall 0 (dyadicInt 1) (nonaffineHalf (nonaffineTranslation (dyadicHalf (dyadicInt 1)) d)).val := by
    rw [←half_translate (dyadicInt 1) d hu]
    change _=arrayShortfall 0 (dyadicInt 1) (arrayTranslate (dyadicInt 1) (nonaffineHalf d).val)
    rw [shortfall_translate,zero_add,show dyadicInt 1+dyadicInt 1=dyadicInt 2 by apply Subtype.ext; norm_num]
  simp only [arrayJ,dyadicMid_zero_two,hs,ht] at hj
  linarith
lemma shortfall_half_moment (μ:Measure NonAffineArray) (hu:∀ᵐd ∂μ,UnitArray d.val)
    (ht:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ)
    (hi:Integrable (fun d:NonAffineArray => arrayShortfall 0 (dyadicInt 1) d.val) μ) :
    Integrable (fun d:NonAffineArray => arrayShortfall 0 (dyadicInt 1) d.val) (μ.map nonaffineHalf) ∧
      (∫d:NonAffineArray,arrayShortfall 0 (dyadicInt 1) d.val ∂μ.map nonaffineHalf)≤
        ∫d:NonAffineArray,arrayShortfall 0 (dyadicInt 1) d.val ∂μ := by
  let f:NonAffineArray→ℝ := fun d => arrayShortfall 0 (dyadicInt 1) d.val
  have hf:Measurable f := (continuous_arrayShortfall _ _).measurable.comp measurable_subtype_coe
  have hb : Integrable (fun d => f (nonaffineHalf d)) μ := (hi.const_mul 2).mono'
    (hf.comp measurable_nonaffineHalf).aestronglyMeasurable (by
      filter_upwards [hu] with d hd
      rw [Real.norm_eq_abs,abs_of_nonneg (shortfall_unit_mem _ (nonaffineHalf_unit d hd) _ _ (by norm_num)).1]
      exact shortfall_half_bound d hd)
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable measurable_nonaffineHalf.aemeasurable).mpr hb,?_⟩
  rw [integral_map measurable_nonaffineHalf.aemeasurable hf.aestronglyMeasurable]
  have hbt : Integrable (fun d => f (nonaffineHalf (nonaffineTranslation (dyadicHalf (dyadicInt 1)) d))) μ := by
    have hmap : Integrable (fun d => f (nonaffineHalf d)) (μ.map (nonaffineTranslation (dyadicHalf (dyadicInt 1)))) := by rw [ht]; exact hb
    exact (integrable_map_measure (hf.comp measurable_nonaffineHalf).aestronglyMeasurable (nonaffineTranslation _).continuous.measurable.aemeasurable).mp hmap
  have havg := integral_mono_ae ((hb.add hbt).div_const 2) hi (hu.mono (fun d hd => half_shortfall_average d hd))
  simp only [Pi.add_apply] at havg
  rw [integral_div,integral_add hb hbt] at havg
  have he := integral_invariant_translation μ (dyadicHalf (dyadicInt 1)) (ht _) (fun d => f (nonaffineHalf d)) (hf.comp measurable_nonaffineHalf)
  rw [he] at havg
  linarith
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma backward_shortfall_moment (n:ℕ) :
    Integrable (fun d:NonAffineArray => arrayShortfall 0 (dyadicInt 1) d.val) (S.backwardLaw L n) ∧
    (∫d:NonAffineArray,arrayShortfall 0 (dyadicInt 1) d.val ∂S.backwardLaw L n)≤1 := by
  induction n with
  | zero => rw [S.backwardLaw_zero L]; exact S.terminal_shortfall_integrable_bound L
  | succ n ih =>
    rw [S.backwardLaw_succ L]
    obtain ⟨hi,hb⟩ := shortfall_half_moment _ (S.backwardLaw_unit L n) (S.backwardLaw_translate L n) ih.1
    exact ⟨hi,hb.trans ih.2⟩
lemma backward_cap_integrable {α:ℝ} (hα:0≤α) (hα1:α≤1) (n:ℕ) :
    Integrable (fun d:NonAffineArray => capF α d.val) (S.backwardLaw L n) := by
  obtain ⟨C,hC,hb⟩ := entropyCap_upper hα hα1
  exact ((S.backward_shortfall_moment L n).1.const_mul C).mono'
    ((continuous_capF α).comp continuous_subtype_val).aestronglyMeasurable (by
      filter_upwards [S.backwardLaw_unit L n] with d hd
      rw [Real.norm_eq_abs,capF,abs_of_nonneg (entropyCap_bounds hα hα1 (shortfall_unit_mem d.val hd _ _ (by norm_num))).1]
      exact hb _ (shortfall_unit_mem d.val hd _ _ (by norm_num)))
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_EndpointShapes
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_EndpointClasses
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TerminalStrict
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
lemma measurable_fineCap (α:ℝ) (n:ℕ) (z:DyadicTime) : Measurable (fineCap α n z) :=
  (continuous_capF α).measurable.comp (measurable_subtype_coe.comp ((measurable_nonaffineHalf.iterate n).comp (nonaffineTranslation z).continuous.measurable))
lemma fineCap_zero (α:ℝ) (n:ℕ) (d:NonAffineArray) : fineCap α n 0 d=capF α ((nonaffineHalf^[n]) d).val := by
  have he : nonaffineTranslation 0 d=d := by apply Subtype.ext; exact arrayTranslate_zero d.val
  simp only [fineCap,he]
lemma fineCap_translate (α:ℝ) (n:ℕ) (z:DyadicTime) (d:NonAffineArray) :
    fineCap α n z d=fineCap α n 0 (nonaffineTranslation z d) := by rw [fineCap_zero]; rfl
lemma slow_interval_exists {d:DistanceArray} {c:ℝ} (hu:UnitArray d) (hs:SlowShape (realArray d) c) :
    ∃a b:ℝ,a<b ∧ ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t≤c*|(t:ℝ)-(s:ℝ)| := by
  rcases slowShape_dyadic hu hs with h|⟨a,hl,h⟩|⟨b,hr,h⟩|⟨a,b,hab,hl,hr,h⟩
  · exact ⟨0,1,by norm_num,fun s t _ _ => h s t⟩
  · exact ⟨a,a+1,by linarith,fun s t hs ht => h s t hs.1 ht.1⟩
  · exact ⟨b-1,b,by linarith,fun s t hs ht => h s t hs.2 ht.2⟩
  · exact ⟨a,b,hab,h⟩
lemma fineCap_eventually_one (α:ℝ) {d:NonAffineArray} (hu:UnitArray d.val)
    (hs:SlowShape (realArray d.val) (999/1000)) : ∃z:DyadicTime,∀ᶠn:ℕ in atTop,fineCap α n z d=1 := by
  obtain ⟨a,b,hab,hslow⟩ := slow_interval_exists hu hs
  obtain ⟨z,haz,hzb⟩ := dyadic_between hab
  have ht : Tendsto (fun n:ℕ => (1:ℝ)/(2:ℝ)^n) atTop (𝓝 0) := by
    simpa only [one_div,inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤2⁻¹) (by norm_num : (2:ℝ)⁻¹<1)
  refine ⟨z,?_⟩
  filter_upwards [ht.eventually (gt_mem_nhds (sub_pos.mpr hzb))] with n hn
  unfold fineCap capF
  rw [halfIterate_shortfall n _ (arrayTranslate_unit _ _ hu),dyadicFine_zero]
  change entropyCap α (arrayShortfall 0 (dyadicFine n (dyadicInt 1)) (arrayTranslate z d.val))=1
  rw [shortfall_translate,zero_add]
  apply entropyCap_one
  have hp : 0<(1:ℝ)/(2:ℝ)^n := by positivity
  have he : ((dyadicFine n (dyadicInt 1)+z:DyadicTime):ℝ)=(1:ℝ)/(2:ℝ)^n+(z:ℝ) := by simp only [AddSubgroup.coe_add,dyadicFine_val,dyadicInt_val,Int.cast_one]
  have hb := hslow z (dyadicFine n (dyadicInt 1)+z) ⟨haz.le,hzb.le⟩ (by rw [he]; constructor <;> linarith)
  rw [he,abs_of_pos (by linarith)] at hb
  have hh : d.val.val z (dyadicFine n (dyadicInt 1)+z)/(((dyadicFine n (dyadicInt 1)+z:DyadicTime):ℝ)-(z:ℝ))≤999/1000 := by
    apply (div_le_iff₀ (show 0<((dyadicFine n (dyadicInt 1)+z:DyadicTime):ℝ)-(z:ℝ) by rw [he]; linarith)).mpr
    simpa only [he] using hb
  unfold arrayShortfall
  linarith
lemma measurableSet_fineCapEvent (α:ℝ) (z:DyadicTime) (N:ℕ) : MeasurableSet (fineCapEvent α z N) := by
  have he : fineCapEvent α z N=⋂n:ℕ,⋂_:N≤n,(fineCap α n z)⁻¹'{1} := by
    ext d; simp only [fineCapEvent,mem_ofPred_eq,mem_iInter,mem_preimage,mem_singleton_iff]
  rw [he]
  exact MeasurableSet.iInter (fun n => MeasurableSet.iInter (fun _ : N≤n => (measurable_fineCap α n z) (measurableSet_singleton 1)))
lemma fineCapEvent_translate (α:ℝ) (z:DyadicTime) (N:ℕ) :
    fineCapEvent α z N=(nonaffineTranslation z)⁻¹'fineCapEvent α 0 N := by
  ext d
  change (∀n≥N,fineCap α n z d=1) ↔ (∀n≥N,fineCap α n 0 (nonaffineTranslation z d)=1)
  constructor <;> intro h n hn
  · rw [←fineCap_translate]; exact h n hn
  · rw [fineCap_translate]; exact h n hn
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma fineCap_integrable {α:ℝ} (hα:0≤α) (hα1:α≤1) (n:ℕ) : Integrable (fineCap α n 0) L.terminal := by
  change Integrable (fun d => fineCap α n 0 d) L.terminal
  simp_rw [fineCap_zero]
  exact (integrable_map_measure ((continuous_capF α).measurable.comp measurable_subtype_coe).aestronglyMeasurable
    (measurable_nonaffineHalf.iterate n).aemeasurable).mp (S.backward_cap_integrable L hα hα1 n)
lemma fineCap_integral (α:ℝ) (n:ℕ) : (∫d,fineCap α n 0 d ∂L.terminal)=(∫d:NonAffineArray,capF α d.val ∂S.backwardLaw L n) := by
  simp_rw [fineCap_zero]
  exact (integral_map (measurable_nonaffineHalf.iterate n).aemeasurable (show AEStronglyMeasurable (fun d:NonAffineArray => capF α d.val) (S.backwardLaw L n) from ((continuous_capF α).measurable.comp measurable_subtype_coe).aestronglyMeasurable)).symm
lemma terminal_has_positive_event (α:ℝ) (hne:L.terminal≠0) : ∃N:ℕ,0<L.terminal (fineCapEvent α 0 N) := by
  have hc : ∀ᵐd ∂L.terminal,d∈⋃z:DyadicTime,⋃N:ℕ,fineCapEvent α z N := by
    filter_upwards [S.unit_aeterminal L,S.shape_aeterminal L] with d hu hs
    obtain ⟨z,hz⟩ := fineCap_eventually_one α hu hs
    obtain ⟨N,hN⟩ := eventually_atTop.mp hz
    exact mem_iUnion.mpr ⟨z,mem_iUnion.mpr ⟨N,hN⟩⟩
  by_contra h
  push Not at h
  have hz (z:DyadicTime) (N:ℕ) : L.terminal (fineCapEvent α z N)=0 := by
    rw [fineCapEvent_translate,←Measure.map_apply (nonaffineTranslation z).continuous.measurable (measurableSet_fineCapEvent α 0 N),S.terminal_translate L z]
    exact le_zero_iff.mp (h N)
  have hm : L.terminal (⋃z:DyadicTime,⋃N:ℕ,fineCapEvent α z N)=0 := measure_iUnion_null (fun z => measure_iUnion_null (hz z))
  have he : L.terminal univ=0 := by
    have hae : (⋃z:DyadicTime,⋃N:ℕ,fineCapEvent α z N)=ᵐ[L.terminal] (univ:Set NonAffineArray) := by
      rw [Filter.eventuallyEq_set]
      filter_upwards [hc] with d hd
      exact ⟨fun _ => mem_univ d,fun _ => hd⟩
    rw [←measure_congr hae]
    exact hm
  exact hne (Measure.measure_univ_eq_zero.mp he)

lemma terminal_event_lower_oai {α:ℝ} (hα:0≤α) (hα1:α≤1) (hne:L.terminal≠0) :
    ∃δ:ℝ,0<δ ∧ ∀ᶠn:ℕ in atTop,δ≤∫d:NonAffineArray,capF α d.val ∂S.backwardLaw L n := by
  obtain ⟨N,hN⟩ := S.terminal_has_positive_event L α hne
  let E:=fineCapEvent α 0 N
  have hE : MeasurableSet E := measurableSet_fineCapEvent α 0 N
  have he (n:ℕ) (hn:N≤n) : (fineCap α n 0)=ᵐ[L.terminal.restrict E] (fun _ => (1:ℝ)) :=
    (ae_restrict_mem hE).mono (fun d hd => hd n hn)
  have hi : Integrable (fun _:NonAffineArray => (1:ℝ)) (L.terminal.restrict E) :=
    (S.fineCap_integrable L hα hα1 N).restrict.congr (he N le_rfl)
  have : IsFiniteMeasure (L.terminal.restrict E) := (integrable_const_iff_isFiniteMeasure (by norm_num : (1:ℝ)≠0)).mp hi
  have hf : L.terminal E≠∞ := by
    have hh : L.terminal E<∞ := by simpa only [Measure.restrict_apply_univ] using (measure_lt_top (L.terminal.restrict E) univ)
    exact hh.ne
  refine ⟨L.terminal.real E,ENNReal.toReal_pos hN.ne' hf,?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [←S.fineCap_integral L α n]
  have hh := integral_mono_measure (Measure.restrict_le_self : L.terminal.restrict E≤L.terminal)
    (show 0≤ᵐ[L.terminal] fineCap α n 0 from (S.unit_aeterminal L).mono (fun d hd => by
      rw [fineCap_zero,capF]
      exact (entropyCap_bounds hα hα1 (shortfall_unit_mem _ (halfIterate_unit n d hd) _ _ (by norm_num))).1))
    (S.fineCap_integrable L hα hα1 n)
  rw [integral_congr_ae (he n hn),integral_const] at hh
  simpa only [smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ] using hh
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.CriticalScaleSequence.terminal_event_lower_oai := @OAI.StandardMapEntropy.CriticalScaleSequence.terminal_event_lower_oai
