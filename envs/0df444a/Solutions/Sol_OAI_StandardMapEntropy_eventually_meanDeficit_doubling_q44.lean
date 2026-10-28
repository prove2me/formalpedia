-- Prove2me | solution 1 for OAI.StandardMapEntropy.eventually_meanDeficit_doubling_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:21:18.576667+00:00
-- url     : https://prove2.me/submissions/9b08c6cf-07b4-4fbc-a3b3-4a7eeb777e8f

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002
import Theorems.Thm_OAI_StandardMapEntropy_eventually_small_endpoints_slice_q44

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

lemma linearSolution_step (v : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    linearSolution v a b (n + 2) =
      v (n + 1) * linearSolution v a b (n + 1) - linearSolution v a b n := rfl

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
-- module Solutions.OAIQ44_CM.StandardMap_TransferCore
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

lemma transferProduct_pair (v : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    transferProduct v n ⟨b,a⟩ = ⟨linearSolution v a b (n+1),linearSolution v a b n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [transferProduct,ContinuousLinearMap.comp_apply,ih]
    apply Complex.ext <;> simp only [transferStep_re,transferStep_im,linearSolution_step]
lemma transferProductInv_area (v : ℕ → ℝ) (n : ℕ) : PlaneAreaPreserving (transferProductInv v n) := by
  induction n with
  | zero => intro z w; rfl
  | succ n ih => exact ih.comp (transferStepInv_area _)
lemma transferProduct_inverse (v : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    transferProduct v n (transferProductInv v n z)=z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [transferProduct, transferProductInv,ContinuousLinearMap.comp_apply,ih,transferStep_inv]
lemma transferProductInv_inverse (v : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    transferProductInv v n (transferProduct v n z)=z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [transferProduct, transferProductInv,ContinuousLinearMap.comp_apply,transferStepInv_inv,ih]
lemma transferProduct_norm_inverse (v : ℕ → ℝ) (n : ℕ) :
    ‖transferProduct v n‖=‖transferProductInv v n‖ :=
  (transferProduct_area v n).norm_inverse (transferProductInv_area v n)
    (transferProduct_inverse v n) (transferProductInv_inverse v n)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_LiftDynamics
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
lemma liftIter_add (k : ℝ) (i j : ℤ) (z : ℝ × ℝ) :
    liftIter k (i+j) z=liftIter k i (liftIter k j z) := by
  simp only [liftIter,zpow_add,Equiv.Perm.coe_mul,Function.comp_apply]
lemma liftIter_nat (k : ℝ) (n : ℕ) (z : ℝ × ℝ) :
    liftIter k n z=(liftedOrbit k z.2 z.1 (n+1),liftedOrbit k z.2 z.1 n) := by
  induction n with
  | zero => simp [liftIter,liftedOrbit]
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,add_comm,liftIter_add,ih]
    simp only [liftIter,zpow_one]
    change (phi k (liftedOrbit k z.2 z.1 (n+1))-liftedOrbit k z.2 z.1 n,
      liftedOrbit k z.2 z.1 (n+1))=_
    rfl
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
lemma liftSegmentTransfer_eq (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) :
    liftSegmentTransfer k z a n=transferProduct
      (orbitCoefficient k (liftIter k a z).2 (liftIter k a z).1) n := by
  unfold liftSegmentTransfer
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [transferProduct,ih]
    congr 2
    unfold liftSegmentCoefficient orbitCoefficient
    rw [show a+((n+1:ℕ):ℤ)-1=(n:ℤ)+a by push_cast; ring,liftIter_add,liftIter_nat]
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
-- module Solutions.OAIQ44_CM.StandardMap_CocycleAlgebra
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
lemma transferProduct_concat (v : ℕ → ℝ) (m n : ℕ) :
    transferProduct v (m+n)=(transferProduct (fun i => v (m+i)) n).comp (transferProduct v m) := by
  induction n with
  | zero => simp [transferProduct]
  | succ n ih =>
    rw [show m+(n+1)=(m+n)+1 by omega,transferProduct,ih,transferProduct]
    simp only [ContinuousLinearMap.comp_assoc,Nat.add_assoc]
lemma torusSegmentCoefficient_shift (k : ℝ) (z : Torus) (a : ℤ) (m : ℕ) :
    (fun i => torusSegmentCoefficient k z a (m+i))=torusSegmentCoefficient k z (a+(m:ℤ)) := by
  funext i
  unfold torusSegmentCoefficient
  congr 3
  push_cast
  ring
lemma torusSegmentTransfer_concat (k : ℝ) (z : Torus) (a : ℤ) (m n : ℕ) :
    torusSegmentTransfer k z a (m+n)=
      (torusSegmentTransfer k z (a+(m:ℤ)) n).comp (torusSegmentTransfer k z a m) := by
  unfold torusSegmentTransfer
  rw [transferProduct_concat,torusSegmentCoefficient_shift]
lemma torusIter_neg_swap (k : ℝ) (n : ℕ) (z : Torus) :
    torusIter k (-(n:ℤ)) z=(torusIter k (n:ℤ) z.swap).swap := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show ((n+1:ℕ):ℤ)=1+(n:ℤ) by omega,show -(1+(n:ℤ))=(-1)+(-(n:ℤ)) by ring,
      torusIter_add,torusIter_add,ih]
    simp only [torusIter,zpow_neg_one,zpow_one,Equiv.Perm.inv_def,torusStep_symm_apply,torusStep_apply,
      recurrenceMap,Prod.fst_swap,Prod.snd_swap,Prod.swap_prod_mk]
lemma torus_backward_pair_coordinate (k : ℝ) (z : Torus) (n : ℕ) :
    (torusIter k (-(n:ℤ)-1) z).1=(torusIter k (n:ℤ) z.swap).1 := by
  rw [show -(n:ℤ)-1=(-1)+(-(n:ℤ)) by ring,torusIter_add,torusIter_neg_swap]
  rfl
lemma torusSegmentTransfer_reverse_identity (k : ℝ) (z : Torus) (n : ℕ) (u : ℂ) :
    torusSegmentTransfer k z (-(n:ℤ)) n
      (planeSwap (torusSegmentTransfer k z.swap 0 n (planeSwap u)))=u := by
  induction n generalizing u with
  | zero => simp [torusSegmentTransfer,transferProduct]
  | succ n ih =>
    have hc : torusSegmentTransfer k z (-((n+1:ℕ):ℤ)) (n+1)=
        (torusSegmentTransfer k z (-(n:ℤ)) n).comp
          (transferStep (torusPotential k (torusIter k (-(n:ℤ)-1) z).1)) := by
      rw [show n+1=1+n by omega,torusSegmentTransfer_concat]
      congr 1
      · congr 1; push_cast; ring
      · simp only [torusSegmentTransfer,transferProduct,ContinuousLinearMap.comp_id,
          torusSegmentCoefficient]
        exact congrArg (fun t : ℤ => transferStep (torusPotential k (torusIter k t z).1)) (by omega)
    rw [hc]
    change torusSegmentTransfer k z (-(n:ℤ)) n
      (transferStep (torusPotential k (torusIter k (-(n:ℤ)-1) z).1)
        (planeSwap (transferStep (torusSegmentCoefficient k z.swap 0 (n+1))
          (torusSegmentTransfer k z.swap 0 n (planeSwap u)))))=u
    have hcoef : torusSegmentCoefficient k z.swap 0 (n+1)=
        torusPotential k (torusIter k (-(n:ℤ)-1) z).1 := by
      unfold torusSegmentCoefficient
      rw [show (0:ℤ)+((n+1:ℕ):ℤ)-1=(n:ℤ) by omega,torus_backward_pair_coordinate]
    rw [hcoef]
    have he (v : ℝ) (w : ℂ) : transferStep v (planeSwap (transferStep v w))=planeSwap w := by
      apply Complex.ext <;> simp
    rw [he]
    exact ih u
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
-- module Solutions.OAIQ44_CM.StandardMap_CancellationVector
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
lemma torus_reverse_operator (k : ℝ) (z : Torus) (n : ℕ) :
    (planeSwap.comp (torusSegmentTransfer k z.swap 0 n)).comp planeSwap=
      transferProductInv (torusSegmentCoefficient k z (-(n:ℤ))) n := by
  ext u
  apply (show Function.Injective (torusSegmentTransfer k z (-(n:ℤ)) n) from fun x y hxy => by
    have := congrArg (transferProductInv (torusSegmentCoefficient k z (-(n:ℤ))) n) hxy
    simpa only [torusSegmentTransfer,transferProductInv_inverse] using this)
  exact (torusSegmentTransfer_reverse_identity k z n u).trans (transferProduct_inverse _ _ _).symm
lemma small_vector_of_cancellation (M : ℝ) (hM : 1 < M) (δ : ℝ) (hδ : 0 ≤ δ)
    (A B : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A) (n : ℕ)
    (ha : M^((1-δ)*(n:ℝ)) ≤ ‖A‖) (hab : ‖B‖ ≤ M^(δ*(n:ℝ))) :
    ∃ u : ℂ, ‖u‖=1 ∧ ‖A u‖ ≤ M^(-((1-2*δ)*(n:ℝ))) ∧
      ‖B (A u)‖ ≤ M^(-((1-2*δ)*(n:ℝ))) := by
  obtain ⟨a,ha1,_,_,hsmall,hAn⟩ := hA.singular_pair
  have hMp : 0 < M := by linarith
  have hneg : ‖A (quarterTurn a)‖ ≤ M^(-((1-δ)*(n:ℝ))) := by
    rw [hsmall,Real.rpow_neg hMp.le]
    exact (inv_le_inv₀ (by linarith : 0 < ‖A‖) (Real.rpow_pos_of_pos hMp _)).mpr ha
  refine ⟨quarterTurn a,by simpa [norm_quarterTurn] using ha1,?_,?_⟩
  · exact hneg.trans (Real.rpow_le_rpow_of_exponent_le hM.le (by nlinarith [Nat.cast_nonneg (α:=ℝ) n]))
  · calc
      _ ≤ ‖B‖*‖A (quarterTurn a)‖ := B.le_opNorm _
      _ ≤ M^(δ*(n:ℝ))*M^(-((1-δ)*(n:ℝ))) := mul_le_mul hab hneg (norm_nonneg _) (Real.rpow_nonneg hMp.le _)
      _ = _ := by rw [← Real.rpow_add hMp]; congr 1; ring
lemma torus_cancellation_vector (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (z : Torus)
    (hback : growthBase k^((1-δ)*(n:ℝ)) ≤ ‖torusSegmentTransfer k z (-(n:ℤ)) n‖)
    (hfull : ‖torusSegmentTransfer k z (-(n:ℤ)) (n+n)‖ ≤ growthBase k^(δ*(n:ℝ))) :
    ∃ u : ℂ, ‖u‖=1 ∧
      ‖torusSegmentTransfer k z.swap 0 n (planeSwap u)‖ ≤ growthBase k^(-((1-2*δ)*(n:ℝ))) ∧
      ‖torusSegmentTransfer k z 0 n u‖ ≤ growthBase k^(-((1-2*δ)*(n:ℝ))) := by
  let A := transferProductInv (torusSegmentCoefficient k z (-(n:ℤ))) n
  let B := torusSegmentTransfer k z (-(n:ℤ)) (n+n)
  have hM : 1 < growthBase k := by linarith [growthBase_ge_four k hk]
  have ha : growthBase k^((1-δ)*(n:ℝ)) ≤ ‖A‖ := by
    dsimp only [A]
    rw [← transferProduct_norm_inverse]
    exact hback
  obtain ⟨u,hu,hum,hup⟩ := small_vector_of_cancellation (growthBase k) hM δ hδ A B
    (transferProductInv_area _ _) n ha hfull
  refine ⟨u,hu,?_,?_⟩
  · dsimp only [A] at hum
    rw [← torus_reverse_operator,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,norm_planeSwap] at hum
    exact hum
  · have he : B (A u)=torusSegmentTransfer k z 0 n u := by
      dsimp only [A,B]
      rw [torusSegmentTransfer_concat,neg_add_cancel,ContinuousLinearMap.comp_apply]
      simp only [torusSegmentTransfer,transferProduct_inverse]
    rwa [he] at hup
lemma torusSegmentTransfer_first (k : ℝ) (z : Torus) (n : ℕ) :
    torusSegmentTransfer k z 0 (n+1)=
      (torusSegmentTransfer k (torusStep k z) 0 n).comp (transferStep (torusPotential k z.1)) := by
  rw [show n+1=1+n by omega,torusSegmentTransfer_concat]
  change (torusSegmentTransfer k z 1 n).comp (torusSegmentTransfer k z 0 1)=_
  have hs : torusSegmentTransfer k (torusStep k z) 0 n=torusSegmentTransfer k z 1 n := by
    exact torusSegmentTransfer_shift k z 0 1 n
  rw [hs]
  simp only [torusSegmentTransfer,transferProduct,torusSegmentCoefficient,zero_add,Nat.cast_one,
    sub_self,torusIter_zero,ContinuousLinearMap.comp_id]
lemma torusStep_swap_prev (k : ℝ) (z : Torus) :
    torusStep k z.swap=((torusStep k).symm z).swap := rfl
lemma torusPotential_bound (k : ℝ) (hk : 0 ≤ k) (x : Circle) : |torusPotential k x|+1 ≤ growthBase k := by
  obtain ⟨t,rfl⟩ := Quotient.mk_surjective x
  exact potential_bound k t hk
lemma max_unit_coordinate (u : ℂ) (hu : ‖u‖=1) : 1/2 ≤ max |u.re| |u.im| := by
  have hs : u.re^2+u.im^2=1 := by simpa only [Complex.sq_norm,Complex.normSq_apply,hu,one_pow,pow_two,one_mul] using (Complex.sq_norm u).symm
  by_contra h
  have hr : |u.re| < 1/2 := lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge h)
  have hi : |u.im| < 1/2 := lt_of_le_of_lt (le_max_right _ _) (lt_of_not_ge h)
  nlinarith [sq_abs u.re,sq_abs u.im,abs_nonneg u.re,abs_nonneg u.im]
lemma normalized_endpoint_norm (A : ℂ →L[ℝ] ℂ) (u : ℂ) (a R : ℝ)
    (ha : 1/2 ≤ |a|) (hR : 0 ≤ R) (h : ‖A u‖ ≤ R) : ‖A (a⁻¹ • u)‖ ≤ 2*R := by
  rw [map_smul,norm_smul,Real.norm_eq_abs,abs_inv]
  have hap : 0 < |a| := by linarith
  have hai : |a|⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hap).mpr (by linarith)
  exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (abs_nonneg a))).trans
    (mul_le_mul_of_nonneg_right hai hR)
lemma torus_small_normalize (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 0 ≤ R)
    (z : Torus) (u : ℂ) (hu : ‖u‖=1)
    (hm : ‖torusSegmentTransfer k z.swap 0 n (planeSwap u)‖ ≤ R)
    (hp : ‖torusSegmentTransfer k z 0 n u‖ ≤ R) :
    torusSmallEndpoints k n (n+1) (2*R) z ∨
      torusSmallEndpoints k (n+1) n (2*R) ((torusStep k).symm z) := by
  have hM : 1 ≤ growthBase k := by linarith [growthBase_ge_four k hk]
  have hcoord := max_unit_coordinate u hu
  by_cases hdom : |u.im| ≤ |u.re|
  · left
    have hure : 1/2 ≤ |u.re| := by simpa only [max_eq_left hdom] using hcoord
    have hur0 : u.re ≠ 0 := by intro hh; simp [hh] at hure; norm_num at hure
    have hb : |u.im/u.re| ≤ 1 := by rw [abs_div]; exact (div_le_one (by linarith : 0 < |u.re|)).mpr hdom
    refine ⟨u.im/u.re,⟨?_,?_⟩,?_,?_⟩
    · linarith [(abs_le.mp hb).1]
    · linarith [(abs_le.mp hb).2]
    · have he : (u.re⁻¹ : ℝ) • planeSwap u=⟨u.im/u.re,1⟩ := by
        apply Complex.ext <;> simp [div_eq_mul_inv,hur0,mul_comm]
      simpa only [Nat.add_sub_cancel,he] using normalized_endpoint_norm
        (torusSegmentTransfer k z.swap 0 n) (planeSwap u) u.re R hure hR hm
    · have he : (u.re⁻¹ : ℝ) • u=⟨1,u.im/u.re⟩ := by
        apply Complex.ext <;> simp [div_eq_mul_inv,hur0,mul_comm]
      simpa only [he] using normalized_endpoint_norm (torusSegmentTransfer k z 0 n) u u.re R hure hR hp
  · right
    have himdom : |u.re| ≤ |u.im| := le_of_lt (lt_of_not_ge hdom)
    have him : 1/2 ≤ |u.im| := by simpa only [max_eq_right himdom] using hcoord
    have hi0 : u.im ≠ 0 := by intro hh; simp [hh] at him; norm_num at him
    let p := torusPotential k z.2
    let w := transferStepInv p u
    have hwp : torusSegmentTransfer k ((torusStep k).symm z) 0 (n+1) w=torusSegmentTransfer k z 0 n u := by
      rw [torusSegmentTransfer_first,ContinuousLinearMap.comp_apply,Equiv.apply_symm_apply]
      change torusSegmentTransfer k z 0 n (transferStep p (transferStepInv p u))=_
      rw [transferStep_inv]
    have hwm : torusSegmentTransfer k (((torusStep k).symm z).swap) 0 (n-1) (planeSwap w)=
        torusSegmentTransfer k z.swap 0 n (planeSwap u) := by
      conv_rhs => rw [← Nat.sub_add_cancel hn,torusSegmentTransfer_first,ContinuousLinearMap.comp_apply,torusStep_swap_prev]
      congr 1
    have hwre : w.re=u.im := rfl
    have hbr : |w.im/u.im| ≤ growthBase k := by
      have hd : |u.re/u.im| ≤ 1 := by rw [abs_div]; exact (div_le_one (by linarith : 0 < |u.im|)).mpr himdom
      have he : w.im/u.im=p-u.re/u.im := by change (p*u.im-u.re)/u.im=_; field_simp
      rw [he]
      exact (abs_sub _ _).trans ((add_le_add_right hd _).trans (torusPotential_bound k hk z.2))
    refine ⟨w.im/u.im,⟨(abs_le.mp hbr).1,(abs_le.mp hbr).2⟩,?_,?_⟩
    · have he : (u.im⁻¹ : ℝ) • planeSwap w=⟨w.im/u.im,1⟩ := by
        apply Complex.ext <;> simp [hwre,div_eq_mul_inv,hi0,mul_comm]
      have hb := normalized_endpoint_norm (torusSegmentTransfer k (((torusStep k).symm z).swap) 0 (n-1))
        (planeSwap w) u.im R him hR (by rw [hwm]; exact hm)
      simpa only [he] using hb
    · have he : (u.im⁻¹ : ℝ) • w=⟨1,w.im/u.im⟩ := by
        apply Complex.ext <;> simp [hwre,div_eq_mul_inv,hi0,mul_comm]
      have hb := normalized_endpoint_norm (torusSegmentTransfer k ((torusStep k).symm z) 0 (n+1))
        w u.im R him hR (by rw [hwp]; exact hp)
      simpa only [he] using hb
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CancellationArea
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
lemma continuous_complex_mk {α : Type*} [TopologicalSpace α] (f g : α → ℝ)
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => (⟨f x,g x⟩:ℂ)) :=
  Complex.equivRealProdCLM.symm.continuous.comp (hf.prodMk hg)
lemma isClosed_torusSmallEndpoints (k : ℝ) (Np Nm : ℕ) (R : ℝ) :
    IsClosed {z : Torus | torusSmallEndpoints k Np Nm R z} := by
  let S : Set (Torus × ℝ) := {p | p.2 ∈ Icc (-growthBase k) (growthBase k) ∧
    ‖torusSegmentTransfer k p.1.swap 0 (Nm-1) ⟨p.2,1⟩‖ ≤ R ∧
    ‖torusSegmentTransfer k p.1 0 Np ⟨1,p.2⟩‖ ≤ R}
  have h1 : Continuous (fun p : Torus × ℝ =>
      ‖torusSegmentTransfer k p.1.swap 0 (Nm-1) ⟨p.2,1⟩‖) := by
    exact (((continuous_torusSegmentTransfer k 0 (Nm-1)).comp (continuous_swap.comp continuous_fst)).clm_apply
      (continuous_complex_mk _ _ continuous_snd continuous_const)).norm
  have h2 : Continuous (fun p : Torus × ℝ =>
      ‖torusSegmentTransfer k p.1 0 Np ⟨1,p.2⟩‖) := by
    exact (((continuous_torusSegmentTransfer k 0 Np).comp continuous_fst).clm_apply
      (continuous_complex_mk _ _ continuous_const continuous_snd)).norm
  have hS : IsCompact S := by
    have hc := (isCompact_univ : IsCompact (univ : Set Torus)).prod
      (isCompact_Icc : IsCompact (Icc (-growthBase k) (growthBase k)))
    convert hc.inter_right ((isClosed_le h1 (continuous_const (y:=R))).inter (isClosed_le h2 (continuous_const (y:=R)))) using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    simp only [S,mem_inter_iff,mem_prod,mem_univ,true_and,mem_ofPred_eq]
  have he : {z : Torus | torusSmallEndpoints k Np Nm R z}=Prod.fst '' S := by
    ext z
    constructor
    · rintro ⟨b,hb,hm,hp⟩
      exact ⟨(z,b),⟨hb,hm,hp⟩,rfl⟩
    · rintro ⟨⟨w,b⟩,hs,hw⟩
      subst z
      exact ⟨b,hs⟩
  rw [he]
  exact (hS.image continuous_fst).isClosed
lemma scalar_pairMagnitude_le_norm (v : ℕ → ℝ) (b : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    pairMagnitude (linearSolution v 1 b) N ≤ ‖transferProduct v (N-1) ⟨b,1⟩‖ := by
  rw [transferProduct_pair,Nat.sub_add_cancel hN]
  exact max_le (Complex.abs_re_le_norm ⟨_,_⟩) (Complex.abs_im_le_norm ⟨_,_⟩)
lemma torusSmallEndpoints_lift_sub (k q a R : ℝ) (Np Nm : ℕ) (hNp : 1 ≤ Np) (hNm : 1 ≤ Nm)
    (h : torusSmallEndpoints k Np Nm R (liftProjection (q,a))) :
    ∃ b : ℝ,
      pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤ R ∧
      pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤ R := by
  obtain ⟨b,_,hm,hp⟩ := h
  refine ⟨b,?_,?_⟩
  · have he : torusSegmentTransfer k (liftProjection (q,a)).swap 0 (Nm-1)=
        transferProduct (orbitCoefficient k q a) (Nm-1) := by
      change torusSegmentTransfer k (liftProjection (a,q)) 0 (Nm-1)=_
      rw [torusSegmentTransfer_lift,liftSegmentTransfer_eq,liftIter_zero]
    rw [he] at hm
    exact (scalar_pairMagnitude_le_norm _ b Nm hNm).trans hm
  · have he : torusSegmentTransfer k (liftProjection (q,a)) 0 Np ⟨1,b⟩=
        transferProduct (orbitCoefficient k q (phi k q-a)) (Np-1) ⟨potential k q-b,1⟩ := by
      conv_lhs => rw [← Nat.sub_add_cancel hNp,torusSegmentTransfer_first,ContinuousLinearMap.comp_apply,
        ← liftProjection_step,torusSegmentTransfer_lift,liftSegmentTransfer_eq,liftIter_zero]
      simp only [liftStep_apply]
      congr 1
      apply Complex.ext <;> simp [liftProjection,torusPotential_coe]
    rw [he] at hp
    exact (scalar_pairMagnitude_le_norm _ _ Np hNp).trans hp
lemma area_small_endpoints_of_slices (k : ℝ) (Np Nm : ℕ) (hNp : 1 ≤ Np) (hNm : 1 ≤ Nm)
    (R : ℝ) (K : ℝ≥0∞)
    (hs : ∀ q : ℝ, volume {a : ℝ | a ∈ Icc 0 1 ∧ ∃ b : ℝ,
      pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤ R ∧
      pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤ R} ≤ K) :
    area {z | torusSmallEndpoints k Np Nm R z} ≤ K := by
  let E := {z | torusSmallEndpoints k Np Nm R z}
  have hE : MeasurableSet E := (isClosed_torusSmallEndpoints k Np Nm R).measurableSet
  have hproj : Measurable liftProjection :=
    (((AddCircle.continuous_mk' (1:ℝ)).comp continuous_fst).prodMk
      ((AddCircle.continuous_mk' (1:ℝ)).comp continuous_snd)).measurable
  have hmp := (AddCircle.measurePreserving_mk (1:ℝ) (0:ℝ)).prod
    (AddCircle.measurePreserving_mk (1:ℝ) (0:ℝ))
  have hm : ((volume.restrict (Ioc (0:ℝ) 1)).prod (volume.restrict (Ioc (0:ℝ) 1)))
      (liftProjection ⁻¹' E)=area E := by
    convert! hmp.measure_preimage hE.nullMeasurableSet using 1
    all_goals try with_reducible_and_instances rfl
    simp only [zero_add]; rfl
  rw [← hm,Measure.prod_apply (hE.preimage hproj)]
  calc
    _ ≤ ∫⁻ _q : ℝ, K ∂(volume.restrict (Ioc (0:ℝ) 1)) := by
      apply lintegral_mono
      intro q
      change (volume.restrict (Ioc (0:ℝ) 1)) (Prod.mk q ⁻¹' (liftProjection ⁻¹' E)) ≤ K
      have hmsec : MeasurableSet (Prod.mk q ⁻¹' (liftProjection ⁻¹' E)) := by
        exact (hE.preimage hproj).preimage (measurable_const.prodMk measurable_id)
      rw [Measure.restrict_apply hmsec]
      apply (measure_mono (show (Prod.mk q ⁻¹' (liftProjection ⁻¹' E)) ∩ Ioc 0 1 ⊆
          {a : ℝ | a ∈ Icc 0 1 ∧ ∃ b : ℝ,
            pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤ R ∧
            pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤ R} from ?_)).trans (hs q)
      intro a ha
      exact ⟨⟨ha.2.1.le,ha.2.2⟩,torusSmallEndpoints_lift_sub k q a R Np Nm hNp hNm ha.1⟩
    _ = K := by simp
lemma eventually_small_endpoints_area :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0 < k → M₀ ≤ growthBase k →
      ∀ n Np Nm : ℕ, 10000000 ≤ n → n ≤ Np ∧ Np ≤ n+1 → n ≤ Nm ∧ Nm ≤ n+1 →
      area {z | torusSmallEndpoints k Np Nm
        (3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) z} ≤ ENNReal.ofReal ((1/4:ℝ)^n) := by
  obtain ⟨M₀,hM⟩ := eventually_small_endpoints_slice_q44
  refine ⟨M₀,?_⟩
  intro k hk hMk n Np Nm hn hNp hNm
  exact area_small_endpoints_of_slices k Np Nm (by omega) (by omega) _ _
    (fun q => hM k hk hMk q n Np Nm hn hNp hNm)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CancellationTheorem
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
lemma isClosed_torusCancellation (k : ℝ) (n : ℕ) : IsClosed {z | torusCancellation k n z} :=
  (isClosed_le continuous_const (continuous_torusSegmentTransfer k _ _).norm).inter
    ((isClosed_le continuous_const (continuous_torusSegmentTransfer k _ _).norm).inter
      (isClosed_le (continuous_torusSegmentTransfer k _ _).norm continuous_const))
lemma torusSmallEndpoints_mono (k : ℝ) (Np Nm : ℕ) {R S : ℝ} (hRS : R≤S) (z : Torus)
    (h : torusSmallEndpoints k Np Nm R z) : torusSmallEndpoints k Np Nm S z := by
  obtain ⟨b,hb,hm,hp⟩ := h
  exact ⟨b,hb,hm.trans hRS,hp.trans hRS⟩
lemma torusCancellation_sub_small (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 1≤n) :
    {z | torusCancellation k n z} ⊆
      {z | torusSmallEndpoints k n (n+1) (3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) z} ∪
      ((torusStep k).symm ⁻¹' {z | torusSmallEndpoints k (n+1) n (3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) z}) := by
  intro z hz
  obtain ⟨u,hu,hm,hp⟩ := torus_cancellation_vector k hk n (1/100000000) (by norm_num) z hz.1 hz.2.2
  have hM : 1≤growthBase k := by linarith [growthBase_ge_four k hk]
  have hR : 0≤growthBase k^(-((1-2*(1/100000000:ℝ))*(n:ℝ))) := Real.rpow_nonneg (by linarith) _
  have hRS : 2*growthBase k^(-((1-2*(1/100000000:ℝ))*(n:ℝ))) ≤
      3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ))) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hM
      (show -((1-2*(1/100000000:ℝ))*(n:ℝ)) ≤ -((1-3/100000000:ℝ)*(n:ℝ)) by
        nlinarith [Nat.cast_nonneg (α:=ℝ) n])
    nlinarith [Real.rpow_nonneg (show 0≤growthBase k by linarith) (-((1-3/100000000:ℝ)*(n:ℝ)))]
  rcases torus_small_normalize k hk n hn _ hR z u hu hm hp with h|h
  · exact Or.inl (torusSmallEndpoints_mono _ _ _ hRS _ h)
  · exact Or.inr (torusSmallEndpoints_mono _ _ _ hRS _ h)
lemma eventually_cancellation_area_large :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0<k → M₀≤growthBase k → ∀ n : ℕ, 10000000≤n →
      area {z | torusCancellation k n z} ≤ 2*ENNReal.ofReal ((1/4:ℝ)^n) := by
  obtain ⟨M₀,hM⟩ := eventually_small_endpoints_area
  refine ⟨M₀,?_⟩
  intro k hk hMk n hn
  have hp := hM k hk hMk n n (n+1) hn ⟨le_rfl,by omega⟩ ⟨by omega,le_rfl⟩
  have hm := hM k hk hMk n (n+1) n hn ⟨by omega,le_rfl⟩ ⟨le_rfl,by omega⟩
  have hmp : MeasurePreserving (torusStep k).symm area area := measurePreserving_torusStep_symm k
  calc
    _ ≤ _ := measure_mono (torusCancellation_sub_small k hk.le n (by omega))
    _ ≤ _ := measure_union_le _ _
    _ = area {z | torusSmallEndpoints k n (n+1) (3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) z} +
        area {z | torusSmallEndpoints k (n+1) n (3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) z} := by
      rw [hmp.measure_preimage (isClosed_torusSmallEndpoints _ _ _ _).measurableSet.nullMeasurableSet]
    _ ≤ _ := by rw [two_mul]; exact add_le_add hp hm
lemma cancellationConstant_pos : 0 < cancellationConstant := by unfold cancellationConstant; positivity
lemma eventually_cancellation_area :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0<k → M₀≤growthBase k → ∀ n : ℕ,
      area {z | torusCancellation k n z} ≤ ENNReal.ofReal (cancellationConstant*(1/4:ℝ)^n) := by
  obtain ⟨M₀,hM⟩ := eventually_cancellation_area_large
  refine ⟨M₀,?_⟩
  intro k hk hMk n
  by_cases hn : 10000000≤n
  · apply (hM k hk hMk n hn).trans
    have hc : 2 ≤ cancellationConstant := by
      have hp : (1:ℝ)≤4^10000000 := one_le_pow₀ (by norm_num)
      simpa only [mul_one,cancellationConstant] using mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤2)
    rw [ENNReal.ofReal_mul cancellationConstant_pos.le]
    exact mul_le_mul_of_nonneg_right (by simpa using ENNReal.ofReal_le_ofReal hc) bot_le
  · have hprob : area {z | torusCancellation k n z}≤1 := by
      calc
        _≤area univ := measure_mono (subset_univ _)
        _=1 := measure_univ
    apply hprob.trans
    have he : (4:ℝ)^n*(1/4:ℝ)^n=1 := by rw [← mul_pow]; norm_num
    have hp := pow_le_pow_right₀ (show (1:ℝ)≤4 by norm_num) (show n≤10000000 by omega)
    have hc : 1 ≤ cancellationConstant*(1/4:ℝ)^n := by
      have hh := mul_le_mul_of_nonneg_right hp (show 0≤(1/4:ℝ)^n by positivity)
      rw [he] at hh
      have h2 := mul_le_mul_of_nonneg_right (show (1:ℝ)≤2 by norm_num)
        (show 0≤(4:ℝ)^10000000*(1/4:ℝ)^n by positivity)
      simpa only [one_mul,cancellationConstant,mul_assoc] using hh.trans (by simpa only [one_mul] using h2)
    simpa using ENNReal.ofReal_le_ofReal hc
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
lemma wingDefect_nonneg (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) : 0 ≤ wingDefect k z n := by
  have hh := productDistance_le k hk z 0 (n:ℤ)
  simp only [Int.cast_natCast,Int.cast_zero,sub_zero,Nat.abs_cast] at hh
  have hm := min_le_right (productDistance k z 0 (-(n:ℤ))) (productDistance k z 0 (n:ℤ))
  unfold wingDefect; linarith
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
lemma torusCancellation_iff_distance (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    torusCancellation k n z ↔
      (1-1/100000000:ℝ)*(n:ℝ) ≤ productDistance k z 0 (-(n:ℤ)) ∧
      (1-1/100000000:ℝ)*(n:ℝ) ≤ productDistance k z 0 (n:ℤ) ∧
      productDistance k z (-(n:ℤ)) (n:ℤ) ≤ (1/100000000:ℝ)*(n:ℝ) := by
  have hM : 0 < growthBase k := lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) (growthBase_ge_four k hk)
  have hp a m : 0 < ‖torusSegmentTransfer k z a m‖ := lt_of_lt_of_le zero_lt_one (torusSegmentTransfer_norm_bounds k hk z a m).1
  rw [productDistance_symm k z 0 (-(n:ℤ))]
  have h1 : productDistance k z (-(n:ℤ)) 0=Real.log ‖torusSegmentTransfer k z (-(n:ℤ)) n‖/Real.log (growthBase k) := by
    convert productDistance_forward k z (-(n:ℤ)) n using 1  ; simp
  have h2 : productDistance k z 0 (n:ℤ)=Real.log ‖torusSegmentTransfer k z 0 n‖/Real.log (growthBase k) := by
    simpa using productDistance_forward k z 0 n
  have h3 : productDistance k z (-(n:ℤ)) (n:ℤ)=Real.log ‖torusSegmentTransfer k z (-(n:ℤ)) (n+n)‖/Real.log (growthBase k) := by
    convert productDistance_forward k z (-(n:ℤ)) (n+n) using 1  ; push_cast  ; ring_nf
  rw [h1,h2,h3]
  simp only [torusCancellation,Real.rpow_le_iff_le_log hM (hp _ _),Real.le_rpow_iff_log_le (hp _ _) hM,
    le_div_iff₀ (log_growthBase_pos k hk),div_le_iff₀ (log_growthBase_pos k hk)]
lemma large_loss_implies_cancellation (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ)
    (hl : 10000000000*(1+wingDefect k z n) < cancellationLoss k z n) :
    let s := ⌊cancellationLoss k z n/2⌋₊
    1  ≤  s ∧ s  ≤  n ∧ cancellationLoss k z n < 2*(s:ℝ)+2 ∧ torusCancellation k s z := by
  let s := ⌊cancellationLoss k z n/2⌋₊
  change 1  ≤  s ∧ s  ≤  n ∧ cancellationLoss k z n < 2*(s:ℝ)+2 ∧ torusCancellation k s z
  have hD := wingDefect_nonneg k hk z n
  obtain ⟨hl0,hln⟩ := cancellationLoss_bounds k hk z n
  have hfloor : (s:ℝ) ≤ cancellationLoss k z n/2 := Nat.floor_le (by linarith)
  have hfloor' : cancellationLoss k z n/2 < (s:ℝ)+1 := Nat.lt_floor_add_one _
  have hs1 : 1  ≤  s := by
    have hs : (1:ℝ) ≤ s := by linarith
    exact_mod_cast hs
  have hsn : s  ≤  n := by
    have hs : (s:ℝ) ≤ n := by linarith
    exact_mod_cast hs
  have hsmall : 2*wingDefect k z n+6 ≤ (1/100000000:ℝ)*(s:ℝ) := by linarith
  refine ⟨hs1,hsn,by linarith,?_⟩
  rw [torusCancellation_iff_distance k hk z s]
  obtain ⟨hL,hR⟩ := productDistance_cut_wings k hk z 0 n s hsn
  simp only [zero_sub,zero_add] at hL hR
  change (s:ℝ)-wingDefect k z n ≤ productDistance k z 0 (-(s:ℤ)) at hL
  change (s:ℝ)-wingDefect k z n ≤ productDistance k z 0 (s:ℤ) at hR
  have hcut := productDistance_truncation k hk z 0 n s hsn
  simp only [zero_sub,zero_add] at hcut
  change min (cancellationLoss k z n) (2*(s:ℝ)-2*wingDefect k z n)-6 ≤ cancellationLoss k z s at hcut
  rw [min_eq_right (by linarith)] at hcut
  have hLs := productDistance_le k hk z 0 (-(s:ℤ))
  have hRs := productDistance_le k hk z 0 (s:ℤ)
  simp only [Int.cast_neg,Int.cast_natCast,Int.cast_zero,sub_zero,abs_neg,Nat.abs_cast] at hLs hRs
  unfold cancellationLoss at hcut
  exact ⟨by linarith,by linarith,by linarith⟩
lemma cancellationLoss_pointwise_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    cancellationLoss k z n ≤ 10000000000*(1+wingDefect k z n)+
      ∑ s∈Finset.range (n+1), (if torusCancellation k s z then 2*(s:ℝ)+2 else 0) := by
  by_cases hl : cancellationLoss k z n ≤ 10000000000*(1+wingDefect k z n)
  · apply hl.trans
    have hh : 0 ≤ ∑ s∈Finset.range (n+1), (if torusCancellation k s z then 2*(s:ℝ)+2 else 0) :=
      Finset.sum_nonneg fun s hs => by split_ifs  <;> positivity
    linarith
  · obtain ⟨hs1,hsn,hls,hcan⟩ := large_loss_implies_cancellation k hk z n (lt_of_not_ge hl)
    let s := ⌊cancellationLoss k z n/2⌋₊
    have hsum := Finset.single_le_sum (f:=fun s : ℕ => if torusCancellation k s z then 2*(s:ℝ)+2 else 0)
      (fun i hi => by split_ifs  <;> positivity) (show s∈Finset.range (n+1) by simpa only [Finset.mem_range] using Nat.lt_succ_of_le hsn)
    rw [ite_eq_left hcan] at hsum
    have hD := wingDefect_nonneg k hk z n
    linarith
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
lemma continuous_wingDefect (k : ℝ) (hk : 0 ≤ k) (n : ℕ) : Continuous (fun z => wingDefect k z n) :=
  continuous_const.sub ((continuous_productDistance k hk 0 (-(n:ℤ))).min (continuous_productDistance k hk 0 (n:ℤ)))
lemma continuous_cancellationLoss (k : ℝ) (hk : 0 ≤ k) (n : ℕ) : Continuous (fun z => cancellationLoss k z n) :=
  ((continuous_productDistance k hk 0 (-(n:ℤ))).add (continuous_productDistance k hk 0 (n:ℤ))).sub
    (continuous_productDistance k hk (-(n:ℤ)) (n:ℤ))
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
lemma integral_wingDefect_le (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0<n) :
    (∫ z,wingDefect k z n ∂area) ≤ 2*(n:ℝ)*meanDeficit k n := by
  have hbd (z : Torus) : wingDefect k z n ≤ ((n:ℝ)-productDistance k z 0 (-(n:ℤ)))+((n:ℝ)-productDistance k z 0 (n:ℤ)) := by
    have hl := productDistance_le k hk z 0 (-(n:ℤ))
    have hr := productDistance_le k hk z 0 (n:ℤ)
    simp only [Int.cast_neg,Int.cast_natCast,Int.cast_zero,sub_zero,abs_neg,Nat.abs_cast] at hl hr
    unfold wingDefect
    rcases le_total (productDistance k z 0 (-(n:ℤ))) (productDistance k z 0 (n:ℤ)) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hL := (integrable_const (n:ℝ)).sub (integrable_productDistance k hk 0 (-(n:ℤ)))
  have hR := (integrable_const (n:ℝ)).sub (integrable_productDistance k hk 0 (n:ℤ))
  have hh := integral_mono ((continuous_wingDefect k hk n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (hL.add hR) hbd
  simp only [Pi.add_apply,Pi.sub_apply] at hh
  have hsum : (∫ z, ((n:ℝ)-productDistance k z 0 (-(n:ℤ)))+((n:ℝ)-productDistance k z 0 (n:ℤ)) ∂area)=
      (∫ z, ((n:ℝ)-productDistance k z 0 (-(n:ℤ))) ∂area)+(∫ z, ((n:ℝ)-productDistance k z 0 (n:ℤ)) ∂area) := by
    convert! integral_add hL hR using 1
    all_goals try with_reducible_and_instances rfl
  have hsub (i : ℤ) : (∫ z, ((n:ℝ)-productDistance k z 0 i) ∂area)=(n:ℝ)-(∫ z,productDistance k z 0 i ∂area) := by
    calc
      _ = (∫ _z : Torus, (n:ℝ) ∂area)-(∫ z,productDistance k z 0 i ∂area) := by
        convert! integral_sub (integrable_const (n:ℝ)) (integrable_productDistance k hk 0 i) using 1
        all_goals try with_reducible_and_instances rfl
      _ = _ := by simp
  rw [hsum,hsub,hsub,integral_wing_left] at hh
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  unfold meanDeficit
  field_simp [hn0] at *
  nlinarith
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
-- module Solutions.OAIQ44_CM.StandardMap_MeanCancellation
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
lemma cancellation_weight_sum (N : ℕ) :
    ∑ s∈Finset.range N, (2*(s:ℝ)+2)*(1/4:ℝ)^s ≤ 4 := by
  have hb (s : ℕ) : (s:ℝ)+1 ≤ (2:ℝ)^s := by
    induction s with
    | zero => norm_num
    | succ s ih => rw [pow_succ]; push_cast; nlinarith
  calc
    _ ≤ ∑ s∈Finset.range N, 2*(1/2:ℝ)^s := Finset.sum_le_sum fun s hs => by
      have hh := mul_le_mul_of_nonneg_right (hb s) (show 0 ≤ (1/4:ℝ)^s by positivity)
      rw [← mul_pow] at hh
      norm_num at hh
      nlinarith
    _ = 2*∑ s∈Finset.range N, (1/2:ℝ)^s := by rw [Finset.mul_sum]
    _ ≤ 4 := by
      have hh := sum_geometric_two_le N
      norm_num only [one_div] at *
      linarith
lemma cancellationWeight_eq_indicator (k : ℝ) (s : ℕ) :
    cancellationWeight k s={z | torusCancellation k s z}.indicator (fun _ => 2*(s:ℝ)+2) := by
  funext z
  simp only [cancellationWeight,Set.indicator_apply,Set.mem_ofPred_eq]
lemma integrable_cancellationWeight (k : ℝ) (s : ℕ) : Integrable (cancellationWeight k s) area := by
  rw [cancellationWeight_eq_indicator]
  exact (integrable_const _).indicator (isClosed_torusCancellation k s).measurableSet
lemma integral_cancellationWeight (k : ℝ) (s : ℕ) :
    (∫ z,cancellationWeight k s z ∂area)=(2*(s:ℝ)+2)*area.real {z | torusCancellation k s z} := by
  rw [cancellationWeight_eq_indicator,integral_indicator (isClosed_torusCancellation k s).measurableSet]
  simp [mul_comm]
lemma integral_cancellationWeight_le (k : ℝ) (C : ℝ) (hC : 0 ≤ C) (s : ℕ)
    (hc : area {z | torusCancellation k s z} ≤ ENNReal.ofReal (C*(1/4:ℝ)^s)) :
    (∫ z,cancellationWeight k s z ∂area) ≤ C*((2*(s:ℝ)+2)*(1/4:ℝ)^s) := by
  rw [integral_cancellationWeight]
  have hr : area.real {z | torusCancellation k s z} ≤ C*(1/4:ℝ)^s := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
    rwa [ENNReal.toReal_ofReal (by positivity)] at hh
  have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*(s:ℝ)+2 by positivity)
  nlinarith
lemma integral_cancellationLoss_le (k : ℝ) (hk : 0 ≤ k) (n : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ s : ℕ, area {z | torusCancellation k s z} ≤ ENNReal.ofReal (C*(1/4:ℝ)^s)) :
    (∫ z,cancellationLoss k z n ∂area) ≤
      10000000000*(1+∫ z,wingDefect k z n ∂area)+4*C := by
  have hD : Integrable (fun z => wingDefect k z n) area :=
    (continuous_wingDefect k hk n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hl : Integrable (fun z => cancellationLoss k z n) area :=
    (continuous_cancellationLoss k hk n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hw : Integrable (fun z => ∑ s∈Finset.range (n+1), cancellationWeight k s z) area :=
    integrable_finsetSum _ (fun s hs => integrable_cancellationWeight k s)
  have ht : Integrable (fun z => 10000000000*(1+wingDefect k z n)) area :=
    ((integrable_const 1).add hD).const_mul _
  have hb (z : Torus) : cancellationLoss k z n ≤ 10000000000*(1+wingDefect k z n)+∑ s∈Finset.range (n+1),cancellationWeight k s z :=
    cancellationLoss_pointwise_bound k hk z n
  have hh := integral_mono hl (ht.add hw) hb
  have hsum : (∫ z,10000000000*(1+wingDefect k z n)+∑ s∈Finset.range (n+1),cancellationWeight k s z ∂area)=
      (∫ z,10000000000*(1+wingDefect k z n) ∂area)+(∫ z,∑ s∈Finset.range (n+1),cancellationWeight k s z ∂area) := by
    convert! integral_add ht hw using 1
    all_goals try with_reducible_and_instances rfl
  have hDint : (∫ z,10000000000*(1+wingDefect k z n) ∂area)=10000000000*(1+∫ z,wingDefect k z n ∂area) := by
    rw [integral_const_mul]
    have he : (∫ z,1+wingDefect k z n ∂area)=1+∫ z,wingDefect k z n ∂area := by
      calc
        _ = (∫ _z : Torus,(1:ℝ) ∂area)+(∫ z,wingDefect k z n ∂area) := by
          convert! integral_add (integrable_const (1:ℝ)) hD using 1
          all_goals try with_reducible_and_instances rfl
        _ = _ := by simp
    rw [he]
  have hwint : (∫ z,∑ s∈Finset.range (n+1),cancellationWeight k s z ∂area)=∑ s∈Finset.range (n+1),∫ z,cancellationWeight k s z ∂area := by
    convert! integral_finsetSum (Finset.range (n+1)) (fun s hs => integrable_cancellationWeight k s) using 1
    all_goals try with_reducible_and_instances rfl
  simp only [Pi.add_apply] at hh
  rw [hsum,hDint,hwint] at hh
  have hsumbd : (∑ s∈Finset.range (n+1),∫ z,cancellationWeight k s z ∂area) ≤ 4*C := by
    calc
      _ ≤ ∑ s∈Finset.range (n+1),C*((2*(s:ℝ)+2)*(1/4:ℝ)^s) :=
        Finset.sum_le_sum fun s hs => integral_cancellationWeight_le k C hC s (hc s)
      _ = C*∑ s∈Finset.range (n+1),(2*(s:ℝ)+2)*(1/4:ℝ)^s := by rw [Finset.mul_sum]
      _ ≤ 4*C := by nlinarith [mul_le_mul_of_nonneg_left (cancellation_weight_sum (n+1)) hC]
  linarith
lemma eventually_meanDeficit_doubling_q44_oai :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0<k → M₀ ≤ growthBase k → ∀ n : ℕ, 0<n →
      meanDeficit k n ≤ meanDeficit k (n+n) ∧
      meanDeficit k (n+n) ≤ doublingConstant*meanDeficit k n+doublingConstant/(n:ℝ) := by
  obtain ⟨M₀,hM⟩ := eventually_cancellation_area
  refine ⟨M₀,?_⟩
  intro k hk hMk n hn
  refine ⟨meanDeficit_doubling_mono k hk.le n hn,?_⟩
  have hb := integral_cancellationLoss_le k hk.le n cancellationConstant cancellationConstant_pos.le (hM k hk hMk)
  have hD := integral_wingDefect_le k hk.le n hn
  rw [integral_cancellationLoss k hk.le n hn] at hb
  have he := (meanDeficit_bounds k hk.le n hn).1
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hc := cancellationConstant_pos
  unfold doublingConstant
  have hn0 : (0:ℝ)<n := by positivity
  apply (mul_le_mul_iff_right₀ hn0).mp
  rw [mul_add,mul_div_cancel₀ _ hn0.ne']
  have hx : 0 ≤ cancellationConstant*meanDeficit k n*(n:ℝ) := by positivity
  nlinarith
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.eventually_meanDeficit_doubling_q44_oai := @OAI.StandardMapEntropy.eventually_meanDeficit_doubling_q44_oai
