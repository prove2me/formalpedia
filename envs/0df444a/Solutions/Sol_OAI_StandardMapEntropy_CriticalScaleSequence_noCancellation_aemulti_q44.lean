-- Prove2me | solution 1 for OAI.StandardMapEntropy.CriticalScaleSequence.noCancellation_aemulti_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:28:57.119335+00:00
-- url     : https://prove2.me/submissions/6e5ebcc3-fe8f-4325-b1d9-7d2626dfc2bc

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

lemma tendsto_growthBase : Filter.Tendsto growthBase Filter.atTop Filter.atTop := by
  have h : Filter.Tendsto (fun k : ℝ => (2 * Real.pi) * k) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) Filter.tendsto_id
  exact Filter.tendsto_atTop_mono (fun k => by dsimp [growthBase]; linarith) h

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
lemma parameter_tendsto : Tendsto S.parameter atTop atTop :=
  tendsto_atTop_mono S.large tendsto_natCast_atTop_atTop
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayGrid
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
lemma nat_le_two_power (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : 1 ≤ (2:ℕ)^n := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      omega
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
end CriticalScaleSequence
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
lemma isOpen_arrayCancellation (s t : DyadicTime) : IsOpen {d | arrayCancellation s t d} :=
  (isOpen_lt continuous_const (continuous_arrayEval s (dyadicMid s t))).inter
    ((isOpen_lt continuous_const (continuous_arrayEval (dyadicMid s t) t)).inter
      (isOpen_lt (continuous_arrayEval s t) continuous_const))
lemma sample_cancellation (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) (hn : 0<n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ))
    (he : arrayCancellation s t (sampleArray k hk z n hn)) :
    torusCancellation k m (torusIter k (a+(m:ℤ)) z) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hmid : (n:ℝ)*(dyadicMid s t:ℝ)=((a+(m:ℤ):ℤ):ℝ) := by
    rw [dyadicMid_val]; push_cast; nlinarith
  have ht' : (n:ℝ)*(t:ℝ)=((a+(m:ℤ)+(m:ℤ):ℤ):ℝ) := by push_cast; linarith
  change _ < rescaledDistance k z n s (dyadicMid s t) ∧
    _ < rescaledDistance k z n (dyadicMid s t) t ∧ rescaledDistance k z n s t<_ at he
  rw [rescaledDistance_aligned _ _ _ _ _ _ _ hs hmid,
    rescaledDistance_aligned _ _ _ _ _ _ _ hmid ht',
    rescaledDistance_aligned _ _ _ _ _ _ _ hs ht'] at he
  rw [torusCancellation_iff_distance k hk]
  simp only [productDistance_shift,zero_add]
  rw [show -(m:ℤ)+(a+(m:ℤ))=a by ring,show (m:ℤ)+(a+(m:ℤ))=a+(m:ℤ)+(m:ℤ) by ring,
    productDistance_symm k z (a+(m:ℤ)) a]
  have h1 := (lt_div_iff₀ hnR).mp he.1
  have h2 := (lt_div_iff₀ hnR).mp he.2.1
  have h3 := (div_lt_iff₀ hnR).mp he.2.2
  have heq : ((t:ℝ)-(s:ℝ))*(n:ℝ)=2*(m:ℝ) := by nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith
lemma quarter_pow_le_inv (m : ℕ) (hm : 0 < m) : (1/4:ℝ)^m ≤ 1/(m:ℝ) := by
  have hpow : (m:ℝ) ≤ (4:ℝ)^m := by
    have hh : (m:ℝ) ≤ (2:ℝ)^m := by exact_mod_cast nat_le_two_power m
    exact hh.trans (pow_le_pow_left₀ (by norm_num) (by norm_num) m)
  have he : (4:ℝ)^m*(1/4:ℝ)^m=1 := by rw [←mul_pow]; norm_num
  apply (le_div_iff₀ (by exact_mod_cast hm : (0:ℝ)< m)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hpow (show 0≤(1/4:ℝ)^m by positivity)]
lemma integral_le_event_bound {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hi : Integrable f μ) (B : ℝ) (_hB : 0≤B) (hfb : ∀ x,f x≤B)
    (E : Set X) (hE : MeasurableSet E) (hz : ∀ x∉E,f x=0) :
    (∫ x,f x ∂μ) ≤ B*(μ E).toReal := by
  have hdom : ∀ x,f x≤E.indicator (fun _ => B) x := by
    intro x
    by_cases hx : x∈E
    · simpa only [indicator_of_mem hx] using hfb x
    · simp only [indicator_of_notMem hx,hz x hx,le_refl]
  have hh := integral_mono hi ((integrable_const B).indicator hE) hdom
  rw [integral_indicator hE,integral_const,smul_eq_mul] at hh
  simpa only [Measure.real,Measure.restrict_apply_univ,mul_comm] using hh
lemma integral_sample_cancellation_bound (k : ℝ) (hk : 0≤k)
    (C : ℝ) (hC : 0≤C) (hc : ∀ m : ℕ,area {z | torusCancellation k m z}≤ENNReal.ofReal (C*(1/4:ℝ)^m))
    (n : ℕ) (hn : 0<n) (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ))
    (F : DistanceArray → ℝ) (hF : Continuous F) (B : ℝ) (hB : 0≤B) (hFB : ∀ d,F d≤B)
    (hz : ∀ d,¬arrayCancellation s t d → F d=0) :
    (∫ d,F d ∂sampleLaw k hk n hn) ≤ B*C/(m:ℝ) := by
  rw [integral_sampleLaw k hk n hn F hF]
  let E : Set Torus := {z | torusCancellation k m (torusIter k (a+(m:ℤ)) z)}
  have hE : MeasurableSet E := (isClosed_torusCancellation k m).measurableSet.preimage
    (continuous_torusIter k _).measurable
  have hzero : ∀ z∉E,F (sampleArray k hk z n hn)=0 := by
    intro z hz'
    apply hz
    intro hh
    exact hz' (sample_cancellation k hk z n hn s t a m hs ht hh)
  have hbound := integral_le_event_bound area _
    ((hF.comp (continuous_sampleArray k hk n hn)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    B hB (fun z => hFB _) E hE hzero
  have hme : area E=area {z | torusCancellation k m z} :=
    (measurePreserving_torusIter k _).measure_preimage (isClosed_torusCancellation k m).measurableSet.nullMeasurableSet
  rw [hme] at hbound
  have he := ENNReal.toReal_mono (by finiteness) (hc m)
  rw [ENNReal.toReal_ofReal (by positivity)] at he
  have hh := mul_le_mul_of_nonneg_left he hB
  have hpow := mul_le_mul_of_nonneg_left (quarter_pow_le_inv m hm) (mul_nonneg hB hC)
  calc
    _ ≤ _ := hbound
    _ ≤ B*(C*(1/4:ℝ)^m) := hh
    _ ≤ B*C/(m:ℝ) := by simpa only [mul_assoc,div_eq_mul_inv,one_mul] using hpow
lemma sum_scaled_inverse (m l : ℕ) (hm : 0 < m) :
    (∑ j∈Finset.range l,1/((m*2^j:ℕ):ℝ)) ≤ 2/(m:ℝ) := by
  have he (j : ℕ) : 1/((m*2^j:ℕ):ℝ)=(1/(m:ℝ))*(1/2:ℝ)^j := by push_cast; rw [div_pow]; ring
  simp_rw [he]
  rw [←Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (sum_geometric_two_le l) (by positivity : 0≤1/(m:ℝ))
  norm_num only [one_div] at *
  simpa only [mul_comm,div_eq_mul_inv] using hh
lemma integral_scale_cancellation_bound (k : ℝ) (hk : 0≤k)
    (C : ℝ) (hC : 0≤C) (hc : ∀ m : ℕ,area {z | torusCancellation k m z}≤ENNReal.ofReal (C*(1/4:ℝ)^m))
    (p l : ℕ) (ε : ℝ) (hε : 0<ε) (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ)) (ht : ((2^p:ℕ):ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ))
    (F : DistanceArray → ℝ) (hF : Continuous F) (B : ℝ) (hB : 0≤B) (hFB : ∀ d,F d≤B)
    (hz : ∀ d,¬arrayCancellation s t d → F d=0) :
    (∫ d,F d ∂scaleLaw k hk p l ε) ≤ 2*B*C/((m:ℝ)*ε) := by
  rw [integral_scaleLaw k hk p l ε hε F hF]
  apply (div_le_iff₀ hε).mpr
  have hsum : (∑ j∈Finset.range l,∫ d,F d ∂sampleLaw k hk (2^(p+j)) (by positivity)) ≤
      B*C*∑ j∈Finset.range l,1/((m*2^j:ℕ):ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hs',ht'⟩ := aligned_times_scale p j s t a m hs ht
    simpa only [div_eq_mul_inv,one_mul] using integral_sample_cancellation_bound k hk C hC hc _ (by positivity)
      s t _ _ (by positivity) hs' ht' F hF B hB hFB hz
  have hh := hsum.trans (mul_le_mul_of_nonneg_left (sum_scaled_inverse m l hm) (mul_nonneg hB hC))
  apply hh.trans_eq
  field_simp
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
lemma cancellation_integral_tendsto (p l : ℕ → ℕ)
    (hp : ∀ i, criticalLowerExponent S.offset i ≤ p i)
    (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ))
    (F : DistanceArray → ℝ) (hF : Continuous F) (hF0 : ∀ d,0≤F d)
    (B : ℝ) (hB : 0≤B) (hFB : ∀ d,F d≤B)
    (hz : ∀ d,¬arrayCancellation s t d → F d=0) :
    Tendsto (fun i => ∫ d,F d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (l i) (S.epsilon i)) atTop (𝓝 0) := by
  obtain ⟨p₀,hp₀⟩ := dyadic_interval_aligned_eventually s t hst
  obtain ⟨M₀,hM₀⟩ := eventually_cancellation_area
  have hM : ∀ᶠ i in atTop,M₀≤growthBase (S.parameter i) :=
    (tendsto_growthBase.comp S.parameter_tendsto).eventually_ge_atTop M₀
  have hp' : Tendsto p atTop atTop := tendsto_atTop_mono hp S.lowerExponent_tendsto
  apply squeeze_zero' (Eventually.of_forall (fun i => integral_nonneg hF0))
  · filter_upwards [hp'.eventually_ge_atTop p₀,hM] with i hi hMi
    obtain ⟨a,m,hm,hs,ht⟩ := hp₀ _ hi
    have hb := integral_scale_cancellation_bound (S.parameter i) (S.positive i).le cancellationConstant
      cancellationConstant_pos.le (hM₀ _ (S.positive i) hMi) (p i) (l i) (S.epsilon i) (S.epsilon_pos i)
      s t a m hm hs ht F hF B hB hFB hz
    have hlen : ((2^(p i):ℕ):ℝ)*((t:ℝ)-(s:ℝ))=2*(m:ℝ) := by nlinarith
    have he : 2*B*cancellationConstant/((m:ℝ)*S.epsilon i)=
        (4*B*cancellationConstant/((t:ℝ)-(s:ℝ)))*(1/(((2^(p i):ℕ):ℝ)*S.epsilon i)) := by
      have hmR : (m:ℝ)=((2^(p i):ℕ):ℝ)*((t:ℝ)-(s:ℝ))/2 := by linarith
      rw [hmR]
      field_simp
      ring
    exact hb.trans (he.le.trans (mul_le_mul_of_nonneg_left (S.inverse_scale_epsilon_bound i _ (hp i))
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) cancellationConstant_pos.le) (sub_pos.mpr hst).le)))
  · simpa only [mul_zero] using (criticalTheta_tendsto S.offset).const_mul (4*B*cancellationConstant/((t:ℝ)-(s:ℝ)))
lemma cancellation_vague_tendsto (p l : ℕ → ℕ)
    (hp : ∀ i, criticalLowerExponent S.offset i ≤ p i)
    (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) (g : C_c(NonAffineArray,ℝ))
    (hg : ∀ d,0≤g d) (hz : ∀ d : NonAffineArray,¬arrayCancellation s t d.val → g d=0) :
    Tendsto (fun i => ∫ d,g d ∂nonaffinePart (scaleLaw (S.parameter i) (S.positive i).le (p i) (l i) (S.epsilon i))) atTop (𝓝 0) := by
  let F := arrayTestExtend g
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn F.continuous.continuousOn
  have hF0 : ∀ d,0≤F d := by
    intro d
    by_cases hd : d∈affineLocus
    · rw [show F d=0 from arrayTestExtend_affine g d hd]
    · exact (arrayTestExtend_apply g ⟨d,hd⟩).symm ▸ hg ⟨d,hd⟩
  have hFB : ∀ d,F d≤ max B 0 := by
    intro d
    have hdb : |F d| ≤ B := by convert! hB d (mem_univ d) using 1
    exact (le_abs_self _).trans (hdb.trans (le_max_left _ _))
  have hFz : ∀ d,¬arrayCancellation s t d → F d=0 := by
    intro d hd
    by_cases ha : d∈affineLocus
    · exact arrayTestExtend_affine g d ha
    · exact (arrayTestExtend_apply g ⟨d,ha⟩).trans (hz ⟨d,ha⟩ hd)
  have hh := S.cancellation_integral_tendsto p l hp s t hst F F.continuous hF0 (max B 0) (le_max_right _ _) hFB hFz
  simpa only [F,integral_arrayTestExtend] using hh
lemma cancellation_null_multi (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) :
    L.multi {d | arrayCancellation s t d.val}=0 := by
  apply vague_open_null L.filter (fun i => nonaffinePart (S.multiLaw i)) L.multi L.multi_converges
    ((isOpen_arrayCancellation s t).preimage continuous_subtype_val)
  intro g hg hz
  exact (S.cancellation_vague_tendsto (criticalLowerExponent S.offset)
    (fun i => S.exponent i-criticalLowerExponent S.offset i) (fun i => le_rfl) s t hst g hg hz).mono_left L.refines
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RealCancellation
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
lemma realArray_noFastCancellation (d : DistanceArray) (hu : UnitArray d)
    (hn : ∀ s t : DyadicTime,(s:ℝ)<(t:ℝ) → ¬arrayCancellation s t d) :
    NoFastCancellation (realArray d) (1/100000000) := by
  have hc := continuous_realArray d hu
  let R : ℝ → ℝ → Prop := fun x y => ¬(x<y ∧
    (1-1/100000000:ℝ)*(y-x)/2 < realArray d x ((x+y)/2) ∧
    (1-1/100000000:ℝ)*(y-x)/2 < realArray d ((x+y)/2) y ∧
    realArray d x y<(1/100000000:ℝ)*(y-x)/2)
  have hcl : IsClosed {p : ℝ×ℝ | R p.1 p.2} := by
    apply IsOpen.isClosed_compl
    exact (isOpen_lt continuous_fst continuous_snd).inter
      ((isOpen_lt (continuous_const.mul (continuous_snd.sub continuous_fst) |>.div_const 2)
        (hc.comp (continuous_fst.prodMk ((continuous_fst.add continuous_snd).div_const 2)))).inter
        ((isOpen_lt (continuous_const.mul (continuous_snd.sub continuous_fst) |>.div_const 2)
          (hc.comp (((continuous_fst.add continuous_snd).div_const 2).prodMk continuous_snd))).inter
          (isOpen_lt hc (continuous_const.mul (continuous_snd.sub continuous_fst) |>.div_const 2))))
  have hdy : ∀ s t : DyadicTime,R s t := by
    intro s t he
    apply hn s t he.1
    simpa only [arrayCancellation,←realArray_coe d hu,dyadicMid_val] using he.2
  have hall := isClosed_property2 (p := R) dyadicTime_dense hcl hdy
  intro z t ht he
  have hh := hall (z-t) (z+t)
  apply hh
  refine ⟨by linarith,?_⟩
  have hm : (z-t+(z+t))/2=z := by ring
  have hl : (z+t-(z-t))/2=t := by ring
  rw [hm]
  rcases he with ⟨he1,he2,he3⟩
  constructor
  · nlinarith
  constructor <;> nlinarith
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma noCancellation_aemulti_q44_oai : ∀ᵐ d ∂L.multi,NoFastCancellation (realArray d.val) (1/100000000) := by
  have hh (s t : DyadicTime) : ∀ᵐ d ∂L.multi,(s:ℝ)<(t:ℝ) → ¬arrayCancellation s t d.val := by
    by_cases hst : (s:ℝ)<(t:ℝ)
    · have he : ∀ᵐ d ∂L.multi,¬arrayCancellation s t d.val := ae_iff.mpr (by simpa using S.cancellation_null_multi L s t hst)
      filter_upwards [he] with d hd
      exact fun _ => hd
    · exact Eventually.of_forall fun d h => (hst h).elim
  filter_upwards [S.unit_aemulti L,ae_all_iff.mpr (fun s => ae_all_iff.mpr (hh s))] with d hu hn
  exact realArray_noFastCancellation d.val hu hn
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.CriticalScaleSequence.noCancellation_aemulti_q44_oai := @OAI.StandardMapEntropy.CriticalScaleSequence.noCancellation_aemulti_q44_oai
