-- Prove2me | solution 1 for OAI.StandardMapEntropy.exists_reversibleRectangleBlock_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:40:38.496602+00:00
-- url     : https://prove2.me/submissions/40f608cb-f7a2-4cdd-9412-49f6b443d210

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002

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
lemma wedge_add_right (z w a : ℂ) : wedge z (w+a) = wedge z w + wedge z a := by
  simp [wedge]; ring
lemma wedge_smul_right (t : ℝ) (z w : ℂ) : wedge z (t • w) = t*wedge z w := by
  simp [wedge]; ring
lemma wedge_refl (z : ℂ) : wedge z z = 0 := by dsimp [wedge]; ring
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

lemma transferStepInv_norm (v : ℝ) : ‖transferStepInv v‖ ≤ |v|+1 := by
  rw [← (transferStep_area v).norm_inverse (transferStepInv_area v) (transferStep_inv v) (transferStepInv_inv v)]
  exact transferStep_norm v

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
-- module Solutions.OAIQ44_CM.StandardMap_BridgeLinear
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
lemma wedge_quarterTurn_both (a b : ℂ) : wedge (quarterTurn a) (quarterTurn b)=wedge a b := by
  simp [wedge,quarterTurn]
  ring
lemma wedge_chain_bound (s : ℕ → ℂ) (e : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hu : ∀ i, a ≤ i → i ≤ b → ‖s i‖=1)
    (he : ∀ i, a ≤ i → i < b → |wedge (s i) (s (i+1))| ≤ e i) :
    |wedge (s a) (s b)| ≤ ∑ i ∈ Finset.Ico a b, e i := by
  induction b,hab using Nat.le_induction with
  | base => simp [wedge_refl]
  | succ b hab ih =>
    have hh:=ih (fun i hai hib => hu i hai (by omega)) (fun i hai hib => he i hai (by omega))
    have ht:=wedge_sine_triangle (s a) (s b) (s (b+1)) (hu a le_rfl (by omega))
      (hu b hab (by omega)) (hu (b+1) (by omega) le_rfl)
    rw [Finset.sum_Ico_succ_top hab]
    exact ht.trans (add_le_add hh (he b hab (by omega)))

lemma stable_direction_step {A B : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A)
    (a b : ℂ) (ha : ‖a‖=1) (_hb : ‖b‖=1)
    (hAa : ‖A a‖=‖A‖) (hBb : ‖B (quarterTurn b)‖=‖B‖⁻¹)
    (M : ℝ) (hB : 0 < ‖B‖) (hstep : ∀ z, ‖A z‖ ≤ M*‖B z‖) :
    |wedge (quarterTurn a) (quarterTurn b)| ≤ M/(‖A‖*‖B‖) := by
  have hpos : 0 < ‖A‖ := lt_of_lt_of_le zero_lt_one hA.singular_pair.choose_spec.2.2.2.2
  have hp:=expanded_projection_bound hA a ha hAa (quarterTurn b)
  rw [dot_quarterTurn_right] at hp
  have hs:=hstep (quarterTurn b)
  rw [hBb] at hs
  rw [wedge_quarterTurn_both]
  apply (le_div_iff₀ (mul_pos hpos hB)).mpr
  rw [abs_neg] at hp
  have hh := mul_le_mul_of_nonneg_right (hp.trans hs) hB.le
  calc
    _ = (‖A‖*|wedge a b|)*‖B‖ := by ring
    _  ≤  (M*‖B‖⁻¹)*‖B‖ := hh
    _ = M := by field_simp

lemma stable_prefix_finite_bound (A : ℕ → ℂ →L[ℝ] ℂ) (a : ℕ → ℂ)
    (D : ℕ → ℝ) (M : ℝ) (l B : ℕ) (hl : 1 ≤ l) (hlB : l ≤ B)
    (harea : ∀ i, 1 ≤ i → i ≤ B → PlaneAreaPreserving (A i))
    (hunit : ∀ i, 1 ≤ i → i ≤ B → ‖a i‖=1)
    (hnorm : ∀ i, 1 ≤ i → i ≤ B → ‖A i‖=D i)
    (hmax : ∀ i, 1 ≤ i → i ≤ B → ‖A i (a i)‖=D i)
    (hstable : ∀ i, 1 ≤ i → i ≤ B → ‖A i (quarterTurn (a i))‖=(D i)⁻¹)
    (hstep : ∀ i, 1 ≤ i → i < B → ∀ z, ‖A i z‖ ≤ M*‖A (i+1) z‖) :
    ‖A l (quarterTurn (a B))‖ ≤ (D l)⁻¹+D l*∑ i ∈ Finset.Ico l B, M/(D i*D (i+1)) := by
  have hpos (i : ℕ) (hi : 1 ≤ i) (hiB : i ≤ B) : 0 < ‖A i‖ :=
    lt_of_lt_of_le zero_lt_one (harea i hi hiB).singular_pair.choose_spec.2.2.2.2
  have hchain:=wedge_chain_bound (fun i => quarterTurn (a i))
    (fun i => M/(D i*D (i+1))) l B hlB
    (fun i hli hiB => by rw [norm_quarterTurn]; exact hunit i (by omega) hiB)
    (by
      intro i hli hiB
      have hh:=stable_direction_step (harea i (by omega) (by omega)) (a i) (a (i+1))
        (hunit i (by omega) (by omega)) (hunit (i+1) (by omega) (by omega))
        (by rw [hmax i (by omega) (by omega),hnorm i (by omega) (by omega)])
        (by rw [hstable (i+1) (by omega) (by omega),hnorm (i+1) (by omega) (by omega)])
        M (hpos (i+1) (by omega) (by omega)) (hstep i (by omega) hiB)
      simpa only [hnorm i (by omega) (by omega),hnorm (i+1) (by omega) (by omega)] using hh)
  rw [wedge_quarterTurn_both] at hchain
  have hup:=two_singular_upper (harea l hl hlB) (a l) (hunit l hl hlB)
    (by rw [hmax l hl hlB,hnorm l hl hlB]) (quarterTurn (a B))
  rw [dot_quarterTurn_right,abs_neg,hnorm l hl hlB] at hup
  have hw:=abs_wedge_le_norm_mul (a l) (quarterTurn (a B))
  rw [norm_quarterTurn,hunit l hl hlB,hunit B (by omega) le_rfl,mul_one] at hw
  have hD : 0 ≤ D l := by rw [← hnorm l hl hlB]; exact norm_nonneg _
  calc
    _  ≤  D l*|wedge (a l) (a B)|+(D l)⁻¹*|wedge (a l) (quarterTurn (a B))| := hup
    _  ≤  D l*(∑ i ∈ Finset.Ico l B, M/(D i*D (i+1)))+(D l)⁻¹*1 :=
      add_le_add (mul_le_mul_of_nonneg_left hchain hD) (mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hD))
    _ = _ := by ring
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
-- module Solutions.OAIQ44_CM.StandardMap_GridPartition
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma circleRep_coe_of_mem {x:ℝ} (hx:x∈Ico (0:ℝ) 1) : circleRep (x:Circle)=x := by
  rw [circleRep_coe,Int.fract_eq_self.mpr hx]
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
lemma norm_comp_planeSwap (A : ℂ →L[ℝ] ℂ) : ‖A.comp planeSwap‖=‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    simpa only [ContinuousLinearMap.comp_apply,norm_planeSwap] using A.le_opNorm (planeSwap z)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    simpa only [ContinuousLinearMap.comp_apply,planeSwap_invol,norm_planeSwap] using
      (A.comp planeSwap).le_opNorm (planeSwap z)
lemma norm_planeSwap_comp (A : ℂ →L[ℝ] ℂ) : ‖planeSwap.comp A‖=‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    simpa only [ContinuousLinearMap.comp_apply,norm_planeSwap] using A.le_opNorm z
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    simpa only [ContinuousLinearMap.comp_apply,norm_planeSwap] using (planeSwap.comp A).le_opNorm z
lemma planeSwap_transferStep (v : ℝ) (z : ℂ) :
    planeSwap (transferStep v (planeSwap z))=transferStepInv v z := by apply Complex.ext <;> rfl
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
lemma torusSegmentTransfer_reverse_norm (k : ℝ) (z : Torus) (n : ℕ) :
    ‖torusSegmentTransfer k z.swap 0 n‖=‖torusSegmentTransfer k z (-(n:ℤ)) n‖ := by
  let A := torusSegmentTransfer k z (-(n:ℤ)) n
  let B := (planeSwap.comp (torusSegmentTransfer k z.swap 0 n)).comp planeSwap
  have hAB : ∀ u, A (B u)=u := torusSegmentTransfer_reverse_identity k z n
  have he : B=transferProductInv (torusSegmentCoefficient k z (-(n:ℤ))) n := by
    ext u
    apply (show Function.Injective A from fun x y hxy => by
      have := congrArg (transferProductInv (torusSegmentCoefficient k z (-(n:ℤ))) n) hxy
      simpa only [A,torusSegmentTransfer,transferProductInv_inverse] using this)
    rw [hAB]
    exact (transferProduct_inverse _ _ _).symm
  have hnorm : ‖B‖=‖torusSegmentTransfer k z.swap 0 n‖ := by
    dsimp only [B]
    rw [norm_comp_planeSwap,norm_planeSwap_comp]
  rw [← hnorm,he,← transferProduct_norm_inverse]
  rfl
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
lemma torusPotential_bound (k : ℝ) (hk : 0 ≤ k) (x : Circle) : |torusPotential k x|+1 ≤ growthBase k := by
  obtain ⟨t,rfl⟩ := Quotient.mk_surjective x
  exact potential_bound k t hk
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_Definitions
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma standardDerivativeProduct_zero (k : ℝ) (z : Torus) :
    standardDerivativeProduct k z 0 = ContinuousLinearMap.id ℝ ℂ := rfl

attribute [local instance] OAI.StandardMapEntropy.realTangentCompTriple
lemma standardDerivativeProduct_succ (k : ℝ) (z : Torus) (n : ℕ) :
    standardDerivativeProduct k z (n + 1) =
      (standardDerivative k ((standardMap k)^[n] z)).comp
        (standardDerivativeProduct k z n) := rfl

end StandardMapEntropy
end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_Subadditive
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace BoundedSubadditive

variable {X : Type*}

lemma excess_nonneg (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    0 ≤ excess T h δ n x := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

lemma excess_succ_mono (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    excess T h δ n x ≤ excess T h δ (n + 1) x := by
  induction n generalizing x with
  | zero => exact excess_nonneg T h δ 1 x
  | succ n ih =>
    exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

lemma excess_mono (T : X → X) (h : X → ℝ) (δ : ℝ) (x : X) :
    Monotone (fun n => excess T h δ n x) :=
  monotone_nat_of_le_succ (fun n => excess_succ_mono T h δ n x)

lemma sum_sub_le_excess (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    birkhoffSum T h n x - (n : ℝ) * δ ≤ excess T h δ n x := by
  induction n generalizing x with
  | zero => simp [birkhoffSum, excess]
  | succ n ih =>
    rw [birkhoffSum_succ']
    have hm : h x - δ + excess T h δ n (T x) ≤ excess T h δ (n + 1) x :=
      le_max_right _ _
    have hi := ih (T x)
    push_cast
    linarith

lemma excess_account (T : X → X) (h : X → ℝ) (δ : ℝ)
    (hh : ∀ x, 0 ≤ h x) (n : ℕ) (x : X) :
    (if 0 < excess T h δ (n + 1) x then δ else 0) ≤
      h x + excess T h δ (n + 1) (T x) - excess T h δ (n + 1) x := by
  split_ifs with hp
  · have he : excess T h δ (n + 1) x = h x - δ + excess T h δ n (T x) := by
      apply max_eq_right
      change 0 < max 0 (h x - δ + excess T h δ n (T x)) at hp
      exact (lt_max_iff.mp hp).resolve_left (lt_irrefl 0) |>.le
    rw [he]
    linarith [excess_succ_mono T h δ n (T x)]
  · have he : excess T h δ (n + 1) x = 0 :=
      le_antisymm (not_lt.mp hp) (excess_nonneg T h δ _ x)
    rw [he]
    linarith [hh x, excess_nonneg T h δ (n + 1) (T x)]

section Measure
variable [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {T : X → X} {h : X → ℝ} {δ : ℝ}

lemma measurable_excess (hT : Measurable T) (hh : Measurable h) (n : ℕ) :
    Measurable (excess T h δ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max ((hh.sub measurable_const).add (ih.comp hT))

lemma integrable_excess (hT : MeasurePreserving T μ μ) (hh : Integrable h μ) (n : ℕ) :
    Integrable (excess T h δ n) μ := by
  induction n with
  | zero => exact integrable_const 0
  | succ n ih =>
    exact (integrable_const (0 : ℝ)).sup
      ((hh.sub (integrable_const δ)).add (hT.integrable_comp_of_integrable ih))

omit [IsFiniteMeasure μ] in
lemma integral_comp (hT : MeasurePreserving T μ μ) {g : X → ℝ}
    (hg : AEStronglyMeasurable g μ) : (∫ x, g (T x) ∂μ) = ∫ x, g x ∂μ := by
  have hg' : AEStronglyMeasurable g (Measure.map T μ) := by rwa [hT.map_eq]
  simpa only [hT.map_eq] using (integral_map hT.measurable.aemeasurable hg').symm

lemma excess_measure_bound (hT : MeasurePreserving T μ μ) (hm : Measurable h)
    (hi : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) (hδ : 0 < δ) (n : ℕ) :
    μ {x | 0 < excess T h δ n x} ≤ ENNReal.ofReal ((∫ x, h x ∂μ) / δ) := by
  cases n with
  | zero => simp [excess]
  | succ n =>
    let s : Set X := {x | 0 < excess T h δ (n + 1) x}
    have hs : MeasurableSet s := measurableSet_lt measurable_const
      (measurable_excess hT.measurable hm _)
    have he := integrable_excess (δ := δ) hT hi (n + 1)
    have heT : Integrable (fun x => excess T h δ (n + 1) (T x)) μ :=
      hT.integrable_comp_of_integrable he
    have hb : (∫ x, s.indicator (fun _ => δ) x ∂μ) ≤
        ∫ x, h x + excess T h δ (n + 1) (T x) - excess T h δ (n + 1) x ∂μ := by
      apply integral_mono ((integrable_const δ).indicator hs)
        ((hi.add heT).sub he)
      intro x
      simpa only [Set.indicator, s, Set.mem_ofPred_eq, Pi.sub_apply, Pi.add_apply, Function.comp_apply] using excess_account T h δ h0 n x
    have hsub := integral_sub (hi.add heT) he
    have hadd := integral_add hi heT
    simp only [Pi.add_apply] at hsub hadd
    rw [integral_indicator_const δ hs, hsub, hadd,
      integral_comp hT he.aestronglyMeasurable] at hb
    have hb' : μ.real s ≤ (∫ x, h x ∂μ) / δ := by
      apply (le_div_iff₀ hδ).mpr
      simpa only [smul_eq_mul, add_sub_cancel_right] using hb
    calc
      μ s = ENNReal.ofReal (μ.real s) := (ENNReal.ofReal_toReal (measure_ne_top μ s)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hb'

lemma maximal_measure_bound (hT : MeasurePreserving T μ μ) (hm : Measurable h)
    (hi : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) (hδ : 0 < δ) :
    μ {x | ∃ n : ℕ, (n : ℝ) * δ < birkhoffSum T h n x} ≤
      ENNReal.ofReal ((∫ x, h x ∂μ) / δ) := by
  have hsub : {x | ∃ n : ℕ, (n : ℝ) * δ < birkhoffSum T h n x} ⊆
      ⋃ n : ℕ, {x | 0 < excess T h δ n x} := by
    rintro x ⟨n, hn⟩
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    exact lt_of_lt_of_le (sub_pos.mpr hn) (sum_sub_le_excess T h δ n x)
  refine (measure_mono hsub).trans ?_
  have hm' : Monotone (fun n : ℕ => {x | 0 < excess T h δ n x}) := by
    intro m n hmn x hx
    exact lt_of_lt_of_le hx (excess_mono T h δ x hmn)
  rw [hm'.measure_iUnion]
  exact iSup_le (fun n => excess_measure_bound hT hm hi h0 hδ n)

end Measure

namespace Cocycle
variable [MeasurableSpace X] {T : X → X} (f : Cocycle X T)

lemma average_bounds (n : ℕ) (x : X) : 0 ≤ f.average n x ∧ f.average n x ≤ 1 := by
  refine ⟨div_nonneg (f.nonneg n x) (Nat.cast_nonneg n), ?_⟩
  by_cases hn : n = 0
  · simp [average, hn]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr (f.le_time n x)

lemma average_bdd_above (x : X) : IsBoundedUnder (· ≤ ·) atTop (fun n => f.average n x) :=
  isBoundedUnder_of ⟨1, fun n => (f.average_bounds n x).2⟩

lemma average_bdd_below (x : X) : IsBoundedUnder (· ≥ ·) atTop (fun n => f.average n x) :=
  isBoundedUnder_of ⟨0, fun n => (f.average_bounds n x).1⟩

lemma lowerRate_bounds (x : X) : 0 ≤ f.lowerRate x ∧ f.lowerRate x ≤ 1 := by
  constructor
  · exact le_liminf_of_le (f.average_bdd_above x).isCoboundedUnder_ge
      (Eventually.of_forall fun n => (f.average_bounds n x).1)
  · have hh := liminf_le_liminf (Eventually.of_forall fun n => (f.average_bounds n x).2)
      (f.average_bdd_below x) (isBoundedUnder_const.isCoboundedUnder_ge)
    simpa only [liminf_const, lowerRate] using hh

lemma measurable_average (n : ℕ) : Measurable (f.average n) :=
  (f.measurable n).div_const _

lemma measurable_lowerRate : Measurable f.lowerRate :=
  Measurable.liminf (fun n => f.measurable_average n)

lemma average_shift_bound (n : ℕ) (x : X) :
    |f.average n (T x) - f.average n x| ≤ 2 / (n : ℝ) := by
  rw [average, average, ← sub_div, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
  exact div_le_div_of_nonneg_right (f.shift_bound n x) (Nat.cast_nonneg n)

lemma lowerRate_shift (x : X) : f.lowerRate (T x) = f.lowerRate x := by
  have hc : Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have haux (a b : X) (hab : ∀ n, f.average n a - f.average n b ≤ 2 / (n : ℝ)) :
      f.lowerRate a ≤ f.lowerRate b := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have he : ∀ᶠ n : ℕ in atTop, f.average n a ≤ f.average n b + ε := by
      filter_upwards [hc.eventually (gt_mem_nhds hε)] with n hn
      linarith [hab n]
    have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => f.average n b + ε) :=
      isBoundedUnder_of ⟨1 + ε, fun n => add_le_add (f.average_bounds n b).2 le_rfl⟩
    have hh := liminf_le_liminf he (f.average_bdd_below a) hb.isCoboundedUnder_ge
    rw [liminf_add_const atTop (fun n => f.average n b) ε
      (f.average_bdd_above b).isCoboundedUnder_ge (f.average_bdd_below b)] at hh
    exact hh
  apply le_antisymm
  · exact haux (T x) x (fun n => (abs_le.mp (f.average_shift_bound n x)).2)
  · apply haux x (T x)
    intro n
    have hh := (abs_le.mp (f.average_shift_bound n x)).1
    linarith

lemma lowerRate_iterate (n : ℕ) (x : X) : f.lowerRate (T^[n] x) = f.lowerRate x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', f.lowerRate_shift, ih]

lemma measurableSet_badSet (ε : ℝ) (N : ℕ) : MeasurableSet (f.badSet ε N) := by
  apply MeasurableSet.compl
  apply MeasurableSet.biUnion (Set.to_countable _)
  intro n hn
  exact measurableSet_le (f.measurable n)
    (measurable_const.mul (f.measurable_lowerRate.add_const ε))

lemma measurable_badObservation (ε : ℝ) (N : ℕ) : Measurable (f.badObservation ε N) :=
  measurable_const.indicator (f.measurableSet_badSet ε N)

lemma badObservation_bounds (ε : ℝ) (N : ℕ) (x : X) :
    0 ≤ f.badObservation ε N x ∧ f.badObservation ε N x ≤ 1 := by
  classical
  by_cases hx : x ∈ f.badSet ε N <;> simp [badObservation, hx]

lemma exists_good_block (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ f.value n x ≤ (n : ℝ) * (f.lowerRate x + ε) := by
  have hh : ∃ᶠ n : ℕ in atTop, f.average n x < f.lowerRate x + ε :=
    frequently_lt_of_liminf_lt (f.average_bdd_above x).isCoboundedUnder_ge (lt_add_of_pos_right _ hε)
  obtain ⟨n, hn, he⟩ := frequently_atTop.mp hh 1
  have hn' : 0 < n := by omega
  refine ⟨n, hn', ?_⟩
  have hi := (div_lt_iff₀ (Nat.cast_pos.mpr hn')).mp he
  nlinarith

lemma badObservation_tendsto_zero (x : X) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => f.badObservation ε N x) atTop (𝓝 0) := by
  obtain ⟨n, hn, hg⟩ := f.exists_good_block x ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with N hN
  symm
  apply Set.indicator_of_notMem
  simp only [badSet, mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_not]
  exact ⟨n, ⟨hn, hN⟩, hg⟩

lemma birkhoff_bad_nonneg (ε : ℝ) (N n : ℕ) (x : X) :
    0 ≤ birkhoffSum T (f.badObservation ε N) n x := by
  exact Finset.sum_nonneg fun i hi => (f.badObservation_bounds ε N (T^[i] x)).1

lemma block_bound (ε : ℝ) (hε : 0 ≤ ε) (N n : ℕ) (x : X) :
    f.value n x ≤ (n : ℝ) * (f.lowerRate x + ε) +
      birkhoffSum T (f.badObservation ε N) n x + (N : ℝ) := by
  classical
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    have ha : 0 ≤ f.lowerRate x + ε := add_nonneg (f.lowerRate_bounds x).1 hε
    by_cases hn : n ≤ N
    · have hcast : (n : ℝ) ≤ N := by exact_mod_cast hn
      have hp := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) ha
      linarith [f.le_time n x, f.birkhoff_bad_nonneg ε N n x]
    · by_cases hx : x ∈ f.badSet ε N
      · have hn0 : 1 ≤ n := by omega
        have he : 1 + (n - 1) = n := by omega
        have hs := f.subadd 1 (n - 1) x
        simp only [he, Function.iterate_one] at hs
        have hi := ih (n - 1) (by omega) (T x)
        rw [f.lowerRate_shift] at hi
        rw [Nat.cast_sub hn0, Nat.cast_one, sub_mul, one_mul] at hi
        have hb : f.badObservation ε N x = 1 := by simp [badObservation, hx]
        have hsum : birkhoffSum T (f.badObservation ε N) n x =
            1 + birkhoffSum T (f.badObservation ε N) (n - 1) (T x) := by
          conv_lhs => rw [show n = (n - 1) + 1 by omega]
          rw [birkhoffSum_succ', hb]
        rw [hsum]
        have h1 := f.le_time 1 x
        norm_num only [Nat.cast_one] at h1
        linarith
      · have hg : x ∈ ⋃ m ∈ Set.Ioc 0 N,
            {y | f.value m y ≤ (m : ℝ) * (f.lowerRate y + ε)} := not_not.mp hx
        obtain ⟨m, hgm⟩ := mem_iUnion.mp hg
        obtain ⟨hm, hfm⟩ := mem_iUnion.mp hgm
        have hmn : m ≤ n := by have := hm.2; omega
        have he : m + (n - m) = n := Nat.add_sub_of_le hmn
        have hs := f.subadd m (n - m) x
        rw [he] at hs
        have hi := ih (n - m) (by have := hm.1; omega) (T^[m] x)
        rw [f.lowerRate_iterate, Nat.cast_sub hmn, sub_mul] at hi
        have hsum : birkhoffSum T (f.badObservation ε N) n x =
            birkhoffSum T (f.badObservation ε N) m x +
              birkhoffSum T (f.badObservation ε N) (n - m) (T^[m] x) := by
          simpa only [he] using birkhoffSum_add T (f.badObservation ε N) m (n - m) x
        rw [hsum]
        have hp := f.birkhoff_bad_nonneg ε N m x
        change f.value m x ≤ (m : ℝ) * (f.lowerRate x + ε) at hfm
        linarith

lemma upperRate_le_of_bad_averages (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) (δ : ℝ) (x : X)
    (hb : ∀ n, birkhoffSum T (f.badObservation ε N) n x ≤ (n : ℝ) * δ) :
    f.upperRate x ≤ f.lowerRate x + ε + δ := by
  apply le_of_forall_pos_le_add
  intro γ hγ
  have hc : Tendsto (fun n : ℕ => (N : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply limsup_le_of_le (f.average_bdd_below x).isCoboundedUnder_le
  filter_upwards [hc.eventually (gt_mem_nhds hγ), eventually_gt_atTop 0] with n hsmall hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hN := (div_lt_iff₀ hn').mp hsmall
  apply (div_le_iff₀ hn').mpr
  have hB := f.block_bound ε hε N n x
  have hbad := hb n
  nlinarith

section Measure
variable {μ : Measure X} [IsFiniteMeasure μ]

lemma integrable_badObservation (ε : ℝ) (N : ℕ) :
    Integrable (f.badObservation ε N) μ :=
  (integrable_const (1 : ℝ)).indicator (f.measurableSet_badSet ε N)

lemma integral_badObservation_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => ∫ x, f.badObservation ε N x ∂μ) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : X => (1 : ℝ))
    (fun N => (f.measurable_badObservation ε N).aestronglyMeasurable)
    (integrable_const 1)
    (fun N => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.badObservation_bounds ε N x).1]
      exact (f.badObservation_bounds ε N x).2)
    (Eventually.of_forall fun x => f.badObservation_tendsto_zero x ε hε)
  simpa only [integral_zero] using hh

lemma ae_upperRate_le_add (hT : MeasurePreserving T μ μ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ x ∂μ, f.upperRate x ≤ f.lowerRate x + 2 * ε := by
  let E : Set X := {x | f.lowerRate x + 2 * ε < f.upperRate x}
  have hbound (N : ℕ) : μ E ≤
      ENNReal.ofReal ((∫ x, f.badObservation ε N x ∂μ) / ε) := by
    have hsub : E ⊆ {x | ∃ n : ℕ, (n : ℝ) * ε < birkhoffSum T (f.badObservation ε N) n x} := by
      intro x hx
      by_contra hn
      change ¬ ∃ n : ℕ, (n : ℝ) * ε < birkhoffSum T (f.badObservation ε N) n x at hn
      push Not at hn
      have hh := f.upperRate_le_of_bad_averages ε hε.le N ε x hn
      change f.lowerRate x + 2 * ε < f.upperRate x at hx
      linarith
    exact (measure_mono hsub).trans
      (maximal_measure_bound hT (f.measurable_badObservation ε N)
        (f.integrable_badObservation ε N) (fun x => (f.badObservation_bounds ε N x).1) hε)
  have hc : Tendsto (fun N => ENNReal.ofReal ((∫ x, f.badObservation ε N x ∂μ) / ε))
      atTop (𝓝 0) := by
    have hh := (f.integral_badObservation_tendsto_zero (μ := μ) ε hε).div_const ε
    simpa only [Function.comp_def, zero_div, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  have hzero : μ E = 0 := le_antisymm (ge_of_tendsto' hc hbound) zero_le
  simpa only [ae_iff, not_le] using hzero

theorem ae_tendsto_average (hT : MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f.average n x) atTop (𝓝 (f.lowerRate x)) := by
  have ha : ∀ᵐ x ∂μ, ∀ j : ℕ, f.upperRate x ≤ f.lowerRate x + 2 * (1 / ((j : ℝ) + 1)) := by
    apply ae_all_iff.mpr
    intro j
    exact f.ae_upperRate_le_add hT _ (by positivity)
  filter_upwards [ha] with x hx
  have hc : Tendsto (fun j : ℕ => f.lowerRate x + 2 * (1 / ((j : ℝ) + 1)))
      atTop (𝓝 (f.lowerRate x)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hu : f.upperRate x ≤ f.lowerRate x := ge_of_tendsto' hc hx
  exact tendsto_of_le_liminf_of_limsup_le le_rfl hu
    (f.average_bdd_above x) (f.average_bdd_below x)

lemma integrable_lowerRate : Integrable f.lowerRate μ :=
  (integrable_const (1 : ℝ)).mono' f.measurable_lowerRate.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.lowerRate_bounds x).1]
      exact (f.lowerRate_bounds x).2)

end Measure
end Cocycle
end BoundedSubadditive

namespace StandardMapEntropy
open BoundedSubadditive

lemma lognorm_average_eq (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (z : Torus) :
    Real.log ‖torusSegmentTransfer k z 0 n‖ / (n : ℝ) =
      Real.log (growthBase k) * (transferCocycle k hk).average n z := by
  change _ = Real.log (growthBase k) * (productDistance k z 0 (n : ℤ) / (n : ℝ))
  have hf : productDistance k z 0 (n : ℤ) =
      Real.log ‖torusSegmentTransfer k z 0 n‖ / Real.log (growthBase k) := by
    simpa only [zero_add] using productDistance_forward k z 0 n
  rw [hf]
  have hlog := (log_growthBase_pos k hk).ne'
  calc
    _ = (Real.log (growthBase k) * (Real.log ‖torusSegmentTransfer k z 0 n‖ /
        Real.log (growthBase k))) / (n : ℝ) := by rw [mul_div_cancel₀ _ hlog]
    _ = _ := by ring

lemma transferLyapunov_limit (k : ℝ) (hk : 0 ≤ k) :
    TransferLimit k (transferLyapunov k hk) := by
  let f := transferCocycle k hk
  refine ⟨measurable_const.mul f.measurable_lowerRate,
    f.integrable_lowerRate.const_mul _, ?_, ?_, ?_⟩
  · intro z
    exact mul_nonneg (log_growthBase_pos k hk).le (f.lowerRate_bounds z).1
  · intro z
    exact congrArg (fun a => Real.log (growthBase k) * a) (f.lowerRate_shift z)
  · filter_upwards [f.ae_tendsto_average (measurePreserving_torusStep k)] with z hz
    have hh : Tendsto (fun n => Real.log (growthBase k) * f.average n z) atTop
        (𝓝 (Real.log (growthBase k) * f.lowerRate z)) := tendsto_const_nhds.mul hz
    simpa only [transferLyapunov, f, ← lognorm_average_eq] using hh

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_DerivativeGrowth
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

lemma tangentCoordinates_norm_le : ‖tangentCoordinates‖ ≤ 3 := by
  apply tangentCoordinates.opNorm_le_bound (by norm_num)
  intro z
  have hr := Complex.abs_re_le_norm z
  have hi := Complex.abs_im_le_norm z
  calc
    ‖tangentCoordinates z‖ ≤ |z.re| + |z.re-z.im| := by
      simpa only [tangentCoordinates_re, tangentCoordinates_im]
        using Complex.norm_le_abs_re_add_abs_im (tangentCoordinates z)
    _ ≤ |z.re| + (|z.re|+|z.im|) := add_le_add le_rfl (abs_sub _ _)
    _ ≤ 3*‖z‖ := by linarith

lemma standardDerivativeProduct_norm_ge_one (k : ℝ) (z : Torus) (n : ℕ) :
    1 ≤ ‖standardDerivativeProduct k z n‖ :=
  (standardDerivativeProduct_area k z n).singular_pair.choose_spec.2.2.2.2

lemma complexProjection_standardInverseLift (k : ℝ) (z : ℂ) :
    complexProjection (standardInverseLift k z) = inverseMap k (complexProjection z) := by
  ext <;> simp [complexProjection, standardInverseLift, inverseMap, kick,
    ← QuotientAddGroup.mk_sub]

lemma continuous_transferStepInv : Continuous transferStepInv := by
  have he : transferStepInv = fun v =>
      (transferStepInv 0).comp ((transferStep (-v)).comp (transferStepInv 0)) := by
    funext v
    apply ContinuousLinearMap.ext
    intro z
    apply Complex.ext <;> simp; ring
  rw [he]
  exact continuous_const.clm_comp ((continuous_transferStep.comp continuous_neg).clm_comp continuous_const)

lemma continuous_standardDerivative (k : ℝ) : Continuous (standardDerivative k) :=
  continuous_const.clm_comp
    ((continuous_transferStep.comp ((continuous_torusPotential k).comp continuous_fst)).clm_comp
      continuous_const)

lemma continuous_standardInverseDerivative (k : ℝ) : Continuous (standardInverseDerivative k) :=
  continuous_const.clm_comp
    ((continuous_transferStepInv.comp ((continuous_torusPotential k).comp
      (continuous_fst.comp (continuous_inverseMap k)))).clm_comp continuous_const)

lemma recurrenceCoordinates_iterate (k : ℝ) (n : ℕ) (z : Torus) :
    recurrenceCoordinates ((standardMap k)^[n] z) =
      (torusStep k)^[n] (recurrenceCoordinates z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', standardMap_conjugacy, ih]
    rfl

lemma standardDerivativeProduct_conjugate (k : ℝ) (z : Torus) (n : ℕ) :
    standardDerivativeProduct k z n = tangentCoordinates.comp
      ((torusSegmentTransfer k (recurrenceCoordinates z) 0 n).comp tangentCoordinates) := by
  induction n with
  | zero =>
    apply ContinuousLinearMap.ext
    intro w
    simpa only [standardDerivativeProduct_zero, torusSegmentTransfer, transferProduct,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      (tangentCoordinates_involutive w).symm
  | succ n ih =>
    have hcoeff : torusSegmentCoefficient k (recurrenceCoordinates z) 0 (n+1) =
        torusPotential k ((standardMap k)^[n] z).1 := by
      unfold torusSegmentCoefficient
      simp only [Nat.cast_add, Nat.cast_one, zero_add, add_sub_cancel_right]
      rw [torusIter_nat_apply, ← recurrenceCoordinates_iterate]
      rfl
    apply ContinuousLinearMap.ext
    intro w
    simp only [standardDerivativeProduct_succ, ih, standardDerivative, torusSegmentTransfer,
      transferProduct, ContinuousLinearMap.comp_apply, tangentCoordinates_involutive, hcoeff]

lemma conjugate_norm_le (A : ℂ →L[ℝ] ℂ) :
    ‖tangentCoordinates.comp (A.comp tangentCoordinates)‖ ≤ 9*‖A‖ := by
  calc
    _ ≤ ‖tangentCoordinates‖ * (‖A‖ * ‖tangentCoordinates‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 3 * (‖A‖ * 3) := by gcongr <;> exact tangentCoordinates_norm_le
    _ = _ := by ring

lemma conjugate_norm_lower (A : ℂ →L[ℝ] ℂ) :
    ‖A‖ ≤ 9*‖tangentCoordinates.comp (A.comp tangentCoordinates)‖ := by
  convert conjugate_norm_le (tangentCoordinates.comp (A.comp tangentCoordinates)) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply ContinuousLinearMap.ext
  intro z
  simp only [ContinuousLinearMap.comp_apply, tangentCoordinates_involutive]

lemma derivative_log_difference_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    |Real.log ‖standardDerivativeProduct k z n‖-
      Real.log ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖| ≤ Real.log 9 := by
  have hA : 0 < ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖ :=
    lt_of_lt_of_le zero_lt_one (torusSegmentTransfer_norm_bounds k hk _ _ _).1
  have hB : 0 < ‖standardDerivativeProduct k z n‖ :=
    lt_of_lt_of_le zero_lt_one (standardDerivativeProduct_norm_ge_one k z n)
  have h₁ := conjugate_norm_le (torusSegmentTransfer k (recurrenceCoordinates z) 0 n)
  have h₂ := conjugate_norm_lower (torusSegmentTransfer k (recurrenceCoordinates z) 0 n)
  rw [← standardDerivativeProduct_conjugate] at h₁ h₂
  have hlog₁ := Real.log_le_log hB h₁
  have hlog₂ := Real.log_le_log hA h₂
  rw [Real.log_mul (by norm_num) hA.ne'] at hlog₁
  rw [Real.log_mul (by norm_num) hB.ne'] at hlog₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end StandardMapEntropy

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

lemma complexProjection_iterate (k : ℝ) (n : ℕ) (z : ℂ) :
    complexProjection ((standardLift k)^[n] z) = (standardMap k)^[n] (complexProjection z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', complexProjection_standardLift, ih]

lemma derivative_rate_of_transfer_rate (k : ℝ) (hk : 0 ≤ k) (z : Torus) (l : ℝ)
    (hl : Tendsto
      (fun n : ℕ => Real.log ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖ / (n : ℝ))
      atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
      atTop (𝓝 l) := by
  have hd : Tendsto (fun n : ℕ =>
      (Real.log ‖standardDerivativeProduct k z n‖ -
        Real.log ‖torusSegmentTransfer k (recurrenceCoordinates z) 0 n‖) / (n : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => Real.log 9 / (n : ℝ)) atTop (𝓝 0))
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (derivative_log_difference_bound k hk z n) (Nat.cast_nonneg _)
  have hh := hd.add hl
  simpa only [sub_div, sub_add_cancel, zero_add] using hh

lemma measurable_recurrenceCoordinates : Measurable recurrenceCoordinates :=
  measurable_fst.prodMk (measurable_fst.sub measurable_snd)

lemma measurable_standardLyapunov (k : ℝ) (hk : 0 ≤ k) :
    Measurable (standardLyapunov k hk) :=
  (transferLyapunov_limit k hk).1.comp measurable_recurrenceCoordinates

lemma integrable_standardLyapunov (k : ℝ) (hk : 0 ≤ k) :
    Integrable (standardLyapunov k hk) area :=
  measurePreserving_recurrenceCoordinates.integrable_comp_of_integrable
    (transferLyapunov_limit k hk).2.1

lemma standardLyapunov_nonneg (k : ℝ) (hk : 0 ≤ k) (z : Torus) :
    0 ≤ standardLyapunov k hk z := (transferLyapunov_limit k hk).2.2.1 _

lemma standardLyapunov_invariant (k : ℝ) (hk : 0 ≤ k) (z : Torus) :
    standardLyapunov k hk (standardMap k z) = standardLyapunov k hk z := by
  unfold standardLyapunov
  rw [standardMap_conjugacy]
  exact (transferLyapunov_limit k hk).2.2.2.1 _

lemma ae_standardLyapunov_rate (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, Tendsto
      (fun n : ℕ => Real.log ‖standardDerivativeProduct k z n‖ / (n : ℝ))
      atTop (𝓝 (standardLyapunov k hk z)) := by
  have hh := measurePreserving_recurrenceCoordinates.quasiMeasurePreserving.ae
    (transferLyapunov_limit k hk).2.2.2.2
  filter_upwards [hh] with z hz
  exact derivative_rate_of_transfer_rate k hk z _ hz

end StandardMapEntropy

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma standardDerivative_norm_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) :
    ‖standardDerivative k z‖ ≤ 9*growthBase k := by
  calc
    _ ≤ 9*‖transferStep (torusPotential k z.1)‖ := conjugate_norm_le _
    _ ≤ 9*(|torusPotential k z.1|+1) :=
      mul_le_mul_of_nonneg_left (transferStep_norm _) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (torusPotential_bound k hk z.1) (by norm_num)

lemma standardDerivativeProduct_step_lower (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) (v : ℂ) :
    ‖standardDerivativeProduct k z n v‖ ≤
      (9*growthBase k)*‖standardDerivativeProduct k z (n+1) v‖ := by
  exact ((standardDerivative_area k ((standardMap k)^[n] z)).norm_lower
    (standardDerivativeProduct k z n v)).trans
    (mul_le_mul_of_nonneg_right (standardDerivative_norm_bound k hk _) (norm_nonneg _))

end StandardMapEntropy
end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_PlaneLyapunov
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Metric
open scoped Topology BigOperators

namespace PlaneLyapunov

variable (A : ℕ → ℂ →L[ℝ] ℂ)

lemma norm_pos (hA : ∀ n, PlaneAreaPreserving (A n)) (n : ℕ) : 0 < ‖A n‖ :=
  lt_of_lt_of_le zero_lt_one (hA n).singular_pair.choose_spec.2.2.2.2

lemma image_norm_pos (hA : ∀ n, PlaneAreaPreserving (A n)) {v : ℂ} (hv : v ≠ 0) (n : ℕ) :
    0 < ‖A n v‖ := by
  have hh := (hA n).norm_lower v
  by_contra h
  have hz : ‖A n v‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
  rw [hz, mul_zero] at hh
  exact (norm_pos_iff.mpr hv).not_ge hh

lemma eventual_exp_lower (hA : ∀ n, PlaneAreaPreserving (A n)) {l α : ℝ}
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l)) (hα : α < l) :
    ∀ᶠ n : ℕ in atTop, Real.exp (α*(n : ℝ)) ≤ ‖A n‖ := by
  filter_upwards [(tendsto_order.mp hl).1 α hα, eventually_gt_atTop 0] with n hn hn0
  have hp : (0 : ℝ) < n := by exact_mod_cast hn0
  calc
    _ ≤ Real.exp (Real.log ‖A n‖) := Real.exp_le_exp.mpr ((le_div_iff₀ hp).mp hn.le)
    _ = _ := Real.exp_log (norm_pos A hA n)

lemma tailConstant_pos {M α : ℝ} (hM : 0 < M) (hα : 0 < α) : 0 < tailConstant M α := by
  unfold tailConstant
  apply div_pos (mul_pos hM (Real.exp_pos _))
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))

lemma stable_error_exp_bound (D : ℕ → ℝ) (M α : ℝ) (hM : 0 ≤ M) (hα : 0 < α)
    (n B : ℕ) (_hnB : n ≤ B)
    (hD : ∀ i, n ≤ i → i ≤ B → Real.exp (α*(i : ℝ)) ≤ D i) :
    (∑ i ∈ Finset.Ico n B, M/(D i*D (i+1))) ≤
      tailConstant M α * Real.exp (-2*α*(n : ℝ)) := by
  have hq0 : 0 ≤ Real.exp (-2*α) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2*α) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he (i : ℕ) (hi : i ∈ Finset.Ico n B) :
      M/(D i*D (i+1)) ≤ M*Real.exp (-α)*(Real.exp (-2*α))^i := by
    have hi0 := (Finset.mem_Ico.mp hi).1
    have hiB := (Finset.mem_Ico.mp hi).2
    have hl := hD i hi0 hiB.le
    have hr := hD (i+1) (by omega) (by omega)
    have hp := mul_le_mul hl hr (Real.exp_pos _).le ((Real.exp_pos _).trans_le hl).le
    calc
      _ ≤ M/(Real.exp (α*(i : ℝ))*Real.exp (α*((i+1 : ℕ) : ℝ))) :=
        div_le_div_of_nonneg_left hM (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hp
      _ = _ := by
        rw [← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_nat_mul]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        push_cast
        ring
  calc
    _ ≤ ∑ i ∈ Finset.Ico n B, M*Real.exp (-α)*(Real.exp (-2*α))^i :=
      Finset.sum_le_sum he
    _ = (M*Real.exp (-α)) * ∑ i ∈ Finset.Ico n B, (Real.exp (-2*α))^i := by
      rw [Finset.mul_sum]
    _ ≤ (M*Real.exp (-α)) * ((Real.exp (-2*α))^n/(1-Real.exp (-2*α))) :=
      mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq0 hq1) (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul]
      unfold tailConstant
      rw [show (n : ℝ)*(-2*α) = -2*α*(n : ℝ) by ring]
      ring

lemma inverse_bound_by_exp (D α : ℝ) (n : ℕ) (hD : Real.exp (α*(n : ℝ)) ≤ D) :
    D⁻¹ ≤ D*Real.exp (-2*α*(n : ℝ)) := by
  have hp : 0 < D := (Real.exp_pos _).trans_le hD
  calc
    _ ≤ (Real.exp (α*(n : ℝ)))⁻¹ := (inv_le_inv₀ hp (Real.exp_pos _)).mpr hD
    _ = Real.exp (α*(n : ℝ))*Real.exp (-2*α*(n : ℝ)) := by
      rw [← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le

lemma exists_stable_bound (hA : ∀ n, PlaneAreaPreserving (A n))
    (M : ℝ) (hM : 0 < M)
    (hstep : ∀ n v, ‖A n v‖ ≤ M*‖A (n+1) v‖)
    {l : ℝ} (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l)) :
    ∃ s : ℂ, ‖s‖=1 ∧ ∀ α : ℝ, 0 < α → α < l →
      ∀ᶠ n : ℕ in atTop, ‖A n s‖ ≤
        ‖A n‖*(1+tailConstant M α)*Real.exp (-2*α*(n : ℝ)) := by
  classical
  choose a hau ham hao has hnorm using fun n => (hA n).singular_pair
  have hu (n : ℕ) : quarterTurn (a n) ∈ sphere (0 : ℂ) 1 := by
    simp only [mem_sphere, dist_zero_right, norm_quarterTurn, hau]
  obtain ⟨s, hs, φ, hφ, hlim⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq hu
  have hsunit : ‖s‖=1 := by simpa only [mem_sphere, dist_zero_right] using hs
  refine ⟨s, hsunit, ?_⟩
  intro α hα hαl
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventual_exp_lower A hA hl hαl)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hb : ‖A n s‖ ≤ ‖A n‖⁻¹ + ‖A n‖ *
      (tailConstant M α * Real.exp (-2*α*(n : ℝ))) := by
    apply le_of_tendsto ((A n).continuous.norm.tendsto s |>.comp hlim)
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop n)] with j hj
    have hh := stable_prefix_finite_bound A a (fun i => ‖A i‖) M n (φ j) hn1 hj
      (fun i _ _ => hA i) (fun i _ _ => hau i) (fun _ _ _ => rfl)
      (fun i _ _ => ham i) (fun i _ _ => has i) (fun i _ _ => hstep i)
    have ht := stable_error_exp_bound (fun i => ‖A i‖) M α hM.le hα n (φ j) hj
      (fun i hni _ => hN i (hnN.trans hni))
    exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ht (norm_nonneg _)))
  have hi := inverse_bound_by_exp ‖A n‖ α n (hN n hnN)
  calc
    _ ≤ ‖A n‖*Real.exp (-2*α*(n : ℝ)) +
        ‖A n‖*(tailConstant M α*Real.exp (-2*α*(n : ℝ))) := add_le_add hi le_rfl |>.trans' hb
    _ = _ := by ring

lemma stable_growth (hA : ∀ n, PlaneAreaPreserving (A n)) (M : ℝ) (hM : 0 < M)
    {l : ℝ} (hlpos : 0 < l)
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l))
    (s : ℂ) (hs : ‖s‖=1)
    (hbound : ∀ α : ℝ, 0 < α → α < l →
      ∀ᶠ n : ℕ in atTop, ‖A n s‖ ≤
        ‖A n‖*(1+tailConstant M α)*Real.exp (-2*α*(n : ℝ))) : Growth A s (-l) := by
  have hsne : s ≠ 0 := by intro h; simp [h] at hs
  have hlow (n : ℕ) : -Real.log ‖A n‖/(n : ℝ) ≤ Real.log ‖A n s‖/(n : ℝ) := by
    have hh := (hA n).norm_lower s
    rw [hs] at hh
    have hhlog := Real.log_le_log zero_lt_one hh
    rw [Real.log_one, Real.log_mul (norm_pos A hA n).ne'
      (image_norm_pos A hA hsne n).ne'] at hhlog
    apply div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  refine ⟨hsne, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro b hb
    have hh : Tendsto (fun n : ℕ => -Real.log ‖A n‖/(n : ℝ)) atTop (𝓝 (-l)) := by
      simpa only [neg_div] using hl.neg
    filter_upwards [(tendsto_order.mp hh).1 b hb] with n hn
    exact hn.trans_le (hlow n)
  · intro b hb
    have hc : max 0 ((l-b)/2) < l := max_lt hlpos (by linarith)
    obtain ⟨α, hαlo, hαhi⟩ := exists_between hc
    have hα : 0 < α := (le_max_left _ _).trans_lt hαlo
    have hαb : l-2*α < b := by
      have := (le_max_right 0 ((l-b)/2)).trans_lt hαlo
      linarith
    have hC : 0 < 1+tailConstant M α := by
      have := tailConstant_pos hM hα
      linarith
    have hu : Tendsto (fun n : ℕ =>
        Real.log ‖A n‖/(n : ℝ)+Real.log (1+tailConstant M α)/(n : ℝ)-2*α)
        atTop (𝓝 (l-2*α)) := by
      have hh := (hl.add (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => Real.log (1+tailConstant M α)/(n : ℝ)) atTop (𝓝 0))).sub
        (tendsto_const_nhds (x := 2*α))
      simpa only [add_zero] using hh
    filter_upwards [hbound α hα hαhi, (tendsto_order.mp hu).2 b hαb,
      eventually_gt_atTop 0] with n hn hnb hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hh := Real.log_le_log (image_norm_pos A hA hsne n) hn
    rw [Real.log_mul (mul_pos (norm_pos A hA n) hC).ne' (Real.exp_pos _).ne',
      Real.log_mul (norm_pos A hA n).ne' hC.ne', Real.log_exp] at hh
    have hdiv := div_le_div_of_nonneg_right hh hnpos.le
    have he : (Real.log ‖A n‖+Real.log (1+tailConstant M α)+ -2*α*(n : ℝ))/(n : ℝ) =
        Real.log ‖A n‖/(n : ℝ)+Real.log (1+tailConstant M α)/(n : ℝ)-2*α := by
      rw [add_div, add_div, mul_div_cancel_right₀ _ hnpos.ne']
      ring
    rw [he] at hdiv
    exact hdiv.trans_lt hnb

lemma growth_on_line (hA : ∀ n, PlaneAreaPreserving (A n))
    {s : ℂ} {l : ℝ} (hsunit : ‖s‖=1) (hs : Growth A s l)
    (v : ℂ) (hv : v ≠ 0) (halign : wedge s v=0) : Growth A v l := by
  have he : v = dot s v • s := by simpa only [halign, zero_smul, add_zero] using unit_expansion s v hsunit
  have hd : dot s v ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at he
    exact hv he
  have hc : Tendsto (fun n : ℕ => Real.log |dot s v|/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine ⟨hv, ?_⟩
  have hh := hc.add hs.2
  simp only [zero_add] at hh
  apply hh.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    conv_rhs => rw [he, map_smul, norm_smul, Real.norm_eq_abs,
      Real.log_mul (abs_pos.mpr hd).ne' (image_norm_pos A hA hs.1 n).ne', add_div]

lemma growth_off_line (hA : ∀ n, PlaneAreaPreserving (A n))
    {l : ℝ} (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖ / (n : ℝ)) atTop (𝓝 l))
    {s : ℂ} (hs : Growth A s (-l)) (v : ℂ) (hv : v ≠ 0) (hoff : wedge s v ≠ 0) :
    Growth A v l := by
  have hws : 0 < |wedge s v| := abs_pos.mpr hoff
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hlo : Tendsto (fun n : ℕ =>
      Real.log |wedge s v|/(n : ℝ)-Real.log ‖A n s‖/(n : ℝ)) atTop (𝓝 l) := by
    have hc : Tendsto (fun n : ℕ => Real.log |wedge s v|/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using hc.sub hs.2
  have hup : Tendsto (fun n : ℕ =>
      Real.log ‖A n‖/(n : ℝ)+Real.log ‖v‖/(n : ℝ)) atTop (𝓝 l) := by
    have hc : Tendsto (fun n : ℕ => Real.log ‖v‖/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using hl.add hc
  refine ⟨hv, tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup ?_ ?_⟩
  · intro n
    have hh := abs_wedge_le_norm_mul (A n s) (A n v)
    rw [hA n] at hh
    have hhlog := Real.log_le_log hws hh
    rw [Real.log_mul (image_norm_pos A hA hs.1 n).ne' (image_norm_pos A hA hv n).ne'] at hhlog
    have hsub : Real.log |wedge s v|-Real.log ‖A n s‖ ≤ Real.log ‖A n v‖ := by linarith
    simpa only [sub_div] using div_le_div_of_nonneg_right hsub (Nat.cast_nonneg n)
  · intro n
    have hh := Real.log_le_log (image_norm_pos A hA hv n) ((A n).le_opNorm v)
    rw [Real.log_mul (norm_pos A hA n).ne' hvpos.ne'] at hh
    simpa only [add_div] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg n)

end PlaneLyapunov
end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_HyperbolicSet
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter BoundedSubadditive
open scoped Topology ENNReal

lemma measurePreserving_torusSwap : MeasurePreserving (Prod.swap : Torus → Torus) area area :=
  Measure.measurePreserving_swap

lemma torusIter_neg_nat_apply (k : ℝ) (n : ℕ) (z : Torus) :
    torusIter k (-(n : ℤ)) z = (torusStep k).symm^[n] z := by
  simp only [torusIter, zpow_neg, zpow_natCast, ← inv_pow,
    Equiv.Perm.inv_def, Equiv.Perm.coe_pow]

lemma transfer_lowerRate_inverse_iterate (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (z : Torus) :
    (transferCocycle k hk).lowerRate (torusIter k (-(n : ℤ)) z) =
      (transferCocycle k hk).lowerRate z := by
  have hi (w : Torus) : (transferCocycle k hk).lowerRate ((torusStep k).symm w) =
      (transferCocycle k hk).lowerRate w := by
    simpa only [Equiv.apply_symm_apply] using
      ((transferCocycle k hk).lowerRate_shift ((torusStep k).symm w)).symm
  rw [torusIter_neg_nat_apply]
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', hi, ih]

lemma transfer_average_reverse (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (z : Torus) :
    (transferCocycle k hk).average n z.swap =
      (transferCocycle k hk).average n (torusIter k (-(n : ℤ)) z) := by
  apply mul_left_cancel₀ (log_growthBase_pos k hk).ne'
  rw [← lognorm_average_eq, ← lognorm_average_eq]
  rw [torusSegmentTransfer_shift, zero_add, torusSegmentTransfer_reverse_norm]

lemma transfer_lowerRate_swap_ae (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, (transferCocycle k hk).lowerRate z.swap =
      (transferCocycle k hk).lowerRate z := by
  let f := transferCocycle k hk
  have hconv := f.ae_tendsto_average (measurePreserving_torusStep k)
  have hconvSwap := measurePreserving_torusSwap.quasiMeasurePreserving.ae hconv
  have hbound (n : ℕ) (z : Torus) : |f.average n z - f.lowerRate z| ≤ 1 := by
    rcases f.average_bounds n z with ⟨h0,h1⟩
    rcases f.lowerRate_bounds z with ⟨l0,l1⟩
    exact abs_le.mpr (by constructor <;> linarith)
  have hboundSwap (n : ℕ) (z : Torus) : |f.average n z.swap - f.lowerRate z| ≤ 1 := by
    rcases f.average_bounds n z.swap with ⟨h0,h1⟩
    rcases f.lowerRate_bounds z with ⟨l0,l1⟩
    exact abs_le.mpr (by constructor <;> linarith)
  have hlim : Tendsto (fun n => ∫ z, |f.average n z - f.lowerRate z| ∂area)
      atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := area) (fun _ : Torus => (1 : ℝ))
      (F := fun n z => |f.average n z-f.lowerRate z|) (f := fun _ => (0 : ℝ))
      (fun n => ((f.measurable_average n).sub f.measurable_lowerRate).abs.aestronglyMeasurable)
      (integrable_const 1)
      (fun n => Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_abs]; exact hbound n z) ?_
    · simpa only [integral_zero] using hh
    · filter_upwards [hconv] with z hz
      simpa only [sub_self, abs_zero] using (hz.sub (tendsto_const_nhds (x := f.lowerRate z))).abs
  have hlimSwap : Tendsto
      (fun n => ∫ z, |f.average n z.swap - f.lowerRate z| ∂area) atTop
      (𝓝 (∫ z, |f.lowerRate z.swap - f.lowerRate z| ∂area)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Torus => (1 : ℝ))
      (fun n => (((f.measurable_average n).comp measurable_swap).sub
        f.measurable_lowerRate).abs.aestronglyMeasurable) (integrable_const 1)
      (fun n => Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_abs]; exact hboundSwap n z)
    filter_upwards [hconvSwap] with z hz
    exact (hz.sub (tendsto_const_nhds (x := f.lowerRate z))).abs
  have heq (n : ℕ) : (∫ z, |f.average n z.swap-f.lowerRate z| ∂area) =
      ∫ z, |f.average n z-f.lowerRate z| ∂area := by
    calc
      _ = ∫ z, |f.average n (torusIter k (-(n : ℤ)) z)-
          f.lowerRate (torusIter k (-(n : ℤ)) z)| ∂area := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          dsimp only
          rw [show f.average n z.swap = f.average n (torusIter k (-(n : ℤ)) z) from
            transfer_average_reverse k hk n z,
            show f.lowerRate (torusIter k (-(n : ℤ)) z) = f.lowerRate z from
            transfer_lowerRate_inverse_iterate k hk n z]
      _ = _ := integral_torusIter k (-(n : ℤ)) (fun z => |f.average n z-f.lowerRate z|)
  have hzero : (∫ z, |f.lowerRate z.swap-f.lowerRate z| ∂area) = 0 :=
    tendsto_nhds_unique hlimSwap (hlim.congr (fun n => (heq n).symm))
  have hint : Integrable (fun z => |f.lowerRate z.swap-f.lowerRate z|) area :=
    ((measurePreserving_torusSwap.integrable_comp_of_integrable f.integrable_lowerRate).sub
      f.integrable_lowerRate).abs
  have h := (integral_eq_zero_iff_of_nonneg (fun z => abs_nonneg _) hint).mp hzero
  filter_upwards [h] with z hz
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

lemma transferLyapunov_swap_ae (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, transferLyapunov k hk z.swap = transferLyapunov k hk z := by
  filter_upwards [transfer_lowerRate_swap_ae k hk] with z hz
  exact congrArg (fun t => Real.log (growthBase k)*t) hz

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_InverseLyapunov
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma standardReversal_inverseMap (k : ℝ) (z : Torus) :
    standardReversal (inverseMap k z) = standardMap k (standardReversal z) := by
  apply Prod.ext
  · simp only [standardReversal_fst, standardReversal_snd, inverseMap, standardMap, kick]
    abel
  · simp only [standardReversal_snd, inverseMap, standardMap, standardReversal_fst, kick]
    abel

lemma standardReversal_inverse_iterate (k : ℝ) (n : ℕ) (z : Torus) :
    standardReversal ((inverseMap k)^[n] z) = (standardMap k)^[n] (standardReversal z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', standardReversal_inverseMap, ih,
        Function.iterate_succ_apply']

lemma measurePreserving_standardReversal : MeasurePreserving standardReversal area area :=
  measurePreserving_recurrenceCoordinates.comp
    (measurePreserving_torusSwap.comp measurePreserving_recurrenceCoordinates)

lemma standardInverseDerivative_conjugate (k : ℝ) (z : Torus) :
    standardInverseDerivative k z = tangentReversal.comp
      ((standardDerivative k (standardReversal z)).comp tangentReversal) := by
  apply ContinuousLinearMap.ext
  intro w
  change tangentCoordinates (transferStepInv _ (tangentCoordinates w)) = _
  have hc : (inverseMap k z).1 = (standardReversal z).1 := rfl
  rw [hc]
  simp only [standardDerivative, tangentReversal, ContinuousLinearMap.comp_apply,
    tangentCoordinates_involutive, planeSwap_transferStep]

lemma standardInverseDerivativeProduct_conjugate (k : ℝ) (z : Torus) (n : ℕ) :
    standardInverseDerivativeProduct k z n = tangentReversal.comp
      ((standardDerivativeProduct k (standardReversal z) n).comp tangentReversal) := by
  induction n with
  | zero =>
    apply ContinuousLinearMap.ext
    intro w
    exact (tangentReversal_involutive w).symm
  | succ n ih =>
    apply ContinuousLinearMap.ext
    intro w
    simp only [standardInverseDerivativeProduct, ih, standardInverseDerivative_conjugate,
      ContinuousLinearMap.comp_apply, tangentReversal_involutive, standardDerivativeProduct,
      standardReversal_inverse_iterate]

lemma complexProjection_inverse_iterate (k : ℝ) (n : ℕ) (z : ℂ) :
    complexProjection ((standardInverseLift k)^[n] z) = (inverseMap k)^[n] (complexProjection z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      complexProjection_standardInverseLift, ih]

lemma tangentReversal_conjugate_norm_le (A : ℂ →L[ℝ] ℂ) :
    ‖tangentReversal.comp (A.comp tangentReversal)‖ ≤ 81*‖A‖ := by
  have he : tangentReversal.comp (A.comp tangentReversal) =
      tangentCoordinates.comp ((planeSwap.comp
        ((tangentCoordinates.comp (A.comp tangentCoordinates)).comp planeSwap)).comp
        tangentCoordinates) := by
    ext w
    rfl
  rw [he]
  calc
    _ ≤ 9*‖planeSwap.comp ((tangentCoordinates.comp (A.comp tangentCoordinates)).comp planeSwap)‖ :=
      conjugate_norm_le _
    _ = 9*‖tangentCoordinates.comp (A.comp tangentCoordinates)‖ := by
      rw [norm_planeSwap_comp, norm_comp_planeSwap]
    _ ≤ 9*(9*‖A‖) := mul_le_mul_of_nonneg_left (conjugate_norm_le A) (by norm_num)
    _ = _ := by ring

lemma inverse_derivative_log_difference_bound (k : ℝ) (z : Torus) (n : ℕ) :
    |Real.log ‖standardInverseDerivativeProduct k z n‖-
      Real.log ‖standardDerivativeProduct k (standardReversal z) n‖| ≤ Real.log 81 := by
  let A := standardDerivativeProduct k (standardReversal z) n
  let B := standardInverseDerivativeProduct k z n
  have hA : 0 < ‖A‖ := lt_of_lt_of_le zero_lt_one (standardDerivativeProduct_norm_ge_one k _ n)
  have hB : 0 < ‖B‖ := lt_of_lt_of_le zero_lt_one
    (standardInverseDerivativeProduct_area k z n).singular_pair.choose_spec.2.2.2.2
  have h1 : ‖B‖ ≤ 81*‖A‖ := by
    dsimp only [B, A]
    rw [standardInverseDerivativeProduct_conjugate]
    exact tangentReversal_conjugate_norm_le _
  have h2 : ‖A‖ ≤ 81*‖B‖ := by
    convert tangentReversal_conjugate_norm_le B using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext w
    simp only [B, standardInverseDerivativeProduct_conjugate,
      ContinuousLinearMap.comp_apply, tangentReversal_involutive]
    rfl
  have hl1 := Real.log_le_log hB h1
  have hl2 := Real.log_le_log hA h2
  rw [Real.log_mul (by norm_num) hA.ne'] at hl1
  rw [Real.log_mul (by norm_num) hB.ne'] at hl2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma standardLyapunov_reversal_ae (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, standardLyapunov k hk (standardReversal z) = standardLyapunov k hk z := by
  have hh := measurePreserving_recurrenceCoordinates.quasiMeasurePreserving.ae
    (transferLyapunov_swap_ae k hk)
  filter_upwards [hh] with z hz
  change transferLyapunov k hk
    (recurrenceCoordinates (recurrenceCoordinates (recurrenceCoordinates z).swap)) = _
  rw [recurrenceCoordinates_involutive]
  exact hz

lemma ae_standardInverseLyapunov_rate (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, Tendsto
      (fun n : ℕ => Real.log ‖standardInverseDerivativeProduct k z n‖ / (n : ℝ))
      atTop (𝓝 (standardLyapunov k hk z)) := by
  have hh := measurePreserving_standardReversal.quasiMeasurePreserving.ae
    (ae_standardLyapunov_rate k hk)
  filter_upwards [hh, standardLyapunov_reversal_ae k hk] with z hz heq
  have hd : Tendsto (fun n : ℕ =>
      (Real.log ‖standardInverseDerivativeProduct k z n‖-
        Real.log ‖standardDerivativeProduct k (standardReversal z) n‖)/(n : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => Real.log 81/(n : ℝ)) atTop (𝓝 0))
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (inverse_derivative_log_difference_bound k z n) (Nat.cast_nonneg _)
  rw [heq] at hz
  simpa only [sub_div, sub_add_cancel, zero_add] using hd.add hz

lemma standardInverseDerivative_norm_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) :
    ‖standardInverseDerivative k z‖ ≤ 9*growthBase k := by
  calc
    _ ≤ 9*‖transferStepInv (torusPotential k (inverseMap k z).1)‖ := conjugate_norm_le _
    _ ≤ 9*(|torusPotential k (inverseMap k z).1|+1) :=
      mul_le_mul_of_nonneg_left (transferStepInv_norm _) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (torusPotential_bound k hk _) (by norm_num)

lemma standardInverseDerivativeProduct_step_lower (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) (v : ℂ) :
    ‖standardInverseDerivativeProduct k z n v‖ ≤
      (9*growthBase k)*‖standardInverseDerivativeProduct k z (n+1) v‖ := by
  exact ((standardInverseDerivative_area k ((inverseMap k)^[n] z)).norm_lower
    (standardInverseDerivativeProduct k z n v)).trans
    (mul_le_mul_of_nonneg_right (standardInverseDerivative_norm_bound k hk _) (norm_nonneg _))

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

namespace PlaneLyapunov

lemma approxSlow_unit (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A) :
    ‖approxSlow A hA‖ = 1 := (denseUnit _).property

lemma approxSlow_bound (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A) :
    ‖A (approxSlow A hA)‖ < 2/‖A‖ := Nat.find_spec (exists_approx_slow A hA)

lemma measurable_approxSlow {X : Type*} [MeasurableSpace X]
    (A : X → ℂ →L[ℝ] ℂ) (hA : ∀ x, PlaneAreaPreserving (A x)) (hm : Measurable A) :
    Measurable (fun x => approxSlow (A x) (hA x)) := by
  classical
  unfold approxSlow
  apply Measurable.find (f := fun j (_ : X) => (denseUnit j).val) (fun j => measurable_const)
    (fun j => measurableSet_lt ?_ (measurable_const.div hm.norm))
    (fun x => exists_approx_slow (A x) (hA x))
  exact (((continuous_id.clm_apply continuous_const :
    Continuous (fun B : ℂ →L[ℝ] ℂ => B (denseUnit j))).measurable).comp hm).norm

lemma unit_sq {s : ℂ} (hs : ‖s‖ = 1) : s.re^2+s.im^2=1 := by
  have hh := Complex.sq_norm s
  rw [hs] at hh
  simpa only [Complex.normSq_apply, one_pow, pow_two, one_mul] using hh.symm

lemma unit_projection_difference {a b : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) :
    |a.re^2-b.re^2| ≤ |wedge a b| ∧
    |a.re*a.im-b.re*b.im| ≤ |wedge a b| := by
  have ha2 := unit_sq ha
  have hb2 := unit_sq hb
  have he1 : a.re^2-b.re^2 = wedge a b * dot a (planeSwap b) := by
    simp only [wedge, dot, planeSwap_re, planeSwap_im]
    linear_combination b.re^2*ha2-a.re^2*hb2
  have he2 : a.re*a.im-b.re*b.im = -wedge a b * dot a (star b) := by
    simp only [wedge, dot, Complex.star_def, Complex.conj_re, Complex.conj_im]
    linear_combination (b.re*b.im)*ha2-(a.re*a.im)*hb2
  have hd1 : |dot a (planeSwap b)| ≤ 1 := by
    simpa only [ha, norm_planeSwap, hb, one_mul] using abs_dot_le_norm_mul a (planeSwap b)
  have hd2 : |dot a (star b)| ≤ 1 := by
    simpa only [ha, norm_star, hb, one_mul] using abs_dot_le_norm_mul a (star b)
  rw [he1, he2, abs_mul, abs_mul, abs_neg]
  constructor <;> nlinarith [abs_nonneg (wedge a b)]

lemma norm_tendsto_zero_of_negative_growth (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) {v : ℂ} {l : ℝ}
    (hg : Growth A v l) (hl : l < 0) : Tendsto (fun n => ‖A n v‖) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => Real.exp ((l/2)*(n : ℝ))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact (tendsto_const_mul_atBot_of_neg (by linarith : l/2 < 0)).2 tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hp
  filter_upwards [(tendsto_order.mp hg.2).2 (l/2) (by linarith), eventually_gt_atTop 0] with n hn hn0
  have hnp : (0 : ℝ)<n := by exact_mod_cast hn0
  have hh := (div_lt_iff₀ hnp).mp hn
  calc
    _ = Real.exp (Real.log ‖A n v‖) := (Real.exp_log (image_norm_pos A hA hg.1 n)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hh.le

lemma approxSlow_wedge_tendsto_zero (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) {s : ℂ}
    (hs : Tendsto (fun n => ‖A n s‖) atTop (𝓝 0)) :
    Tendsto (fun n => wedge (approxSlow (A n) (hA n)) s) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_)
    (by simpa only [mul_zero] using (tendsto_const_nhds (x := (2 : ℝ))).mul hs)
  rw [Real.norm_eq_abs, ← hA n]
  calc
    _ ≤ ‖A n (approxSlow (A n) (hA n))‖*‖A n s‖ := abs_wedge_le_norm_mul _ _
    _ ≤ 2*‖A n s‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (approxSlow_bound (A n) (hA n)).le.trans
        (div_le_self (by norm_num) (hA n).singular_pair.choose_spec.2.2.2.2)

lemma approxSlow_projection_tendsto (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) {s : ℂ} (hunit : ‖s‖=1)
    (hs : Tendsto (fun n => ‖A n s‖) atTop (𝓝 0)) :
    Tendsto (fun n => (approxSlow (A n) (hA n)).re^2) atTop (𝓝 (s.re^2)) ∧
    Tendsto (fun n => (approxSlow (A n) (hA n)).re*(approxSlow (A n) (hA n)).im)
      atTop (𝓝 (s.re*s.im)) := by
  have hw := (approxSlow_wedge_tendsto_zero A hA hs).abs
  simp only [abs_zero] at hw
  constructor
  · have hd : Tendsto (fun n => (approxSlow (A n) (hA n)).re^2-s.re^2) atTop (𝓝 0) := by
      apply squeeze_zero_norm (fun n => ?_) hw
      rw [Real.norm_eq_abs]
      exact (unit_projection_difference (approxSlow_unit _ _) hunit).1
    have hh := hd.add (tendsto_const_nhds (x := s.re^2))
    rw [zero_add] at hh
    apply hh.congr'
    exact Eventually.of_forall fun n => by dsimp only; ring
  · have hd : Tendsto (fun n => (approxSlow (A n) (hA n)).re*
        (approxSlow (A n) (hA n)).im-s.re*s.im) atTop (𝓝 0) := by
      apply squeeze_zero_norm (fun n => ?_) hw
      rw [Real.norm_eq_abs]
      exact (unit_projection_difference (approxSlow_unit _ _) hunit).2
    simpa only [sub_add_cancel, zero_add] using hd.add (tendsto_const_nhds (x := s.re*s.im))

lemma stableCandidate_wedge (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) {s : ℂ} (hunit : ‖s‖=1)
    (hs : Tendsto (fun n => ‖A n s‖) atTop (𝓝 0)) : wedge s (stableCandidate A hA)=0 := by
  classical
  have hp := approxSlow_projection_tendsto A hA hunit hs
  unfold stableCandidate
  rw [hp.1.liminf_eq, hp.2.liminf_eq]
  dsimp only
  split_ifs with h
  · have hr : s.re=0 := sq_eq_zero_iff.mp h
    simp [wedge, hr]
  · simp only [wedge]
    ring

lemma measurable_stableCandidate {X : Type*} [MeasurableSpace X]
    (A : X → ℕ → ℂ →L[ℝ] ℂ) (hA : ∀ x n, PlaneAreaPreserving (A x n))
    (hm : ∀ n, Measurable (fun x => A x n)) :
    Measurable (fun x => stableCandidate (A x) (hA x)) := by
  classical
  have hslow (n) := measurable_approxSlow (fun x => A x n) (fun x => hA x n) (hm n)
  have hp : Measurable (fun x => liminf (fun n => (approxSlow (A x n) (hA x n)).re^2) atTop) :=
    Measurable.liminf fun n => (Complex.measurable_re.comp (hslow n)).pow_const 2
  have hq : Measurable (fun x => liminf (fun n =>
      (approxSlow (A x n) (hA x n)).re*(approxSlow (A x n) (hA x n)).im) atTop) :=
    Measurable.liminf fun n => (Complex.measurable_re.comp (hslow n)).mul
      (Complex.measurable_im.comp (hslow n))
  exact Measurable.ite (measurableSet_eq_fun hp measurable_const) measurable_const
    (Complex.equivRealProdCLM.symm.continuous.measurable.comp (hp.prodMk hq))

lemma measurable_stableUnit {X : Type*} [MeasurableSpace X]
    (A : X → ℕ → ℂ →L[ℝ] ℂ) (hA : ∀ x n, PlaneAreaPreserving (A x n))
    (hm : ∀ n, Measurable (fun x => A x n)) :
    Measurable (fun x => stableUnit (A x) (hA x)) := by
  have hh := measurable_stableCandidate A hA hm
  exact hh.norm.inv.smul hh

theorem stableUnit_growth (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n))
    (M : ℝ) (hM : 0<M) (hstep : ∀ n v, ‖A n v‖ ≤ M*‖A (n+1) v‖)
    {l : ℝ} (hpos : 0<l)
    (hl : Tendsto (fun n : ℕ => Real.log ‖A n‖/(n : ℝ)) atTop (𝓝 l)) :
    Growth A (stableUnit A hA) (-l) := by
  obtain ⟨s,hunit,hbound⟩ := exists_stable_bound A hA M hM hstep hl
  have hg := stable_growth A hA M hM hpos hl s hunit hbound
  have hz := norm_tendsto_zero_of_negative_growth A hA hg (by linarith)
  apply growth_on_line A hA hunit hg _
    (by intro hzero; have hh := norm_stableUnit A hA; rw [hzero, norm_zero] at hh; norm_num at hh)
  rw [stableUnit, wedge_smul_right, stableCandidate_wedge A hA hunit hz, mul_zero]

end PlaneLyapunov
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma continuous_standardDerivativeProduct (k : ℝ) (n : ℕ) :
    Continuous (fun z => standardDerivativeProduct k z n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact ((continuous_standardDerivative k).comp ((continuous_standardMap k).iterate n)).clm_comp ih

lemma continuous_standardInverseDerivativeProduct (k : ℝ) (n : ℕ) :
    Continuous (fun z => standardInverseDerivativeProduct k z n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact ((continuous_standardInverseDerivative k).comp ((continuous_inverseMap k).iterate n)).clm_comp ih

lemma measurable_stableVector (k : ℝ) : Measurable (stableVector k) :=
  PlaneLyapunov.measurable_stableUnit _ _ (fun n => (continuous_standardDerivativeProduct k n).measurable)
lemma measurable_unstableVector (k : ℝ) : Measurable (unstableVector k) :=
  PlaneLyapunov.measurable_stableUnit _ _ (fun n => (continuous_standardInverseDerivativeProduct k n).measurable)
lemma stableVector_ne_zero (k : ℝ) (z : Torus) : stableVector k z ≠ 0 := by
  intro hz; have hh := norm_stableVector k z; rw [hz, norm_zero] at hh; norm_num at hh
lemma unstableVector_ne_zero (k : ℝ) (z : Torus) : unstableVector k z ≠ 0 := by
  intro hz; have hh := norm_unstableVector k z; rw [hz, norm_zero] at hh; norm_num at hh

lemma ae_stableVector_growth (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      PlaneLyapunov.Growth (standardDerivativeProduct k z) (stableVector k z)
        (-standardLyapunov k hk z) := by
  filter_upwards [ae_standardLyapunov_rate k hk] with z hz hpos
  exact PlaneLyapunov.stableUnit_growth _ (standardDerivativeProduct_area k z)
    (9*growthBase k) (by have := growthBase_ge_four k hk; positivity)
    (standardDerivativeProduct_step_lower k hk z) hpos hz

lemma ae_unstableVector_growth (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      PlaneLyapunov.Growth (standardInverseDerivativeProduct k z) (unstableVector k z)
        (-standardLyapunov k hk z) := by
  filter_upwards [ae_standardInverseLyapunov_rate k hk] with z hz hpos
  exact PlaneLyapunov.stableUnit_growth _ (standardInverseDerivativeProduct_area k z)
    (9*growthBase k) (by have := growthBase_ge_four k hk; positivity)
    (standardInverseDerivativeProduct_step_lower k hk z) hpos hz

lemma standardInverseDerivative_standardDerivative (k : ℝ) (z : Torus) (v : ℂ) :
    standardInverseDerivative k (standardMap k z) (standardDerivative k z v)=v := by
  simp only [standardInverseDerivative, standardDerivative, ContinuousLinearMap.comp_apply,
    tangentCoordinates_involutive, inverseMap_standardMap, transferStepInv_inv]

lemma standardDerivativeProduct_shift (k : ℝ) (z : Torus) (n : ℕ) (v : ℂ) :
    standardDerivativeProduct k (standardMap k z) n (standardDerivative k z v) =
      standardDerivativeProduct k z (n+1) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [standardDerivativeProduct_succ, ContinuousLinearMap.comp_apply, ih,
      ← Function.iterate_succ_apply]

lemma standardInverseDerivativeProduct_shift (k : ℝ) (z : Torus) (n : ℕ) (v : ℂ) :
    standardInverseDerivativeProduct k (inverseMap k z) n (standardInverseDerivative k z v) =
      standardInverseDerivativeProduct k z (n+1) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [standardInverseDerivativeProduct, ContinuousLinearMap.comp_apply, ih,
      ← Function.iterate_succ_apply]

lemma standardInverseDerivativeProduct_forward (k : ℝ) (z : Torus) (n : ℕ) (v : ℂ) :
    standardInverseDerivativeProduct k (standardMap k z) (n+1) (standardDerivative k z v) =
      standardInverseDerivativeProduct k z n v := by
  rw [← standardInverseDerivativeProduct_shift, standardInverseDerivative_standardDerivative,
    inverseMap_standardMap]

lemma contracting_wedge_zero (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) {s t : ℂ}
    (hs : Tendsto (fun n => ‖A n s‖) atTop (𝓝 0))
    (ht : Tendsto (fun n => ‖A n t‖) atTop (𝓝 0)) : wedge s t=0 := by
  have hh : Tendsto (fun _ : ℕ => |wedge s t|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) (fun n => ?_)
      (by simpa only [mul_zero] using hs.mul ht)
    rw [← hA n]
    exact abs_wedge_le_norm_mul _ _
  exact abs_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hh)

lemma ae_stableVector_covariant (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (stableVector k (standardMap k z)) (standardDerivative k z (stableVector k z))=0 := by
  have hs := ae_stableVector_growth k hk
  filter_upwards [hs, (measurePreserving_standardMap k).quasiMeasurePreserving.ae hs] with z hz hnext hp
  have hn := hnext (by simpa only [standardLyapunov_invariant] using hp)
  have h0 := PlaneLyapunov.norm_tendsto_zero_of_negative_growth _
    (standardDerivativeProduct_area k z) (hz hp) (by linarith)
  have h1 := PlaneLyapunov.norm_tendsto_zero_of_negative_growth _
    (standardDerivativeProduct_area k (standardMap k z)) hn
    (by rw [standardLyapunov_invariant]; linarith)
  apply contracting_wedge_zero _ (standardDerivativeProduct_area k (standardMap k z)) h1
  convert h0.comp (tendsto_add_atTop_nat 1) using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact congrArg norm (standardDerivativeProduct_shift k z n (stableVector k z))

lemma ae_unstableVector_covariant (k : ℝ) (hk : 0 ≤ k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (unstableVector k (standardMap k z)) (standardDerivative k z (unstableVector k z))=0 := by
  have hs := ae_unstableVector_growth k hk
  filter_upwards [hs, (measurePreserving_standardMap k).quasiMeasurePreserving.ae hs] with z hz hnext hp
  have hn := hnext (by simpa only [standardLyapunov_invariant] using hp)
  have h0 := PlaneLyapunov.norm_tendsto_zero_of_negative_growth _
    (standardInverseDerivativeProduct_area k z) (hz hp) (by linarith)
  have h1 := PlaneLyapunov.norm_tendsto_zero_of_negative_growth _
    (standardInverseDerivativeProduct_area k (standardMap k z)) hn
    (by rw [standardLyapunov_invariant]; linarith)
  apply contracting_wedge_zero _ (standardInverseDerivativeProduct_area k (standardMap k z)) h1
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [standardInverseDerivativeProduct_forward] using h0

lemma unit_collinear_eq_smul {s v : ℂ} (hs : ‖s‖=1) (hw : wedge s v=0) :
    v = dot s v • s := by
  simpa only [hw, zero_smul, add_zero] using unit_expansion s v hs

lemma unit_collinear_dot_ne_zero {s v : ℂ} (hs : ‖s‖=1) (hw : wedge s v=0) (hv : v ≠ 0) :
    dot s v ≠ 0 := by
  intro h
  have hh := unit_collinear_eq_smul hs hw
  rw [h, zero_smul] at hh
  exact hv hh

lemma covariant_collinear_iff (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A)
    {s u t v : ℂ} (hs : s ≠ 0) (hu : u ≠ 0) (ht : ‖t‖=1) (hv : ‖v‖=1)
    (hst : wedge t (A s)=0) (huv : wedge v (A u)=0) :
    wedge s u=0 ↔ wedge t v=0 := by
  have hAs : A s ≠ 0 := by
    intro h; exact hs (by have hh := hA.norm_lower s; rw [h, norm_zero, mul_zero] at hh; exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  have hAu : A u ≠ 0 := by
    intro h; exact hu (by have hh := hA.norm_lower u; rw [h, norm_zero, mul_zero] at hh; exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  have hcs := unit_collinear_dot_ne_zero ht hst hAs
  have hcu := unit_collinear_dot_ne_zero hv huv hAu
  rw [← hA, unit_collinear_eq_smul ht hst, unit_collinear_eq_smul hv huv,
    wedge_smul_left, wedge_smul_right]
  simp only [mul_eq_zero, hcs, hcu, false_or]

lemma measurableSet_coincidentLines (k : ℝ) (hk : 0 ≤ k) :
    MeasurableSet (coincidentLines k hk) := by
  apply (measurableSet_lt measurable_const (measurable_standardLyapunov k hk)).inter
  apply measurableSet_eq_fun _ measurable_const
  exact ((Complex.measurable_re.comp (measurable_stableVector k)).mul
    (Complex.measurable_im.comp (measurable_unstableVector k))).sub
    ((Complex.measurable_im.comp (measurable_stableVector k)).mul
      (Complex.measurable_re.comp (measurable_unstableVector k)))

lemma preimage_coincidentLines_ae (k : ℝ) (hk : 0 ≤ k) :
    standardMap k ⁻¹' coincidentLines k hk =ᵐ[area] coincidentLines k hk := by
  filter_upwards [ae_stableVector_covariant k hk, ae_unstableVector_covariant k hk] with z hs hu
  change (0 < standardLyapunov k hk (standardMap k z) ∧
      wedge (stableVector k (standardMap k z)) (unstableVector k (standardMap k z))=0) =
    (0 < standardLyapunov k hk z ∧ wedge (stableVector k z) (unstableVector k z)=0)
  rw [standardLyapunov_invariant]
  by_cases hp : 0 < standardLyapunov k hk z
  · simp only [hp, true_and]
    exact propext (covariant_collinear_iff _ (standardDerivative_area k z)
      (stableVector_ne_zero k z) (unstableVector_ne_zero k z)
      (norm_stableVector k _) (norm_unstableVector k _) (hs hp) (hu hp)).symm
  · simp only [hp, false_and]

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_TransverseLines
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma standardLyapunov_iterate (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (z : Torus) :
    standardLyapunov k hk ((standardMap k)^[n] z)=standardLyapunov k hk z := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', standardLyapunov_invariant, ih]

lemma ae_stableVector_product_covariant (k : ℝ) (hk : 0 ≤ k) (n : ℕ) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (stableVector k ((standardMap k)^[n] z))
        (standardDerivativeProduct k z n (stableVector k z))=0 := by
  induction n with
  | zero => exact Eventually.of_forall fun z _ => by simp only [standardDerivativeProduct_zero, ContinuousLinearMap.id_apply, Function.iterate_zero_apply]; dsimp only [wedge]; ring
  | succ n ih =>
    have hs := ((measurePreserving_standardMap k).iterate n).quasiMeasurePreserving.ae
      (ae_stableVector_covariant k hk)
    filter_upwards [ih, hs] with z hz hnext hp
    have he := unit_collinear_eq_smul (norm_stableVector k _) (hz hp)
    have hh := hnext (by simpa only [standardLyapunov_iterate] using hp)
    rw [standardDerivativeProduct_succ, ContinuousLinearMap.comp_apply, he, map_smul,
      Function.iterate_succ_apply', wedge_smul_right, hh, mul_zero]

lemma standardDerivativeProduct_inverse (k : ℝ) (z : Torus) (n : ℕ) (v : ℂ) :
    standardInverseDerivativeProduct k ((standardMap k)^[n] z) n
      (standardDerivativeProduct k z n v)=v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [standardDerivativeProduct_succ, ContinuousLinearMap.comp_apply,
      ← standardInverseDerivativeProduct_shift, Function.iterate_succ_apply',
      inverseMap_standardMap, standardInverseDerivative_standardDerivative, ih]

lemma standardDerivativeProduct_norm_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    ‖standardDerivativeProduct k z n‖ ≤ (9*growthBase k)^n := by
  induction n with
  | zero => simp [standardDerivativeProduct]
  | succ n ih =>
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by
        rw [pow_succ']
        exact mul_le_mul (standardDerivative_norm_bound k hk _) ih
          (norm_nonneg _) (by have := growthBase_ge_four k hk; positivity))

lemma standardInverseDerivativeProduct_norm_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    ‖standardInverseDerivativeProduct k z n‖ ≤ (9*growthBase k)^n := by
  induction n with
  | zero => simp [standardInverseDerivativeProduct]
  | succ n ih =>
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by
        rw [pow_succ']
        exact mul_le_mul (standardInverseDerivative_norm_bound k hk _) ih
          (norm_nonneg _) (by have := growthBase_ge_four k hk; positivity))

lemma area_unit_log_abs_bound (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A)
    {v : ℂ} (hv : ‖v‖=1) : |Real.log ‖A v‖| ≤ Real.log ‖A‖ := by
  have hpA : 0 < ‖A‖ := lt_of_lt_of_le zero_lt_one hA.singular_pair.choose_spec.2.2.2.2
  have hpv : 0 < ‖A v‖ := by
    have hh := hA.norm_lower v
    rw [hv] at hh
    by_contra h
    have hz : ‖A v‖=0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hz, mul_zero] at hh
    norm_num at hh
  have hupper : ‖A v‖ ≤ ‖A‖ := by simpa only [hv, mul_one] using A.le_opNorm v
  have hlower := Real.log_le_log (by norm_num : (0 : ℝ) < 1)
    (show 1 ≤ ‖A‖*‖A v‖ by simpa only [hv] using hA.norm_lower v)
  rw [Real.log_one, Real.log_mul hpA.ne' hpv.ne'] at hlower
  exact abs_le.mpr ⟨by linarith, Real.log_le_log hpv hupper⟩

lemma area_unit_rate_bound (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A)
    {v : ℂ} (hv : ‖v‖=1) {K : ℝ} (hK : 1≤K) (n : ℕ) (hbound : ‖A‖ ≤ K^n) :
    |Real.log ‖A v‖/(n : ℝ)| ≤ Real.log K := by
  have hKpos : 0<K := lt_of_lt_of_le zero_lt_one hK
  have hlog := Real.log_le_log
    (lt_of_lt_of_le zero_lt_one hA.singular_pair.choose_spec.2.2.2.2) hbound
  rw [Real.log_pow] at hlog
  have hh := (area_unit_log_abs_bound A hA hv).trans hlog
  rw [abs_div, Nat.abs_cast]
  by_cases hn : n=0
  · simp only [hn, Nat.cast_zero, div_zero]; exact Real.log_nonneg hK
  · exact (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn : (0 : ℝ)<n)).mpr (by nlinarith)

lemma measurable_stableGrowthAverage (k : ℝ) (n : ℕ) : Measurable (stableGrowthAverage k n) :=
  ((((continuous_fst.clm_apply continuous_snd : Continuous (fun p : (ℂ →L[ℝ] ℂ) × ℂ => p.1 p.2)).measurable.comp
    ((continuous_standardDerivativeProduct k n).measurable.prodMk (measurable_stableVector k))).norm).log).div_const _
lemma measurable_stableBackwardAverage (k : ℝ) (n : ℕ) : Measurable (stableBackwardAverage k n) :=
  ((((continuous_fst.clm_apply continuous_snd : Continuous (fun p : (ℂ →L[ℝ] ℂ) × ℂ => p.1 p.2)).measurable.comp
    ((continuous_standardInverseDerivativeProduct k n).measurable.prodMk (measurable_stableVector k))).norm).log).div_const _

lemma stableGrowthAverage_bound (k : ℝ) (hk : 0≤k) (n : ℕ) (z : Torus) :
    |stableGrowthAverage k n z| ≤ Real.log (9*growthBase k) :=
  area_unit_rate_bound _ (standardDerivativeProduct_area k z n) (norm_stableVector k z)
    (by have := growthBase_ge_four k hk; linarith) n (standardDerivativeProduct_norm_bound k hk z n)
lemma stableBackwardAverage_bound (k : ℝ) (hk : 0≤k) (n : ℕ) (z : Torus) :
    |stableBackwardAverage k n z| ≤ Real.log (9*growthBase k) :=
  area_unit_rate_bound _ (standardInverseDerivativeProduct_area k z n) (norm_stableVector k z)
    (by have := growthBase_ge_four k hk; linarith) n (standardInverseDerivativeProduct_norm_bound k hk z n)

lemma ae_stable_averages_cancel (k : ℝ) (hk : 0≤k) (n : ℕ) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      stableGrowthAverage k n z + stableBackwardAverage k n ((standardMap k)^[n] z)=0 := by
  filter_upwards [ae_stableVector_product_covariant k hk n] with z hz hp
  let v := standardDerivativeProduct k z n (stableVector k z)
  let s := stableVector k ((standardMap k)^[n] z)
  have he : v = dot s v • s := unit_collinear_eq_smul (norm_stableVector k _) (hz hp)
  have hnorm : ‖v‖ = |dot s v| := by
    conv_lhs => rw [he, norm_smul, Real.norm_eq_abs, show ‖s‖=1 from norm_stableVector k _, mul_one]
  have hmul : ‖v‖ * ‖standardInverseDerivativeProduct k ((standardMap k)^[n] z) n s‖ = 1 := by
    calc
      _ = ‖standardInverseDerivativeProduct k ((standardMap k)^[n] z) n v‖ := by
        conv_rhs => rw [he, map_smul, norm_smul, Real.norm_eq_abs, ← hnorm]
      _ = 1 := by rw [standardDerivativeProduct_inverse, norm_stableVector]
  have hpv := PlaneLyapunov.image_norm_pos _ (standardDerivativeProduct_area k z)
    (stableVector_ne_zero k z) n
  have hps := PlaneLyapunov.image_norm_pos _ (standardInverseDerivativeProduct_area k ((standardMap k)^[n] z))
    (stableVector_ne_zero k ((standardMap k)^[n] z)) n
  have hlog := congrArg Real.log hmul
  rw [Real.log_mul hpv.ne' hps.ne', Real.log_one] at hlog
  unfold stableGrowthAverage stableBackwardAverage
  rw [← add_div, hlog, zero_div]

lemma measurePreserving_coincidentLines (k : ℝ) (hk : 0≤k) :
    MeasurePreserving (standardMap k) (area.restrict (coincidentLines k hk))
      (area.restrict (coincidentLines k hk)) := by
  have hh := (measurePreserving_standardMap k).restrict_preimage (measurableSet_coincidentLines k hk)
  rw [Measure.restrict_congr_set (preimage_coincidentLines_ae k hk)] at hh
  exact hh

lemma ae_coincident_backward_growth (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area.restrict (coincidentLines k hk), Tendsto (fun n => stableBackwardAverage k n z)
      atTop (𝓝 (-standardLyapunov k hk z)) := by
  filter_upwards [ae_restrict_mem (measurableSet_coincidentLines k hk),
    (ae_unstableVector_growth k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le] with z hz hg
  have hw : wedge (unstableVector k z) (stableVector k z)=0 := by
    rw [wedge_swap, hz.2, neg_zero]
  exact (PlaneLyapunov.growth_on_line _ (standardInverseDerivativeProduct_area k z)
    (norm_unstableVector k z) (hg hz.1) (stableVector k z) (stableVector_ne_zero k z) hw).2

theorem measure_coincidentLines_zero (k : ℝ) (hk : 0≤k) : area (coincidentLines k hk)=0 := by
  let μ := area.restrict (coincidentLines k hk)
  let C := Real.log (9*growthBase k)
  have ha (n) : Integrable (stableGrowthAverage k n) μ :=
    Integrable.mono' (integrable_const C) (measurable_stableGrowthAverage k n).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact stableGrowthAverage_bound k hk n z)
  have hb (n) : Integrable (stableBackwardAverage k n) μ :=
    Integrable.mono' (integrable_const C) (measurable_stableBackwardAverage k n).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact stableBackwardAverage_bound k hk n z)
  have hla : Tendsto (fun n => ∫ z, stableGrowthAverage k n z ∂μ) atTop
      (𝓝 (∫ z, -standardLyapunov k hk z ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Torus => C)
      (fun n => (measurable_stableGrowthAverage k n).aestronglyMeasurable) (integrable_const C)
      (fun n => Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact stableGrowthAverage_bound k hk n z)
    filter_upwards [ae_restrict_mem (measurableSet_coincidentLines k hk),
      (ae_stableVector_growth k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le] with z hz hg
    exact (hg hz.1).2
  have hlb : Tendsto (fun n => ∫ z, stableBackwardAverage k n z ∂μ) atTop
      (𝓝 (∫ z, -standardLyapunov k hk z ∂μ)) := by
    exact tendsto_integral_of_dominated_convergence (fun _ : Torus => C)
      (fun n => (measurable_stableBackwardAverage k n).aestronglyMeasurable) (integrable_const C)
      (fun n => Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact stableBackwardAverage_bound k hk n z)
      (ae_coincident_backward_growth k hk)
  have hcancel (n) : (∫ z, stableGrowthAverage k n z ∂μ) +
      (∫ z, stableBackwardAverage k n z ∂μ)=0 := by
    have hmp : MeasurePreserving ((standardMap k)^[n]) μ μ :=
      (measurePreserving_coincidentLines k hk).iterate n
    have hcomp : Integrable (fun z => stableBackwardAverage k n ((standardMap k)^[n] z)) μ :=
      hmp.integrable_comp_of_integrable (hb n)
    rw [← BoundedSubadditive.integral_comp hmp (hb n).aestronglyMeasurable,
      ← integral_add (ha n) hcomp]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (measurableSet_coincidentLines k hk),
      (ae_stable_averages_cancel k hk n).filter_mono Measure.absolutelyContinuous_restrict.ae_le] with z hz he
    exact he hz.1
  have hz : (∫ z, -standardLyapunov k hk z ∂μ) + (∫ z, -standardLyapunov k hk z ∂μ)=0 :=
    tendsto_nhds_unique (hla.add hlb) (by simpa only [hcancel] using tendsto_const_nhds (x := (0 : ℝ)))
  have hzero : (∫ z, standardLyapunov k hk z ∂μ)=0 := by
    rw [integral_neg] at hz
    linarith
  have hAE : ∀ᵐ z ∂μ, standardLyapunov k hk z=0 :=
    (integral_eq_zero_iff_of_nonneg (standardLyapunov_nonneg k hk)
      (integrable_standardLyapunov k hk).integrableOn).mp hzero
  have hempty : ∀ᵐ z ∂μ, False := by
    filter_upwards [hAE, ae_restrict_mem (measurableSet_coincidentLines k hk)] with z hz hmem
    exact (ne_of_gt hmem.1) hz
  have hμ : μ=0 := ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hempty)
  have hh := congrArg (fun ν : Measure Torus => ν univ) hμ
  simpa only [μ, Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using hh

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma ae_transverseLines (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (stableVector k z) (unstableVector k z) ≠ 0 := by
  have hh : ∀ᵐ z ∂area, z ∉ coincidentLines k hk := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using measure_coincidentLines_zero k hk
  filter_upwards [hh] with z hz hp hw
  exact hz ⟨hp,hw⟩

theorem ae_hyperbolic_splitting (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (stableVector k z) (unstableVector k z) ≠ 0 ∧
      PlaneLyapunov.Growth (standardDerivativeProduct k z) (stableVector k z) (-standardLyapunov k hk z) ∧
      PlaneLyapunov.Growth (standardDerivativeProduct k z) (unstableVector k z) (standardLyapunov k hk z) ∧
      PlaneLyapunov.Growth (standardInverseDerivativeProduct k z) (stableVector k z) (standardLyapunov k hk z) ∧
      PlaneLyapunov.Growth (standardInverseDerivativeProduct k z) (unstableVector k z) (-standardLyapunov k hk z) ∧
      wedge (stableVector k (standardMap k z)) (standardDerivative k z (stableVector k z))=0 ∧
      wedge (unstableVector k (standardMap k z)) (standardDerivative k z (unstableVector k z))=0 := by
  filter_upwards [ae_transverseLines k hk, ae_stableVector_growth k hk, ae_unstableVector_growth k hk,
    ae_standardLyapunov_rate k hk, ae_standardInverseLyapunov_rate k hk,
    ae_stableVector_covariant k hk, ae_unstableVector_covariant k hk] with z ht hs hu ha hb hsc huc hp
  have hrev : wedge (unstableVector k z) (stableVector k z) ≠ 0 := by
    rw [wedge_swap]; exact neg_ne_zero.mpr (ht hp)
  exact ⟨ht hp, hs hp,
    PlaneLyapunov.growth_off_line _ (standardDerivativeProduct_area k z) ha (hs hp)
      (unstableVector k z) (unstableVector_ne_zero k z) (ht hp),
    PlaneLyapunov.growth_off_line _ (standardInverseDerivativeProduct_area k z) hb (hu hp)
      (stableVector k z) (stableVector_ne_zero k z) hrev,
    hu hp, hsc hp, huc hp⟩

lemma measurePreserving_inverseMap (k : ℝ) : MeasurePreserving (inverseMap k) area area :=
  (measurePreserving_standardMap k).symm (standardMap_measurableEquiv k)

lemma standardLyapunov_inverse (k : ℝ) (hk : 0≤k) (z : Torus) :
    standardLyapunov k hk (inverseMap k z)=standardLyapunov k hk z := by
  have hh := standardLyapunov_invariant k hk (inverseMap k z)
  rw [standardMap_inverseMap] at hh
  exact hh.symm

lemma standardLyapunov_inverse_iterate (k : ℝ) (hk : 0≤k) (n : ℕ) (z : Torus) :
    standardLyapunov k hk ((inverseMap k)^[n] z)=standardLyapunov k hk z := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', standardLyapunov_inverse, ih]

lemma inverse_covariant_line (k : ℝ) (z : Torus) {s t : ℂ}
    (h : wedge s (standardDerivative k (inverseMap k z) t)=0) :
    wedge t (standardInverseDerivative k z s)=0 := by
  have hh := (standardInverseDerivative_area k z) s (standardDerivative k (inverseMap k z) t)
  have he := standardInverseDerivative_standardDerivative k (inverseMap k z) t
  rw [standardMap_inverseMap] at he
  rw [he, h] at hh
  rw [wedge_swap, hh, neg_zero]

lemma ae_stableVector_inverse_covariant (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (stableVector k (inverseMap k z)) (standardInverseDerivative k z (stableVector k z))=0 := by
  filter_upwards [(measurePreserving_inverseMap k).quasiMeasurePreserving.ae
    (ae_stableVector_covariant k hk)] with z hz hp
  apply inverse_covariant_line k z
  simpa only [standardMap_inverseMap] using hz (by simpa only [standardLyapunov_inverse] using hp)

lemma ae_unstableVector_inverse_covariant (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (unstableVector k (inverseMap k z)) (standardInverseDerivative k z (unstableVector k z))=0 := by
  filter_upwards [(measurePreserving_inverseMap k).quasiMeasurePreserving.ae
    (ae_unstableVector_covariant k hk)] with z hz hp
  apply inverse_covariant_line k z
  simpa only [standardMap_inverseMap] using hz (by simpa only [standardLyapunov_inverse] using hp)

lemma ae_unstableVector_product_covariant (k : ℝ) (hk : 0≤k) (n : ℕ) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (unstableVector k ((standardMap k)^[n] z))
        (standardDerivativeProduct k z n (unstableVector k z))=0 := by
  induction n with
  | zero =>
    exact Eventually.of_forall fun z _ => by
      simp only [standardDerivativeProduct_zero, ContinuousLinearMap.id_apply, Function.iterate_zero_apply]
      dsimp only [wedge]; ring
  | succ n ih =>
    have hs := ((measurePreserving_standardMap k).iterate n).quasiMeasurePreserving.ae
      (ae_unstableVector_covariant k hk)
    filter_upwards [ih, hs] with z hz hnext hp
    have he := unit_collinear_eq_smul (norm_unstableVector k _) (hz hp)
    have hh := hnext (by simpa only [standardLyapunov_iterate] using hp)
    rw [standardDerivativeProduct_succ, ContinuousLinearMap.comp_apply, he, map_smul,
      Function.iterate_succ_apply', wedge_smul_right, hh, mul_zero]

lemma ae_stableVector_inverse_product_covariant (k : ℝ) (hk : 0≤k) (n : ℕ) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (stableVector k ((inverseMap k)^[n] z))
        (standardInverseDerivativeProduct k z n (stableVector k z))=0 := by
  induction n with
  | zero =>
    exact Eventually.of_forall fun z _ => by
      simp only [standardInverseDerivativeProduct, ContinuousLinearMap.id_apply, Function.iterate_zero_apply]
      dsimp only [wedge]; ring
  | succ n ih =>
    have hs := ((measurePreserving_inverseMap k).iterate n).quasiMeasurePreserving.ae
      (ae_stableVector_inverse_covariant k hk)
    filter_upwards [ih, hs] with z hz hnext hp
    have he := unit_collinear_eq_smul (norm_stableVector k _) (hz hp)
    have hh := hnext (by simpa only [standardLyapunov_inverse_iterate] using hp)
    rw [standardInverseDerivativeProduct, ContinuousLinearMap.comp_apply, he, map_smul,
      Function.iterate_succ_apply', wedge_smul_right, hh, mul_zero]

lemma ae_unstableVector_inverse_product_covariant (k : ℝ) (hk : 0≤k) (n : ℕ) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (unstableVector k ((inverseMap k)^[n] z))
        (standardInverseDerivativeProduct k z n (unstableVector k z))=0 := by
  induction n with
  | zero =>
    exact Eventually.of_forall fun z _ => by
      simp only [standardInverseDerivativeProduct, ContinuousLinearMap.id_apply, Function.iterate_zero_apply]
      dsimp only [wedge]; ring
  | succ n ih =>
    have hs := ((measurePreserving_inverseMap k).iterate n).quasiMeasurePreserving.ae
      (ae_unstableVector_inverse_covariant k hk)
    filter_upwards [ih, hs] with z hz hnext hp
    have he := unit_collinear_eq_smul (norm_unstableVector k _) (hz hp)
    have hh := hnext (by simpa only [standardLyapunov_inverse_iterate] using hp)
    rw [standardInverseDerivativeProduct, ContinuousLinearMap.comp_apply, he, map_smul,
      Function.iterate_succ_apply', wedge_smul_right, hh, mul_zero]

lemma invariant_unit_frame_wedge (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A)
    {s u t v : ℂ} (ht : ‖t‖=1) (hv : ‖v‖=1)
    (hst : wedge t (A s)=0) (huv : wedge v (A u)=0) :
    |wedge s u| = ‖A s‖ * ‖A u‖ * |wedge t v| := by
  have he1 := unit_collinear_eq_smul ht hst
  have he2 := unit_collinear_eq_smul hv huv
  rw [← hA, he1, he2, wedge_smul_left, wedge_smul_right, abs_mul, abs_mul,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, ht, hv, mul_one, mul_one]
  ring

lemma invariant_frame_angle_rate (A : ℕ → ℂ →L[ℝ] ℂ)
    (hA : ∀ n, PlaneAreaPreserving (A n)) {s u : ℂ}
    (hs : s ≠ 0) (hu : u ≠ 0) (hw : wedge s u ≠ 0)
    (t v : ℕ → ℂ) (ht : ∀ n, ‖t n‖=1) (hv : ∀ n, ‖v n‖=1)
    (hst : ∀ n, wedge (t n) (A n s)=0) (huv : ∀ n, wedge (v n) (A n u)=0)
    {l : ℝ} (hgrs : PlaneLyapunov.Growth A s l) (hgru : PlaneLyapunov.Growth A u (-l)) :
    Tendsto (fun n : ℕ => Real.log |wedge (t n) (v n)|/(n : ℝ)) atTop (𝓝 0) := by
  have he (n) := invariant_unit_frame_wedge (A n) (hA n) (ht n) (hv n) (hst n) (huv n)
  have hpos (n) : 0 < |wedge (t n) (v n)| := by
    have hp := abs_pos.mpr hw
    rw [he n] at hp
    exact (mul_pos_iff.mp hp).resolve_right (fun h => (not_lt_of_ge (mul_nonneg (norm_nonneg _) (norm_nonneg _))) h.1) |>.2
  have ha (n) := PlaneLyapunov.image_norm_pos A hA hs n
  have hb (n) := PlaneLyapunov.image_norm_pos A hA hu n
  have hlog (n) : Real.log |wedge (t n) (v n)| =
      Real.log |wedge s u|-Real.log ‖A n s‖-Real.log ‖A n u‖ := by
    have hh := congrArg Real.log (he n)
    rw [Real.log_mul (mul_pos (ha n) (hb n)).ne' (hpos n).ne',
      Real.log_mul (ha n).ne' (hb n).ne'] at hh
    linarith
  have hc : Tendsto (fun n : ℕ => Real.log |wedge s u|/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := (hc.sub hgrs.2).sub hgru.2
  simpa only [hlog, sub_div, zero_sub, sub_neg_eq_add, neg_add_cancel] using hh

theorem ae_angle_tempered (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      Tendsto (fun n : ℕ => Real.log |wedge (stableVector k ((standardMap k)^[n] z))
        (unstableVector k ((standardMap k)^[n] z))|/(n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.log |wedge (stableVector k ((inverseMap k)^[n] z))
        (unstableVector k ((inverseMap k)^[n] z))|/(n : ℝ)) atTop (𝓝 0) := by
  filter_upwards [ae_hyperbolic_splitting k hk,
    ae_all_iff.mpr (ae_stableVector_product_covariant k hk),
    ae_all_iff.mpr (ae_unstableVector_product_covariant k hk),
    ae_all_iff.mpr (ae_stableVector_inverse_product_covariant k hk),
    ae_all_iff.mpr (ae_unstableVector_inverse_product_covariant k hk)] with z hz hsc huc hsb hub hp
  rcases hz hp with ⟨ht, hs, hu, bs, bu, _⟩
  constructor
  · apply invariant_frame_angle_rate _ (standardDerivativeProduct_area k z)
      (stableVector_ne_zero k z) (unstableVector_ne_zero k z) ht
      (fun n => stableVector k ((standardMap k)^[n] z))
      (fun n => unstableVector k ((standardMap k)^[n] z))
      (fun n => norm_stableVector k _) (fun n => norm_unstableVector k _)
      (fun n => hsc n hp) (fun n => huc n hp) hs
    simpa only [neg_neg] using hu
  · exact invariant_frame_angle_rate _ (standardInverseDerivativeProduct_area k z)
      (stableVector_ne_zero k z) (unstableVector_ne_zero k z) ht
      (fun n => stableVector k ((inverseMap k)^[n] z))
      (fun n => unstableVector k ((inverseMap k)^[n] z))
      (fun n => norm_stableVector k _) (fun n => norm_unstableVector k _)
      (fun n => hsb n hp) (fun n => hub n hp) bs bu

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PlaneLyapunov

lemma summable_energy (A : ℕ → ℂ →L[ℝ] ℂ) (hA : ∀ n, PlaneAreaPreserving (A n))
    {v : ℂ} {l χ : ℝ} (hg : Growth A v l) (hχ : l+χ < 0) :
    Summable (fun n : ℕ => ‖A n v‖^2 * Real.exp (2*χ*(n : ℝ))) := by
  let a := (l-χ)/2
  have ha : l<a := by dsimp only [a]; linarith
  have hb : 2*(a+χ)<0 := by dsimp only [a]; linarith
  have hsum := summable_geometric_of_lt_one (Real.exp_pos (2*(a+χ))).le
    (Real.exp_lt_one_iff.mpr hb)
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [(tendsto_order.mp hg.2).2 a ha, eventually_gt_atTop 0] with n hn hn0
  have hnp : (0 : ℝ)<n := by exact_mod_cast hn0
  have hlt := (div_lt_iff₀ hnp).mp hn
  have hnorm : ‖A n v‖ ≤ Real.exp (a*(n : ℝ)) := by
    calc
      _ = Real.exp (Real.log ‖A n v‖) := (Real.exp_log (image_norm_pos A hA hg.1 n)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlt.le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
  calc
    _ ≤ (Real.exp (a*(n : ℝ)))^2 * Real.exp (2*χ*(n : ℝ)) :=
      mul_le_mul_of_nonneg_right (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le |>.mpr hnorm)
        (Real.exp_pos _).le
    _ = (Real.exp (2*(a+χ)))^n := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring

lemma energy_ge_one (A : ℕ → ℂ →L[ℝ] ℂ) (χ : ℝ) {v : ℂ}
    (hunit : ‖v‖=1) (hzero : A 0 = ContinuousLinearMap.id ℝ ℂ)
    (hsum : Summable (fun n : ℕ => ‖A n v‖^2 * Real.exp (2*χ*(n : ℝ)))) :
    1 ≤ energy A χ v := by
  have hh := hsum.le_tsum 0 (fun n _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  simpa only [hzero, ContinuousLinearMap.id_apply, hunit, one_pow, Nat.cast_zero,
    mul_zero, Real.exp_zero, mul_one, energy] using hh

lemma measurable_energy {X : Type*} [MeasurableSpace X]
    (A : X → ℕ → ℂ →L[ℝ] ℂ) (χ : ℝ) (v : X → ℂ)
    (hA : ∀ n, Measurable (fun x => A x n)) (hv : Measurable v) :
    Measurable (fun x => energy (A x) χ (v x)) := by
  apply Measurable.tsum
  intro n
  exact (((continuous_fst.clm_apply continuous_snd :
    Continuous (fun p : (ℂ →L[ℝ] ℂ) × ℂ => p.1 p.2)).measurable.comp
    ((hA n).prodMk hv)).norm.pow_const 2).mul_const _

lemma energy_shift (A B : ℕ → ℂ →L[ℝ] ℂ) (D : ℂ →L[ℝ] ℂ)
    (hshift : ∀ n v, B n (D v)=A (n+1) v)
    (hzero : A 0=ContinuousLinearMap.id ℝ ℂ) {s t : ℂ}
    (hs : ‖s‖=1) (ht : ‖t‖=1) (hcov : wedge t (D s)=0) (χ : ℝ)
    (hsum : Summable (fun n : ℕ => ‖A n s‖^2 * Real.exp (2*χ*(n : ℝ)))) :
    energy A χ s = 1 + Real.exp (2*χ)*‖D s‖^2*energy B χ t := by
  have he := unit_collinear_eq_smul ht hcov
  have hn : ‖D s‖ = |dot t (D s)| := by
    conv_lhs => rw [he, norm_smul, Real.norm_eq_abs, ht, mul_one]
  have hc (n : ℕ) : ‖A (n+1) s‖^2 * Real.exp (2*χ*((n+1 : ℕ) : ℝ)) =
      (Real.exp (2*χ)*‖D s‖^2) * (‖B n t‖^2 * Real.exp (2*χ*(n : ℝ))) := by
    conv_lhs => rw [← hshift, he, map_smul, norm_smul, Real.norm_eq_abs, ← hn]
    have hexp : Real.exp (2*χ*((n+1 : ℕ) : ℝ)) =
        Real.exp (2*χ) * Real.exp (2*χ*(n : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  unfold energy
  rw [hsum.tsum_eq_zero_add, hzero, ContinuousLinearMap.id_apply, hs, one_pow,
    Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
  simp_rw [hc]
  rw [tsum_mul_left]

end PlaneLyapunov

lemma measurable_stableEnergy (k χ : ℝ) : Measurable (stableEnergy k χ) :=
  PlaneLyapunov.measurable_energy _ χ _
    (fun n => (continuous_standardDerivativeProduct k n).measurable) (measurable_stableVector k)
lemma measurable_unstableEnergy (k χ : ℝ) : Measurable (unstableEnergy k χ) :=
  PlaneLyapunov.measurable_energy _ χ _
    (fun n => (continuous_standardInverseDerivativeProduct k n).measurable) (measurable_unstableVector k)
lemma measurable_stableScale (k χ : ℝ) : Measurable (stableScale k χ) :=
  Real.continuous_sqrt.measurable.comp (measurable_const.max (measurable_stableEnergy k χ))
lemma measurable_unstableScale (k χ : ℝ) : Measurable (unstableScale k χ) :=
  Real.continuous_sqrt.measurable.comp (measurable_const.max (measurable_unstableEnergy k χ))

lemma ae_stableEnergy_regular (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area, χ < standardLyapunov k hk z →
      Summable (fun n : ℕ => ‖standardDerivativeProduct k z n (stableVector k z)‖^2 *
        Real.exp (2*χ*(n : ℝ))) ∧ 1 ≤ stableEnergy k χ z ∧
      (stableScale k χ z)^2=stableEnergy k χ z ∧
      stableEnergy k χ z = 1 + Real.exp (2*χ)*‖standardDerivative k z (stableVector k z)‖^2*
        stableEnergy k χ (standardMap k z) := by
  filter_upwards [ae_stableVector_growth k hk, ae_stableVector_covariant k hk] with z hg hcov hpos
  have hp := hχ.trans_lt hpos
  have hsum := PlaneLyapunov.summable_energy _ (standardDerivativeProduct_area k z) (hg hp)
    (show -standardLyapunov k hk z+χ<0 by linarith)
  have hge : 1 ≤ stableEnergy k χ z := PlaneLyapunov.energy_ge_one _ χ (norm_stableVector k z) rfl hsum
  refine ⟨hsum,hge,?_,?_⟩
  · rw [stableScale, max_eq_right hge, Real.sq_sqrt (zero_le_one.trans hge)]
  · exact PlaneLyapunov.energy_shift _ _ (standardDerivative k z)
      (standardDerivativeProduct_shift k z) rfl (norm_stableVector k z)
      (norm_stableVector k _) (hcov hp) χ hsum

lemma ae_unstableEnergy_regular (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area, χ < standardLyapunov k hk z →
      Summable (fun n : ℕ => ‖standardInverseDerivativeProduct k z n (unstableVector k z)‖^2 *
        Real.exp (2*χ*(n : ℝ))) ∧ 1 ≤ unstableEnergy k χ z ∧
      (unstableScale k χ z)^2=unstableEnergy k χ z ∧
      unstableEnergy k χ z = 1 + Real.exp (2*χ)*‖standardInverseDerivative k z (unstableVector k z)‖^2*
        unstableEnergy k χ (inverseMap k z) := by
  filter_upwards [ae_unstableVector_growth k hk, ae_unstableVector_inverse_covariant k hk] with z hg hcov hpos
  have hp := hχ.trans_lt hpos
  have hsum := PlaneLyapunov.summable_energy _ (standardInverseDerivativeProduct_area k z) (hg hp)
    (show -standardLyapunov k hk z+χ<0 by linarith)
  have hge : 1 ≤ unstableEnergy k χ z := PlaneLyapunov.energy_ge_one _ χ (norm_unstableVector k z) rfl hsum
  refine ⟨hsum,hge,?_,?_⟩
  · rw [unstableScale, max_eq_right hge, Real.sq_sqrt (zero_le_one.trans hge)]
  · exact PlaneLyapunov.energy_shift _ _ (standardInverseDerivative k z)
      (standardInverseDerivativeProduct_shift k z) rfl (norm_unstableVector k z)
      (norm_unstableVector k _) (hcov hp) χ hsum

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_BoundedTempering
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace BoundedSubadditive
variable {X : Type*} [MeasurableSpace X] {T : X → X}

lemma ae_exists_bounded_average_limit {μ : Measure X} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : 0<C) (hbound : ∀ x, |g x|≤C) :
    ∀ᵐ x ∂μ, ∃ l : ℝ, Tendsto (fun n : ℕ => birkhoffSum T g n x/(n : ℝ)) atTop (𝓝 l) := by
  let r : X → ℝ := fun x => (g x+C)/(2*C)
  have hr : Measurable r := (hg.add_const C).div_const _
  have hr0 (x) : 0 ≤ r x := div_nonneg (by have := (abs_le.mp (hbound x)).1; linarith) (by positivity)
  have hr1 (x) : r x≤1 := by
    apply (div_le_iff₀ (show 0<2*C by positivity)).mpr
    have := (abs_le.mp (hbound x)).2
    linarith
  let f := observationCocycle r hT.measurable hr hr0 hr1
  have he (n : ℕ) (x : X) : birkhoffSum T g n x =
      2*C*birkhoffSum T r n x-(n : ℝ)*C := by
    have hpoint (y : X) : g y=2*C*r y-C := by dsimp only [r]; field_simp; ring
    unfold birkhoffSum
    calc
      _ = ∑ i ∈ Finset.range n, (2*C*r (T^[i] x)-C) := Finset.sum_congr rfl fun i _ => hpoint _
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp
  filter_upwards [f.ae_tendsto_average hT] with x hx
  refine ⟨2*C*f.lowerRate x-C, ?_⟩
  have hh := (hx.const_mul (2*C)).sub_const C
  apply hh.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  change 2*C*(birkhoffSum T r n x/(n : ℝ))-C = birkhoffSum T g n x/(n : ℝ)
  rw [he]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

theorem ae_nonnegative_coboundary_tempered {μ : Measure X} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {u : X → ℝ} (hu : Measurable u) (h0 : ∀ x, 0≤u x)
    {C : ℝ} (hC : 0<C) (hstep : ∀ᵐ x ∂μ, |u (T x)-u x|≤C) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => u (T^[n] x)/(n : ℝ)) atTop (𝓝 0) := by
  let g : X → ℝ := fun x => max (-C) (min C (u (T x)-u x))
  have hg : Measurable g := measurable_const.max
    (measurable_const.min ((hu.comp hT.measurable).sub hu))
  have hbound (x : X) : |g x|≤C := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have heq : ∀ᵐ x ∂μ, g x=u (T x)-u x := by
    filter_upwards [hstep] with x hx
    dsimp only [g]
    rw [min_eq_right (abs_le.mp hx).2, max_eq_right (abs_le.mp hx).1]
  have htel : ∀ᵐ x ∂μ, ∀ n : ℕ, birkhoffSum T g n x=u (T^[n] x)-u x := by
    filter_upwards [ae_all_iff.mpr (fun n : ℕ => (hT.iterate n).quasiMeasurePreserving.ae heq)] with x hx
    intro n
    induction n with
    | zero => simp only [birkhoffSum_zero, Function.iterate_zero_apply, sub_self]
    | succ n ih =>
      rw [birkhoffSum_succ, ih, hx n, Function.iterate_succ_apply']
      ring
  have hrec : ∀ᵐ x ∂μ, ∀ N : ℕ, u x≤N → ∃ᶠ n : ℕ in atTop, u (T^[n] x)≤N := by
    exact ae_all_iff.mpr fun N => hT.conservative.ae_mem_imp_frequently_image_mem
      (measurableSet_le hu measurable_const).nullMeasurableSet
  filter_upwards [ae_exists_bounded_average_limit hT hg hC hbound, htel, hrec] with x hx ht hr
  obtain ⟨l,hl⟩ := hx
  have hlim : Tendsto (fun n : ℕ => u (T^[n] x)/(n : ℝ)) atTop (𝓝 l) := by
    have hc : Tendsto (fun n : ℕ => u x/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [ht, sub_div, sub_add_cancel, add_zero] using hl.add hc
  have hl0 : 0≤l := ge_of_tendsto hlim (Eventually.of_forall fun n => div_nonneg (h0 _) (Nat.cast_nonneg _))
  obtain ⟨N,hN⟩ := exists_nat_ge (u x)
  have hreturn := hr N hN
  have hnlim : Tendsto (fun n : ℕ => (N : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hl1 : l≤0 := le_of_tendsto_of_tendsto_of_frequently hlim hnlim
    (hreturn.mono fun n hn => div_le_div_of_nonneg_right hn (Nat.cast_nonneg _))
  have he : l=0 := le_antisymm hl1 hl0
  rwa [he] at hlim

end BoundedSubadditive

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma measurableSet_spectralGapRegion (k : ℝ) (hk : 0≤k) (χ : ℝ) :
    MeasurableSet (spectralGapRegion k hk χ) :=
  measurableSet_lt measurable_const (measurable_standardLyapunov k hk)
lemma preimage_spectralGapRegion (k : ℝ) (hk : 0≤k) (χ : ℝ) :
    standardMap k ⁻¹' spectralGapRegion k hk χ = spectralGapRegion k hk χ := by
  ext z
  simp only [spectralGapRegion, mem_preimage, mem_ofPred_eq, standardLyapunov_invariant]
lemma preimage_inverse_spectralGapRegion (k : ℝ) (hk : 0≤k) (χ : ℝ) :
    inverseMap k ⁻¹' spectralGapRegion k hk χ = spectralGapRegion k hk χ := by
  ext z
  simp only [spectralGapRegion, mem_preimage, mem_ofPred_eq, standardLyapunov_inverse]
lemma measurePreserving_spectralGapRegion (k : ℝ) (hk : 0≤k) (χ : ℝ) :
    MeasurePreserving (standardMap k) (area.restrict (spectralGapRegion k hk χ))
      (area.restrict (spectralGapRegion k hk χ)) := by
  have hh := (measurePreserving_standardMap k).restrict_preimage (measurableSet_spectralGapRegion k hk χ)
  rwa [preimage_spectralGapRegion] at hh
lemma measurePreserving_inverse_spectralGapRegion (k : ℝ) (hk : 0≤k) (χ : ℝ) :
    MeasurePreserving (inverseMap k) (area.restrict (spectralGapRegion k hk χ))
      (area.restrict (spectralGapRegion k hk χ)) := by
  have hh := (measurePreserving_inverseMap k).restrict_preimage (measurableSet_spectralGapRegion k hk χ)
  rwa [preimage_inverse_spectralGapRegion] at hh

lemma unit_image_bounds (A : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A)
    {K : ℝ} (hbound : ‖A‖≤K) {v : ℂ} (hv : ‖v‖=1) :
    ‖A v‖≤K ∧ 1≤K*‖A v‖ := by
  constructor
  · calc ‖A v‖ ≤ ‖A‖ := by simpa only [hv, mul_one] using A.le_opNorm v
         _ ≤ K := hbound
  · calc 1 ≤ ‖A‖*‖A v‖ := by simpa only [hv] using hA.norm_lower v
         _ ≤ K*‖A v‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

lemma positive_energy_ratio_bounds {a b ρ K t : ℝ}
    (ha : 1≤a) (hb : 1≤b) (hρ : 0≤ρ) (hK : 1≤K) (ht : 1≤t)
    (hu : ρ≤K) (hl : 1≤K*ρ) (he : a=1+t*ρ^2*b) :
    a≤(1+t*K^2+K^2)*b ∧ b≤(1+t*K^2+K^2)*a := by
  have hb0 : 0≤b := zero_le_one.trans hb
  have ha0 : 0≤a := zero_le_one.trans ha
  have hK0 : 0≤K := zero_le_one.trans hK
  have ht0 : 0≤t := zero_le_one.trans ht
  have hρK : ρ^2≤K^2 := (sq_le_sq₀ hρ hK0).mpr hu
  have hprod : 1≤K^2*ρ^2 := by nlinarith [sq_nonneg (K*ρ-1)]
  have hmain : ρ^2*b≤a := by nlinarith [mul_nonneg (sub_nonneg.mpr ht) (mul_nonneg (sq_nonneg ρ) hb0)]
  constructor
  · have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρK ht0) hb0
    nlinarith [mul_nonneg (sq_nonneg K) hb0]
  · have hh := mul_le_mul_of_nonneg_right hprod hb0
    have hh' := mul_le_mul_of_nonneg_left hmain (sq_nonneg K)
    have hp := mul_nonneg (show 0≤1+t*K^2 by positivity) ha0
    nlinarith

lemma log_ratio_bound {a b R : ℝ} (ha : 0<a) (hb : 0<b) (hR : 0<R)
    (hab : a≤R*b) (hba : b≤R*a) : |Real.log b-Real.log a|≤Real.log R := by
  have h1 := Real.log_le_log ha hab
  have h2 := Real.log_le_log hb hba
  rw [Real.log_mul hR.ne' hb.ne'] at h1
  rw [Real.log_mul hR.ne' ha.ne'] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma ae_both_coboundary_tempered {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {T S : X → X}
    (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S μ μ)
    (hTS : ∀ x, T (S x)=x) {u : X → ℝ} (hu : Measurable u) (h0 : ∀ x, 0≤u x)
    {C : ℝ} (hC : 0<C) (hstep : ∀ᵐ x ∂μ, |u (T x)-u x|≤C) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => u (T^[n] x)/(n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => u (S^[n] x)/(n : ℝ)) atTop (𝓝 0) := by
  have hstep' : ∀ᵐ x ∂μ, |u (S x)-u x|≤C := by
    filter_upwards [hS.quasiMeasurePreserving.ae hstep] with x hx
    rwa [hTS, abs_sub_comm] at hx
  exact (BoundedSubadditive.ae_nonnegative_coboundary_tempered hT hu h0 hC hstep).and
    (BoundedSubadditive.ae_nonnegative_coboundary_tempered hS hu h0 hC hstep')

lemma energyRatioBound_ge_one (k χ : ℝ) : 1≤energyRatioBound k χ := by
  unfold energyRatioBound
  have hh : 0 ≤ Real.exp (2*χ)*(9*growthBase k)^2 := by positivity
  nlinarith [sq_nonneg (9*growthBase k)]

lemma ae_stableEnergy_log_increment (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      |Real.log (max 1 (stableEnergy k χ (standardMap k z)))-
        Real.log (max 1 (stableEnergy k χ z))| ≤ Real.log (energyRatioBound k χ) := by
  have hreg := ae_stableEnergy_regular k hk χ hχ
  filter_upwards [ae_restrict_mem (measurableSet_spectralGapRegion k hk χ),
    hreg.filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    ((measurePreserving_standardMap k).quasiMeasurePreserving.ae hreg).filter_mono
      Measure.absolutelyContinuous_restrict.ae_le] with z hz h0 h1
  have hz' : χ < standardLyapunov k hk z := hz
  have ha := (h0 hz').2.1
  have hb := (h1 (by simpa only [standardLyapunov_invariant] using hz')).2.1
  have hi := unit_image_bounds _ (standardDerivative_area k z) (standardDerivative_norm_bound k hk z)
    (norm_stableVector k z)
  have hrat := positive_energy_ratio_bounds ha hb (norm_nonneg _)
    (show 1≤9*growthBase k by have := growthBase_ge_four k hk; linarith)
    (Real.one_le_exp_iff.mpr (by linarith : 0≤2*χ)) hi.1 hi.2 (h0 hz').2.2.2
  rw [max_eq_right ha, max_eq_right hb]
  exact log_ratio_bound (zero_lt_one.trans_le ha) (zero_lt_one.trans_le hb)
    (zero_lt_one.trans_le (energyRatioBound_ge_one k χ)) hrat.1 hrat.2

lemma ae_unstableEnergy_log_increment (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      |Real.log (max 1 (unstableEnergy k χ (inverseMap k z)))-
        Real.log (max 1 (unstableEnergy k χ z))| ≤ Real.log (energyRatioBound k χ) := by
  have hreg := ae_unstableEnergy_regular k hk χ hχ
  filter_upwards [ae_restrict_mem (measurableSet_spectralGapRegion k hk χ),
    hreg.filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    ((measurePreserving_inverseMap k).quasiMeasurePreserving.ae hreg).filter_mono
      Measure.absolutelyContinuous_restrict.ae_le] with z hz h0 h1
  have hz' : χ < standardLyapunov k hk z := hz
  have ha := (h0 hz').2.1
  have hb := (h1 (by simpa only [standardLyapunov_inverse] using hz')).2.1
  have hi := unit_image_bounds _ (standardInverseDerivative_area k z) (standardInverseDerivative_norm_bound k hk z)
    (norm_unstableVector k z)
  have hrat := positive_energy_ratio_bounds ha hb (norm_nonneg _)
    (show 1≤9*growthBase k by have := growthBase_ge_four k hk; linarith)
    (Real.one_le_exp_iff.mpr (by linarith : 0≤2*χ)) hi.1 hi.2 (h0 hz').2.2.2
  rw [max_eq_right ha, max_eq_right hb]
  exact log_ratio_bound (zero_lt_one.trans_le ha) (zero_lt_one.trans_le hb)
    (zero_lt_one.trans_le (energyRatioBound_ge_one k χ)) hrat.1 hrat.2

lemma log_stableScale (k χ : ℝ) (z : Torus) :
    Real.log (stableScale k χ z)=Real.log (max 1 (stableEnergy k χ z))/2 :=
  Real.log_sqrt (zero_le_one.trans (le_max_left _ _))
lemma log_unstableScale (k χ : ℝ) (z : Torus) :
    Real.log (unstableScale k χ z)=Real.log (max 1 (unstableEnergy k χ z))/2 :=
  Real.log_sqrt (zero_le_one.trans (le_max_left _ _))

theorem ae_lyapunovScale_tempered (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      Tendsto (fun n : ℕ => Real.log (stableScale k χ ((standardMap k)^[n] z))/(n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.log (stableScale k χ ((inverseMap k)^[n] z))/(n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.log (unstableScale k χ ((standardMap k)^[n] z))/(n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.log (unstableScale k χ ((inverseMap k)^[n] z))/(n : ℝ)) atTop (𝓝 0) := by
  have hC : 0<Real.log (energyRatioBound k χ)+1 := by
    have := Real.log_nonneg (energyRatioBound_ge_one k χ)
    linarith
  have hs := ae_both_coboundary_tempered
    (measurePreserving_spectralGapRegion k hk χ) (measurePreserving_inverse_spectralGapRegion k hk χ)
    (standardMap_inverseMap k)
    ((measurable_const.max (measurable_stableEnergy k χ)).log)
    (fun z => Real.log_nonneg (le_max_left _ _)) hC
    ((ae_stableEnergy_log_increment k hk χ hχ).mono fun z hz => hz.trans (by linarith))
  have hu := ae_both_coboundary_tempered
    (measurePreserving_inverse_spectralGapRegion k hk χ) (measurePreserving_spectralGapRegion k hk χ)
    (inverseMap_standardMap k)
    ((measurable_const.max (measurable_unstableEnergy k χ)).log)
    (fun z => Real.log_nonneg (le_max_left _ _)) hC
    ((ae_unstableEnergy_log_increment k hk χ hχ).mono fun z hz => hz.trans (by linarith))
  filter_upwards [hs,hu] with z hz hw
  have hdiv {f : ℕ → ℝ} (hf : Tendsto (fun n : ℕ => f n/(n : ℝ)) atTop (𝓝 0)) :
      Tendsto (fun n : ℕ => f n/2/(n : ℝ)) atTop (𝓝 0) := by
    have hh := hf.div_const 2
    rw [zero_div] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    ring
  exact ⟨by simpa only [log_stableScale] using hdiv hz.1,
    by simpa only [log_stableScale] using hdiv hz.2,
    by simpa only [log_unstableScale] using hdiv hw.2,
    by simpa only [log_unstableScale] using hdiv hw.1⟩

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma planeCoframe_frame (s u : ℂ) {a b : ℝ} (ha : a≠0) (hb : b≠0)
    (hw : wedge s u≠0) :
    (planeCoframe s u a b).comp (planeFrame s u a b)=ContinuousLinearMap.id ℝ ℂ := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, planeCoframe_apply,
    planeFrame_apply, wedge_add_left, wedge_add_right, wedge_smul_left, wedge_smul_right,
    wedge_refl]
  apply Complex.ext <;> dsimp only
  all_goals (field_simp [ha,hb,hw]; ring)

lemma planeCoframe_norm_le {s u : ℂ} (hs : ‖s‖=1) (hu : ‖u‖=1)
    {a b : ℝ} (ha : 1≤a) (hb : 1≤b) (hw : wedge s u≠0) :
    ‖planeCoframe s u a b‖≤4*a*b/|wedge s u| := by
  have ha0 : 0≤a := zero_le_one.trans ha
  have hb0 : 0≤b := zero_le_one.trans hb
  have hw0 : 0 < |wedge s u| := abs_pos.mpr hw
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have h1 : |wedge v u|≤‖v‖ := by simpa only [hu,mul_one] using abs_wedge_le_norm_mul v u
  have h2 : |wedge s v|≤‖v‖ := by simpa only [hs,one_mul] using abs_wedge_le_norm_mul s v
  have hab : a+b≤2*a*b := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  calc
    _ ≤ |(planeCoframe s u a b v).re|+|(planeCoframe s u a b v).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = (2*a*|wedge v u|+2*b*|wedge s v|)/|wedge s u| := by
      simp only [planeCoframe_apply, abs_div, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hb0,
        abs_of_nonneg (by norm_num : (0 : ℝ)≤2)]
      ring
    _ ≤ (2*a*‖v‖+2*b*‖v‖)/|wedge s u| :=
      div_le_div_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_left h1 (by positivity))
        (mul_le_mul_of_nonneg_left h2 (by positivity))) hw0.le
    _ ≤ 4*a*b/|wedge s u| * ‖v‖ := by
      have hh := mul_le_mul_of_nonneg_right hab (by positivity : 0≤2*‖v‖)
      have hh' := div_le_div_of_nonneg_right hh hw0.le
      calc
        _ = ((a+b)*(2*‖v‖))/|wedge s u| := by ring
        _ ≤ ((2*a*b)*(2*‖v‖))/|wedge s u| := hh'
        _ = _ := by ring

lemma lyapunovCoframe_frame (k χ : ℝ) (z : Torus)
    (hw : wedge (stableVector k z) (unstableVector k z)≠0) :
    (lyapunovCoframe k χ z).comp (lyapunovFrame k χ z)=ContinuousLinearMap.id ℝ ℂ :=
  planeCoframe_frame _ _ (ne_of_gt (zero_lt_one.trans_le (stableScale_ge_one k χ z)))
    (ne_of_gt (zero_lt_one.trans_le (unstableScale_ge_one k χ z))) hw

lemma planeCoframe_norm_ge_one {s u : ℂ} (hs : ‖s‖=1) (hu : ‖u‖=1)
    {a b : ℝ} (ha : 1≤a) (hb : 1≤b) (hw : wedge s u≠0) :
    1≤‖planeCoframe s u a b‖ := by
  have hh := (planeCoframe s u a b).opNorm_comp_le (planeFrame s u a b)
  rw [planeCoframe_frame s u (ne_of_gt (zero_lt_one.trans_le ha))
    (ne_of_gt (zero_lt_one.trans_le hb)) hw, ContinuousLinearMap.norm_id] at hh
  apply hh.trans
  simpa only [mul_one] using (mul_le_mul_of_nonneg_left
    (planeFrame_norm_le hs hu ha hb) (norm_nonneg (planeCoframe s u a b)))

lemma planeCoframe_log_bound {s u : ℂ} (hs : ‖s‖=1) (hu : ‖u‖=1)
    {a b : ℝ} (ha : 1≤a) (hb : 1≤b) (hw : wedge s u≠0) :
    0≤Real.log ‖planeCoframe s u a b‖ ∧
      Real.log ‖planeCoframe s u a b‖≤Real.log 4+Real.log a+Real.log b-Real.log |wedge s u| := by
  have hh := planeCoframe_norm_ge_one hs hu ha hb hw
  refine ⟨Real.log_nonneg hh, ?_⟩
  have hle := Real.log_le_log (zero_lt_one.trans_le hh) (planeCoframe_norm_le hs hu ha hb hw)
  have ha0 : a≠0 := ne_of_gt (zero_lt_one.trans_le ha)
  have hb0 : b≠0 := ne_of_gt (zero_lt_one.trans_le hb)
  rwa [Real.log_div (by positivity) (abs_ne_zero.mpr hw),
    Real.log_mul (mul_ne_zero (by norm_num) ha0) hb0, Real.log_mul (by norm_num) ha0] at hle

lemma coframe_tempered {s u : ℕ → ℂ} {a b : ℕ → ℝ}
    (hs : ∀ n, ‖s n‖=1) (hu : ∀ n, ‖u n‖=1)
    (ha : ∀ n, 1≤a n) (hb : ∀ n, 1≤b n) (hw : ∀ n, wedge (s n) (u n)≠0)
    (hta : Tendsto (fun n : ℕ => Real.log (a n)/(n : ℝ)) atTop (𝓝 0))
    (htb : Tendsto (fun n : ℕ => Real.log (b n)/(n : ℝ)) atTop (𝓝 0))
    (htw : Tendsto (fun n : ℕ => Real.log |wedge (s n) (u n)|/(n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log ‖planeCoframe (s n) (u n) (a n) (b n)‖/(n : ℝ)) atTop (𝓝 0) := by
  have hcon : Tendsto (fun n : ℕ => Real.log 4/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim := ((hcon.add hta).add htb).sub htw
  simp only [zero_add, zero_sub, neg_zero] at hlim
  apply squeeze_zero (fun n => div_nonneg (planeCoframe_log_bound (hs n) (hu n) (ha n) (hb n) (hw n)).1 (Nat.cast_nonneg n))
    (fun n => div_le_div_of_nonneg_right (planeCoframe_log_bound (hs n) (hu n) (ha n) (hb n) (hw n)).2 (Nat.cast_nonneg n))
  convert hlim using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  ring

theorem ae_lyapunovCoframe_tempered (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      Tendsto (fun n : ℕ => Real.log ‖lyapunovCoframe k χ ((standardMap k)^[n] z)‖/(n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.log ‖lyapunovCoframe k χ ((inverseMap k)^[n] z)‖/(n : ℝ)) atTop (𝓝 0) := by
  have hf : ∀ᵐ z ∂area, ∀ n : ℕ, 0 < standardLyapunov k hk z →
      wedge (stableVector k ((standardMap k)^[n] z)) (unstableVector k ((standardMap k)^[n] z))≠0 := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [((measurePreserving_standardMap k).iterate n).quasiMeasurePreserving.ae
      (ae_transverseLines k hk)] with z hz hp
    exact hz (by simpa only [standardLyapunov_iterate] using hp)
  have hb : ∀ᵐ z ∂area, ∀ n : ℕ, 0 < standardLyapunov k hk z →
      wedge (stableVector k ((inverseMap k)^[n] z)) (unstableVector k ((inverseMap k)^[n] z))≠0 := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [((measurePreserving_inverseMap k).iterate n).quasiMeasurePreserving.ae
      (ae_transverseLines k hk)] with z hz hp
    exact hz (by simpa only [standardLyapunov_inverse_iterate] using hp)
  filter_upwards [ae_lyapunovScale_tempered k hk χ hχ,
    hf.filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    hb.filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    (ae_angle_tempered k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    ae_restrict_mem (measurableSet_spectralGapRegion k hk χ)] with z hz hf hb hw hp
  have hpos : 0 < standardLyapunov k hk z := hχ.trans_lt hp
  constructor
  · exact coframe_tempered (fun n => norm_stableVector k _) (fun n => norm_unstableVector k _)
      (fun n => stableScale_ge_one k χ _) (fun n => unstableScale_ge_one k χ _)
      (fun n => hf n hpos) hz.1 hz.2.2.1 (hw hpos).1
  · exact coframe_tempered (fun n => norm_stableVector k _) (fun n => norm_unstableVector k _)
      (fun n => stableScale_ge_one k χ _) (fun n => unstableScale_ge_one k χ _)
      (fun n => hb n hpos) hz.2.1 hz.2.2.2 (hw hpos).2

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_MeasurableFrame
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma measurable_complex_mk {X : Type*} [MeasurableSpace X] {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => (⟨f x,g x⟩ : ℂ)) :=
  Complex.equivRealProdCLM.symm.continuous.measurable.comp (hf.prodMk hg)

lemma measurable_wedge {X : Type*} [MeasurableSpace X] {f g : X → ℂ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => wedge (f x) (g x)) :=
  ((Complex.continuous_re.measurable.comp hf).mul (Complex.continuous_im.measurable.comp hg)).sub
    ((Complex.continuous_im.measurable.comp hf).mul (Complex.continuous_re.measurable.comp hg))

lemma measurable_rankOne {X : Type*} [MeasurableSpace X] (L : ℂ →L[ℝ] ℝ)
    {v : X → ℂ} (hv : Measurable v) : Measurable (fun x => L.smulRight (v x)) :=
  ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ) L).measurable.comp hv

lemma planeCoframe_columns (s u : ℂ) (a b : ℝ) :
    planeCoframe s u a b =
      Complex.reCLM.smulRight ⟨2*a*u.im/wedge s u, -2*b*s.im/wedge s u⟩ +
      Complex.imCLM.smulRight ⟨-2*a*u.re/wedge s u, 2*b*s.re/wedge s u⟩ := by
  apply ContinuousLinearMap.ext
  intro v
  rw [planeCoframe_apply]
  apply Complex.ext <;> simp [wedge] <;> ring

lemma measurable_lyapunovFrame (k χ : ℝ) : Measurable (lyapunovFrame k χ) := by
  apply Measurable.add
  · exact measurable_rankOne _ (((measurable_const.mul (measurable_stableScale k χ)).inv).smul
      (measurable_stableVector k))
  · exact measurable_rankOne _ (((measurable_const.mul (measurable_unstableScale k χ)).inv).smul
      (measurable_unstableVector k))

lemma measurable_lyapunovCoframe (k χ : ℝ) : Measurable (lyapunovCoframe k χ) := by
  have hs := measurable_stableVector k
  have hu := measurable_unstableVector k
  have ha := measurable_stableScale k χ
  have hb := measurable_unstableScale k χ
  have hw := measurable_wedge hs hu
  have hsr := Complex.continuous_re.measurable.comp hs
  have hsi := Complex.continuous_im.measurable.comp hs
  have hur := Complex.continuous_re.measurable.comp hu
  have hui := Complex.continuous_im.measurable.comp hu
  change Measurable (fun z => planeCoframe (stableVector k z) (unstableVector k z)
    (stableScale k χ z) (unstableScale k χ z))
  simp only [planeCoframe_columns]
  exact (measurable_rankOne _ (measurable_complex_mk
    (((measurable_const.mul ha).mul hui).div hw)
    (((measurable_const.mul hb).mul hsi).div hw))).add
    (measurable_rankOne _ (measurable_complex_mk
      (((measurable_const.mul ha).mul hur).div hw)
      (((measurable_const.mul hb).mul hsr).div hw)))

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace TemperedControl

variable {X : Type*} [MeasurableSpace X]

lemma orbit_add (e : X ≃ᵐ X) (n m : ℤ) (x : X) :
    orbit e (n+m) x=orbit e n (orbit e m x) := by simp only [orbit,zpow_add,Equiv.Perm.mul_apply]
lemma orbit_nat (e : X ≃ᵐ X) (n : ℕ) (x : X) : orbit e n x=e^[n] x := by
  rw [orbit,zpow_natCast,Equiv.Perm.coe_pow]; rfl
lemma orbit_neg_nat (e : X ≃ᵐ X) (n : ℕ) (x : X) : orbit e (-n) x=e.symm^[n] x := by
  rw [orbit,zpow_neg,zpow_natCast,← inv_pow,Equiv.Perm.coe_pow]; rfl
lemma measurable_orbit (e : X ≃ᵐ X) (n : ℤ) : Measurable (orbit e n) := by
  obtain ⟨n,rfl | rfl⟩ := Int.eq_nat_or_neg n
  · change Measurable (fun x => orbit e (n : ℤ) x)
    simpa only [orbit_nat] using e.measurable.iterate n
  · change Measurable (fun x => orbit e (-(n : ℤ)) x)
    simpa only [orbit_neg_nat] using e.symm.measurable.iterate n

lemma summable_damped_of_log_rate {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    (hrate : Tendsto (fun n : ℕ => Real.log (c n)/(n : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0<ε) : Summable (fun n : ℕ => c n*Real.exp (-ε*(n : ℝ))) := by
  have hgeo := summable_geometric_of_lt_one (Real.exp_pos (-ε/2)).le
    (Real.exp_lt_one_iff.mpr (by linarith : -ε/2<0))
  apply hgeo.of_norm_bounded_eventually_nat
  filter_upwards [(tendsto_order.mp hrate).2 (ε/2) (by linarith), eventually_gt_atTop 0] with n hn hn0
  have hnp : (0 : ℝ)<n := by exact_mod_cast hn0
  have hlt := (div_lt_iff₀ hnp).mp hn
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hc n) (Real.exp_pos _))]
  calc
    _ ≤ Real.exp (ε/2*(n : ℝ))*Real.exp (-ε*(n : ℝ)) :=
      mul_le_mul_of_nonneg_right (by
        calc c n = Real.exp (Real.log (c n)) := (Real.exp_log (hc n)).symm
             _ ≤ _ := Real.exp_le_exp.mpr hlt.le) (Real.exp_pos _).le
    _ = (Real.exp (-ε/2))^n := by rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; ring

lemma summable_control (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0 < c x) {ε : ℝ} (hε : 0<ε)
    {x : X}
    (hf : Tendsto (fun n : ℕ => Real.log (c (e^[n] x))/(n : ℝ)) atTop (𝓝 0))
    (hb : Tendsto (fun n : ℕ => Real.log (c (e.symm^[n] x))/(n : ℝ)) atTop (𝓝 0)) :
    Summable (fun n : ℤ => c (orbit e n x)*weight ε n) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa only [orbit_nat,weight,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using
      summable_damped_of_log_rate (fun n => hc _) hf hε
  · simpa only [orbit_neg_nat,weight,Int.cast_neg,Int.cast_natCast,abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using summable_damped_of_log_rate (fun n => hc _) hb hε

lemma control_ge (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0 ≤ c x) (ε : ℝ) (x : X)
    (hs : Summable (fun n : ℤ => c (orbit e n x)*weight ε n)) : c x ≤ control e c ε x := by
  have hh := hs.le_tsum 0 (fun n _ => mul_nonneg (hc _) (Real.exp_pos _).le)
  simpa only [control,orbit_zero,weight,Int.cast_zero,abs_zero,mul_zero,Real.exp_zero,mul_one] using hh

lemma weight_shift_bound {ε : ℝ} (hε : 0≤ε) (n m : ℤ) :
    weight ε n≤Real.exp (ε*|(m : ℝ)|)*weight ε (n+m) := by
  unfold weight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (abs_add_le (n : ℝ) (m : ℝ)) hε
  rw [Int.cast_add]
  linarith

lemma summable_control_orbit (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0 ≤ c x)
    {ε : ℝ} (hε : 0≤ε) {x : X}
    (hs : Summable (fun n : ℤ => c (orbit e n x)*weight ε n)) (m : ℤ) :
    Summable (fun n : ℤ => c (orbit e n (orbit e m x))*weight ε n) := by
  have hshift : Summable (fun n : ℤ => c (orbit e (n+m) x)*weight ε (n+m)) :=
    (Equiv.addRight m).summable_iff.mpr hs
  apply (hshift.mul_left (Real.exp (ε*|(m : ℝ)|))).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hc _)
    (show 0≤weight ε n from (Real.exp_pos _).le)), ← orbit_add]
  calc
    _ ≤ c (orbit e (n+m) x)*(Real.exp (ε*|(m : ℝ)|)*weight ε (n+m)) :=
      mul_le_mul_of_nonneg_left (weight_shift_bound hε n m) (hc _)
    _ = _ := by ring

lemma control_orbit_le (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0 ≤ c x)
    {ε : ℝ} (hε : 0≤ε) {x : X}
    (hs : Summable (fun n : ℤ => c (orbit e n x)*weight ε n)) (m : ℤ) :
    control e c ε (orbit e m x)≤Real.exp (ε*|(m : ℝ)|)*control e c ε x := by
  have hshift : Summable (fun n : ℤ => c (orbit e (n+m) x)*weight ε (n+m)) :=
    (Equiv.addRight m).summable_iff.mpr hs
  have hle := Summable.tsum_le_tsum (fun n : ℤ => show
      c (orbit e n (orbit e m x))*weight ε n≤
        Real.exp (ε*|(m : ℝ)|)*(c (orbit e (n+m) x)*weight ε (n+m)) from by
    rw [← orbit_add]
    calc
      _ ≤ c (orbit e (n+m) x)*(Real.exp (ε*|(m : ℝ)|)*weight ε (n+m)) :=
        mul_le_mul_of_nonneg_left (weight_shift_bound hε n m) (hc _)
      _ = _ := by ring)
    (summable_control_orbit e hc hε hs m) (hshift.mul_left _)
  have heq := (Equiv.addRight m).tsum_eq (fun n : ℤ => c (orbit e n x)*weight ε n)
  change (∑' n : ℤ, c (orbit e (n+m) x)*weight ε (n+m))=control e c ε x at heq
  rw [tsum_mul_left, heq] at hle
  exact hle

lemma radius_mul_control_le (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0 ≤ c x)
    (ε : ℝ) (x : X) (hs : Summable (fun n : ℤ => c (orbit e n x)*weight ε n)) :
    radius e c ε x*c x≤1 := by
  have hh := control_ge e hc ε x hs
  have h0 := control_nonneg e hc ε x
  unfold radius
  calc
    _ ≤ (1+control e c ε x)⁻¹*(1+control e c ε x) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr (by linarith))
    _ = 1 := inv_mul_cancel₀ (by linarith)

lemma radius_orbit_lower (e : X ≃ᵐ X) {c : X → ℝ} (hc : ∀ x, 0 ≤ c x)
    {ε : ℝ} (hε : 0≤ε) {x : X}
    (hs : Summable (fun n : ℤ => c (orbit e n x)*weight ε n)) (m : ℤ) :
    Real.exp (-ε*|(m : ℝ)|)*radius e c ε x ≤ radius e c ε (orbit e m x) := by
  have hle := control_orbit_le e hc hε hs m
  have hexp : 1≤Real.exp (ε*|(m : ℝ)|) := Real.one_le_exp_iff.mpr (by positivity)
  have hb : 1+control e c ε (orbit e m x)≤Real.exp (ε*|(m : ℝ)|)*(1+control e c ε x) := by nlinarith
  have hp : 0<1+control e c ε (orbit e m x) := by have := control_nonneg e hc ε (orbit e m x); linarith
  have hh := one_div_le_one_div_of_le hp hb
  simpa only [radius, one_div, mul_inv, ← Real.exp_neg, neg_mul] using hh

lemma measurable_control (e : X ≃ᵐ X) {c : X → ℝ} (hc : Measurable c) (ε : ℝ) :
    Measurable (control e c ε) := Measurable.tsum fun n => (hc.comp (measurable_orbit e n)).mul_const _
lemma measurable_radius (e : X ≃ᵐ X) {c : X → ℝ} (hc : Measurable c) (ε : ℝ) :
    Measurable (radius e c ε) := (measurable_const.add (measurable_control e hc ε)).inv

end TemperedControl
end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma diagonalPlane_apply (α β : ℝ) (v : ℂ) :
    diagonalPlane α β v = ⟨α*v.re, β*v.im⟩ := by
  apply Complex.ext <;> simp [diagonalPlane] <;> ring

lemma planeFrame_normal_form (D : ℂ →L[ℝ] ℂ) {s u t v : ℂ}
    (ht : ‖t‖=1) (hv : ‖v‖=1) (hw : wedge t v≠0)
    (hs : wedge t (D s)=0) (hu : wedge v (D u)=0)
    {a b c d : ℝ} (ha : a≠0) (hb : b≠0) :
    (planeCoframe t v c d).comp (D.comp (planeFrame s u a b)) =
      diagonalPlane (dot t (D s)*c/a) (dot v (D u)*d/b) := by
  apply ContinuousLinearMap.ext
  intro x
  have he1 := unit_collinear_eq_smul ht hs
  have he2 := unit_collinear_eq_smul hv hu
  simp only [ContinuousLinearMap.comp_apply, planeFrame_apply, map_add, map_smul]
  conv_lhs => rw [he1, he2]
  simp only [planeCoframe_apply, wedge_smul_left,
    wedge_smul_right, wedge_refl, diagonalPlane_apply]
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul]
  all_goals (field_simp [ha,hb,hw]; ring)

lemma collinear_image_norm (D : ℂ →L[ℝ] ℂ) {s t : ℂ} (ht : ‖t‖=1)
    (hcov : wedge t (D s)=0) : ‖D s‖=|dot t (D s)| := by
  have he := unit_collinear_eq_smul ht hcov
  conv_lhs => rw [he, norm_smul, Real.norm_eq_abs, ht, mul_one]

lemma energy_contraction {a b ρ χ : ℝ} (ha : 0<a) (hb : 0≤b) (hr : 0≤ρ)
    (he : a^2=1+Real.exp (2*χ)*ρ^2*b^2) :
    ρ*b/a≤Real.exp (-χ) := by
  have hexp : Real.exp (2*χ)=(Real.exp χ)^2 := by rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hs : (Real.exp χ*ρ*b)^2≤a^2 := by rw [hexp] at he; nlinarith
  have hle : Real.exp χ*ρ*b≤a := (sq_le_sq₀ (by positivity) ha.le).mp hs
  have hmain : ρ*b≤Real.exp (-χ)*a := by
    have hh := mul_le_mul_of_nonneg_left hle (Real.exp_pos (-χ)).le
    have hid : Real.exp (-χ)*Real.exp χ=1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      _ = Real.exp (-χ)*(Real.exp χ*ρ*b) := by rw [← mul_assoc, ← mul_assoc, hid, one_mul]
      _ ≤ _ := hh
  exact (div_le_iff₀ ha).mpr hmain

lemma ae_lyapunov_normal_form (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      (lyapunovCoframe k χ (standardMap k z)).comp
        ((standardDerivative k z).comp (lyapunovFrame k χ z)) =
      diagonalPlane (stableMultiplier k χ z) (unstableMultiplier k χ z) := by
  filter_upwards [ae_restrict_mem (measurableSet_spectralGapRegion k hk χ),
    ((measurePreserving_standardMap k).quasiMeasurePreserving.ae (ae_transverseLines k hk)).filter_mono
      Measure.absolutelyContinuous_restrict.ae_le,
    (ae_stableVector_covariant k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    (ae_unstableVector_covariant k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le] with z hz htr hs hu
  have hp : 0 < standardLyapunov k hk z := hχ.trans_lt hz
  exact planeFrame_normal_form _ (norm_stableVector k _) (norm_unstableVector k _)
    (htr (by simpa only [standardLyapunov_invariant] using hp)) (hs hp) (hu hp)
    (ne_of_gt (zero_lt_one.trans_le (stableScale_ge_one k χ z)))
    (ne_of_gt (zero_lt_one.trans_le (unstableScale_ge_one k χ z)))

lemma ae_stableMultiplier_bound (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      |stableMultiplier k χ z|≤Real.exp (-χ) := by
  have hreg := ae_stableEnergy_regular k hk χ hχ
  filter_upwards [ae_restrict_mem (measurableSet_spectralGapRegion k hk χ),
    hreg.filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    ((measurePreserving_standardMap k).quasiMeasurePreserving.ae hreg).filter_mono
      Measure.absolutelyContinuous_restrict.ae_le,
    (ae_stableVector_covariant k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le] with z hz h0 h1 hc
  have hz' : χ < standardLyapunov k hk z := hz
  have he := (h0 hz').2.2.2
  rw [← (h0 hz').2.2.1,
    ← (h1 (by simpa only [standardLyapunov_invariant] using hz')).2.2.1] at he
  have ha := zero_lt_one.trans_le (stableScale_ge_one k χ z)
  have hb := zero_lt_one.trans_le (stableScale_ge_one k χ (standardMap k z))
  have hn := collinear_image_norm (standardDerivative k z) (norm_stableVector k _) (hc (hχ.trans_lt hz'))
  simpa only [stableMultiplier, abs_div, abs_mul, abs_of_pos ha, abs_of_pos hb, ← hn] using
    energy_contraction ha hb.le (norm_nonneg _) he

lemma covariant_inverse_norm_product (D E : ℂ →L[ℝ] ℂ) (hDE : ∀ x, E (D x)=x)
    {s t : ℂ} (hs : ‖s‖=1) (ht : ‖t‖=1) (hcov : wedge t (D s)=0) :
    ‖D s‖*‖E t‖=1 := by
  have he := unit_collinear_eq_smul ht hcov
  have hn := collinear_image_norm D ht hcov
  calc
    _ = ‖E (D s)‖ := by conv_rhs => rw [he, map_smul, norm_smul, Real.norm_eq_abs, ← hn]
    _ = 1 := by rw [hDE,hs]

lemma ae_unstableMultiplier_bound (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      Real.exp χ≤|unstableMultiplier k χ z| := by
  have hreg := ae_unstableEnergy_regular k hk χ hχ
  filter_upwards [ae_restrict_mem (measurableSet_spectralGapRegion k hk χ),
    hreg.filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    ((measurePreserving_standardMap k).quasiMeasurePreserving.ae hreg).filter_mono
      Measure.absolutelyContinuous_restrict.ae_le,
    (ae_unstableVector_covariant k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le] with z hz h0 h1 hc
  have hz' : χ < standardLyapunov k hk z := hz
  have hnext : χ < standardLyapunov k hk (standardMap k z) := by simpa only [standardLyapunov_invariant] using hz'
  have he := (h1 hnext).2.2.2
  rw [inverseMap_standardMap, ← (h0 hz').2.2.1, ← (h1 hnext).2.2.1] at he
  have ha := zero_lt_one.trans_le (unstableScale_ge_one k χ (standardMap k z))
  have hb := zero_lt_one.trans_le (unstableScale_ge_one k χ z)
  have hcon := energy_contraction ha hb.le (norm_nonneg _) he
  have hn := collinear_image_norm (standardDerivative k z) (norm_unstableVector k _) (hc (hχ.trans_lt hz'))
  have hprod := covariant_inverse_norm_product (standardDerivative k z)
    (standardInverseDerivative k (standardMap k z)) (standardInverseDerivative_standardDerivative k z)
    (norm_unstableVector k _) (norm_unstableVector k _) (hc (hχ.trans_lt hz'))
  have hh := mul_le_mul_of_nonneg_left hcon (norm_nonneg (standardDerivative k z (unstableVector k z)))
  have hbasic : unstableScale k χ z / unstableScale k χ (standardMap k z) ≤
      ‖standardDerivative k z (unstableVector k z)‖*Real.exp (-χ) := by
    simpa only [← mul_div_assoc, ← mul_assoc, hprod, one_mul] using hh
  have hexp : Real.exp χ*Real.exp (-χ)=1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hh' := mul_le_mul_of_nonneg_left ((div_le_iff₀ ha).mp hbasic) (Real.exp_pos χ).le
  have hfinal : Real.exp χ*unstableScale k χ z ≤
      ‖standardDerivative k z (unstableVector k z)‖*unstableScale k χ (standardMap k z) := by
    calc
      _ ≤ Real.exp χ*(‖standardDerivative k z (unstableVector k z)‖*Real.exp (-χ)*unstableScale k χ (standardMap k z)) := hh'
      _ = (Real.exp χ*Real.exp (-χ))*(‖standardDerivative k z (unstableVector k z)‖*unstableScale k χ (standardMap k z)) := by ring
      _ = _ := by rw [hexp,one_mul]
  simpa only [unstableMultiplier, abs_div, abs_mul, abs_of_pos ha, abs_of_pos hb, ← hn] using
    (le_div_iff₀ hb).mpr hfinal

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma log_max_one_rate {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => Real.log (a n)/(n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log (max 1 (a n))/(n : ℝ)) atTop (𝓝 0) := by
  have hlim := ha.abs
  rw [abs_zero] at hlim
  apply squeeze_zero (fun n => div_nonneg (Real.log_nonneg (le_max_left _ _)) (Nat.cast_nonneg n))
    (fun n => show Real.log (max 1 (a n))/(n : ℝ)≤|Real.log (a n)/(n : ℝ)| from ?_) hlim
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  by_cases hh : 1≤a n
  · rw [max_eq_right hh]
    exact le_abs_self _
  · rw [max_eq_left (not_le.mp hh).le,Real.log_one]
    exact abs_nonneg _

lemma measurable_chartControl (k χ : ℝ) : Measurable (chartControl k χ) :=
  measurable_const.max (measurable_lyapunovCoframe k χ).norm
lemma measurable_chartRadius (k χ ε : ℝ) : Measurable (chartRadius k χ ε) :=
  TemperedControl.measurable_radius _ (measurable_chartControl k χ) ε

lemma ae_chartControl_summable (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) (ε : ℝ) (hε : 0<ε) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      Summable (fun n : ℤ => chartControl k χ (TemperedControl.orbit (standardMap_measurableEquiv k) n z)*
        TemperedControl.weight ε n) := by
  filter_upwards [ae_lyapunovCoframe_tempered k hk χ hχ] with z hz
  exact TemperedControl.summable_control _
    (fun z => zero_lt_one.trans_le (chartControl_ge_one k χ z)) hε
    (log_max_one_rate hz.1) (log_max_one_rate hz.2)

theorem ae_chartRadius_control (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0≤χ) (ε : ℝ) (hε : 0<ε) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      chartRadius k χ ε z*‖lyapunovCoframe k χ z‖≤1 ∧
      Real.exp (-ε)*chartRadius k χ ε z ≤ chartRadius k χ ε (standardMap k z) ∧
      Real.exp (-ε)*chartRadius k χ ε (standardMap k z) ≤ chartRadius k χ ε z := by
  filter_upwards [ae_chartControl_summable k hk χ hχ ε hε] with z hz
  have hc : ∀ z, 0 ≤ chartControl k χ z := fun z => zero_le_one.trans (chartControl_ge_one k χ z)
  have hs := TemperedControl.summable_control_orbit (standardMap_measurableEquiv k) hc hε.le hz 1
  have h0 := TemperedControl.radius_mul_control_le (standardMap_measurableEquiv k) hc ε z hz
  have h1 := TemperedControl.radius_orbit_lower (standardMap_measurableEquiv k) hc hε.le hz 1
  have h2 := TemperedControl.radius_orbit_lower (standardMap_measurableEquiv k) hc hε.le hs (-1)
  refine ⟨?_,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left (le_max_right _ _) (chartRadius_pos k χ ε z).le).trans h0
  · simpa only [chartRadius,Int.cast_one,abs_one,mul_one,TemperedControl.orbit_one,
      standardMap_measurableEquiv_apply] using h1
  · simpa only [chartRadius,TemperedControl.orbit_neg_one,TemperedControl.orbit_one,
      standardMap_measurableEquiv_apply, standardMap_measurableEquiv_symm_apply, inverseMap_standardMap,
      Int.cast_neg,Int.cast_one,abs_neg,abs_one,mul_one] using h2

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_SmoothRemainder
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal

lemma flatInverse_frame {q : ℝ} (hq : q≠0) {F C : ℂ →L[ℝ] ℂ}
    (hCF : C.comp F=ContinuousLinearMap.id ℝ ℂ) (v : RealPlane) :
    flatInverse q C (flatFrame q F v)=v := by
  have hh : C (F (pairToComplex v))=pairToComplex v := congrArg (fun D : ℂ →L[ℝ] ℂ => D (pairToComplex v)) hCF
  simp only [flatInverse,flatFrame,ContinuousLinearMap.comp_apply,smul_apply,map_smul,
    hh,smul_smul,mul_inv_cancel₀ hq,one_smul,complexToPair_pairToComplex]

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_PerronStability
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma tangentReversal_norm_le (w : ℂ) : ‖tangentReversal w‖≤3*‖w‖ := by
  have hh := Complex.norm_le_abs_re_add_abs_im (tangentReversal w)
  simp only [tangentReversal_re,tangentReversal_im,abs_neg] at hh
  have hh' := abs_sub w.re w.im
  have hr := Complex.abs_re_le_norm w
  have hi := Complex.abs_im_le_norm w
  linarith
lemma tangentReversal_ne_zero {w : ℂ} (hw : w≠0) : tangentReversal w≠0 := by
  intro he
  have hh := congrArg tangentReversal he
  exact hw (by simpa only [tangentReversal_involutive,map_zero] using hh)

lemma measurePreserving_reversal_spectralGapRegion (k : ℝ) (hk : 0≤k) (χ : ℝ) :
    MeasurePreserving standardReversal (area.restrict (spectralGapRegion k hk χ))
      (area.restrict (spectralGapRegion k hk χ)) := by
  have hh := measurePreserving_standardReversal.restrict_preimage (measurableSet_spectralGapRegion k hk χ)
  have he : standardReversal ⁻¹' spectralGapRegion k hk χ =ᵐ[area] spectralGapRegion k hk χ := by
    filter_upwards [standardLyapunov_reversal_ae k hk] with z hz
    change (χ < standardLyapunov k hk (standardReversal z))=(χ < standardLyapunov k hk z)
    rw [hz]
  rwa [Measure.restrict_congr_set he] at hh

lemma ae_stableVector_reversal_unstable (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (unstableVector k z) (tangentReversal (stableVector k (standardReversal z)))=0 := by
  filter_upwards [standardLyapunov_reversal_ae k hk,ae_unstableVector_growth k hk,
    measurePreserving_standardReversal.quasiMeasurePreserving.ae (ae_stableVector_growth k hk)] with z he hu hs hp
  have hu0 := PlaneLyapunov.norm_tendsto_zero_of_negative_growth _
    (standardInverseDerivativeProduct_area k z) (hu hp) (by linarith)
  have hs0 := PlaneLyapunov.norm_tendsto_zero_of_negative_growth _
    (standardDerivativeProduct_area k (standardReversal z)) (hs (by rwa [he])) (by rw [he]; linarith)
  apply contracting_wedge_zero _ (standardInverseDerivativeProduct_area k z) hu0
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (by simpa only [mul_zero] using Tendsto.const_mul 3 hs0)
  rw [standardInverseDerivativeProduct_conjugate]
  simp only [ContinuousLinearMap.comp_apply,tangentReversal_involutive]
  exact tangentReversal_norm_le _

lemma ae_reversal_tangent_transverse (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area, 0 < standardLyapunov k hk z →
      wedge (stableVector k z) (tangentReversal (stableVector k (standardReversal z)))≠0 := by
  filter_upwards [ae_stableVector_reversal_unstable k hk,ae_transverseLines k hk] with z hu hs hp
  have he := unit_collinear_eq_smul (norm_unstableVector k z) (hu hp)
  have hc : dot (unstableVector k z) (tangentReversal (stableVector k (standardReversal z)))≠0 := by
    intro hz
    rw [hz,zero_smul] at he
    exact tangentReversal_ne_zero (stableVector_ne_zero k _) he
  rw [he,wedge_smul_right]
  exact mul_ne_zero hc (hs hp)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_FineCharts
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

lemma fineInverse_frame (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus)
    (hw : wedge (stableVector k z) (unstableVector k z)≠0) (v : RealPlane) :
    fineInverse k χ ε δ z (fineFrame k χ ε δ z v)=v :=
  flatInverse_frame (ne_of_gt (fineSize_pos k χ ε hδ z)) (lyapunovCoframe_frame k χ z hw) v
lemma ae_fineRegular (k : ℝ) (hk : 0≤k) {χ ε : ℝ} (hχ : 0<χ) (hε : 0<ε) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ), FineRegular k χ ε z := by
  filter_upwards [ae_restrict_mem (measurableSet_spectralGapRegion k hk χ),
    (ae_transverseLines k hk).filter_mono Measure.absolutelyContinuous_restrict.ae_le,
    ae_lyapunov_normal_form k hk χ hχ.le,ae_stableMultiplier_bound k hk χ hχ.le,
    ae_unstableMultiplier_bound k hk χ hχ.le,ae_chartRadius_control k hk χ hχ.le ε hε]
    with z hz ht hn hs hu hr
  exact ⟨ht (hχ.trans hz),hn,hs,hu,hr⟩
lemma ae_fineRegular_all_iterates (k : ℝ) (hk : 0≤k) {χ ε : ℝ} (hχ : 0<χ) (hε : 0<ε) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ),
      ∀ n : ℕ, FineRegular k χ ε ((standardMap k)^[n] z) ∧ FineRegular k χ ε ((inverseMap k)^[n] z) := by
  rw [ae_all_iff]
  intro n
  exact (((measurePreserving_spectralGapRegion k hk χ).iterate n).quasiMeasurePreserving.ae
    (ae_fineRegular k hk hχ hε)).and
    (((measurePreserving_inverse_spectralGapRegion k hk χ).iterate n).quasiMeasurePreserving.ae
    (ae_fineRegular k hk hχ hε))

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
lemma codingScale_pos (k ε : ℝ) {δ : ℝ} (hδ : 0<δ) : 0 < codingScale k ε δ := by
  unfold codingScale
  exact div_pos (lt_min zero_lt_one (fineScale_pos k ε hδ)) (by positivity)
lemma codingRadius_pos (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (z : Torus) : 0 < codingRadius k χ ε δ z :=
  mul_pos (codingScale_pos k ε hδ) (sq_pos_of_pos (chartRadius_pos k χ ε z))

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_PhysicalVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma complexRep_projection_of_cell {z : ℂ} (hz : z∈complexCell) : complexRep (complexProjection z)=z := by
  apply Complex.ext
  · exact circleRep_coe_of_mem hz.1
  · exact circleRep_coe_of_mem hz.2
lemma measurePreserving_complexProjection_cell :
    MeasurePreserving complexProjection (volume.restrict complexCell) area := by
  have hp := (AddCircle.measurePreserving_mk (1 : ℝ) 0).prod (AddCircle.measurePreserving_mk (1 : ℝ) 0)
  simp only [zero_add] at hp
  rw [←restrict_Ico_eq_restrict_Ioc,Measure.prod_restrict] at hp
  have hc := Complex.volume_preserving_equiv_real_prod.restrict_preimage (measurableSet_Ico.prod measurableSet_Ico :
    MeasurableSet (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1))
  exact hp.comp hc
lemma area_le_volume_of_complexRep_subset {S : Set Torus} (hS : MeasurableSet S) {V : Set ℂ}
    (hsub : ∀ z∈S,complexRep z∈V) : area S≤volume V := by
  rw [←measurePreserving_complexProjection_cell.measure_preimage hS.nullMeasurableSet,
    Measure.restrict_apply (measurePreserving_complexProjection_cell.measurable hS)]
  apply measure_mono
  intro z hz
  have hh := hsub (complexProjection z) hz.1
  rwa [complexRep_projection_of_cell hz.2] at hh

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Holonomy_FineStableGeometry
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal

lemma measurable_compact_continuity_block {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → Y} (hf : Measurable f)
    {A : Set X} (hA : MeasurableSet A) {r : ℝ≥0∞} (hr : r<μ A) :
    ∃ K : Set X, K⊆A ∧ IsCompact K ∧ ContinuousOn f K ∧ r<μ K := by
  let g : X → X×Y := fun x => (x,f x)
  have hg : Measurable g := measurable_id.prodMk hf
  let G : Set (X×Y) := {p | p.1∈A ∧ p.2=f p.1}
  have hG : MeasurableSet G :=
    (hA.preimage measurable_fst).inter (measurableSet_eq_fun measurable_snd (hf.comp measurable_fst))
  have hpre : g ⁻¹' G=A := by ext x; simp [g,G]
  have hmass : μ.map g G=μ A := by rw [Measure.map_apply hg hG,hpre]
  obtain ⟨C,hCG,hC,hCr⟩ := hG.exists_lt_isCompact (μ := μ.map g) (r := r) (by simpa only [hmass] using hr)
  let K : Set X := Prod.fst '' C
  have hK : IsCompact K := hC.image continuous_fst
  have hKA : K⊆A := by rintro x ⟨p,hp,rfl⟩; exact (hCG hp).1
  have hCK : g ⁻¹' C=K := by
    ext x
    constructor
    · intro hx; exact ⟨g x,hx,rfl⟩
    · rintro ⟨p,hp,hpx⟩
      have he : g x=p := by
        apply Prod.ext
        · exact hpx.symm
        · change f x=p.2; rw [←hpx]; exact (hCG hp).2.symm
      simpa only [mem_preimage,he] using hp
  have hmeasure : μ.map g C=μ K := by rw [Measure.map_apply hg hC.measurableSet,hCK]
  refine ⟨K,hKA,hK,?_,by rwa [←hmeasure]⟩
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let q : C → K := fun p => ⟨p.1.1,⟨p.1,p.2,rfl⟩⟩
  have hq : Continuous q := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hqs : Function.Surjective q := by
    rintro ⟨x,p,hp,hpx⟩
    refine ⟨⟨p,hp⟩,?_⟩
    exact Subtype.ext hpx
  have hquot := IsQuotientMap.of_surjective_continuous hqs hq
  rw [continuousOn_iff_continuous_domRestrict]
  apply hquot.continuous_iff.mpr
  have he : (fun x : K => f x) ∘ q=(fun p : C => p.1.2) := by
    funext p
    exact (hCG p.2).2.symm
  change Continuous ((fun x : K => f x) ∘ q)
  rw [he]
  exact continuous_snd.comp continuous_subtype_val

lemma measurable_lyapunovChartData (k χ ε : ℝ) : Measurable (lyapunovChartData k χ ε) :=
  (measurable_lyapunovFrame k χ).prodMk
    ((measurable_lyapunovCoframe k χ).prodMk (measurable_chartRadius k χ ε))
lemma measurable_orbitChartData (k χ ε : ℝ) : Measurable (orbitChartData k χ ε) :=
  Measurable.of_eval fun n =>
    ((measurable_lyapunovChartData k χ ε).comp ((measurePreserving_standardMap k).measurable.iterate n)).prodMk
      ((measurable_lyapunovChartData k χ ε).comp ((measurePreserving_inverseMap k).measurable.iterate n))

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma continuous_complexProjection : Continuous complexProjection :=
  ((AddCircle.continuous_mk' (1 : ℝ)).comp Complex.continuous_re).prodMk
    ((AddCircle.continuous_mk' (1 : ℝ)).comp Complex.continuous_im)

lemma continuous_fineFrame_of_data {X : Type*} [TopologicalSpace X] (k χ ε δ : ℝ)
    (z : X → Torus) (h : Continuous (fun x => lyapunovChartData k χ ε (z x))) :
    Continuous (fun x => fineFrame k χ ε δ (z x)) :=
  ((continuous_const.mul h.snd.snd).smul h.fst).clm_comp continuous_const
lemma continuous_fineInverse_of_data {X : Type*} [TopologicalSpace X] (k χ ε δ : ℝ) (hδ : 0<δ)
    (z : X → Torus) (h : Continuous (fun x => lyapunovChartData k χ ε (z x))) :
    Continuous (fun x => fineInverse k χ ε δ (z x)) :=
  continuous_const.clm_comp (((continuous_const.mul h.snd.snd).inv₀
    (fun x => (fineSize_pos k χ ε hδ (z x)).ne')).smul h.snd.fst)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Holonomy_FinePlaqueParameters
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

lemma fine_holonomy_parameters {χ τ : ℝ} (hχ : 0<χ) (hτ : 0<τ) :
    ∃ ε δ : ℝ, 0<ε ∧ 0<δ ∧ δ≤1/2 ∧ Real.exp (-χ+ε)+δ<1 ∧
      Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1 ∧
      Real.exp (-χ+ε)*δ/(1-Real.exp (-χ+ε))≤τ := by
  let ε := χ/10
  let ℓ := Real.exp (-χ+ε)
  let ρ := Real.exp (-χ/2)
  have hε : 0<ε := by dsimp [ε]; positivity
  have hℓ0 : 0<ℓ := Real.exp_pos _
  have hℓρ : ℓ<ρ := Real.exp_lt_exp.mpr (by dsimp [ε]; linarith)
  have hρ1 : ρ<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hℓ1 : ℓ<1 := hℓρ.trans hρ1
  let δ := min ((ρ-ℓ)/2) (min (τ*(1-ℓ)/2) (1/2))
  have hδ : 0<δ := lt_min (by linarith) (lt_min (by positivity) (by norm_num))
  have hdρ : δ≤(ρ-ℓ)/2 := min_le_left _ _
  have hdτ : δ≤τ*(1-ℓ)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hd1 : δ≤1/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hqρ : ℓ+δ≤ρ := by linarith
  have hslow : Real.exp (4*ε)*ρ<1 := by
    rw [←Real.exp_add]
    exact Real.exp_lt_one_iff.mpr (by dsimp [ε]; linarith)
  refine ⟨ε,δ,hε,hδ,hd1,hqρ.trans_lt hρ1,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left hqρ (Real.exp_pos _).le).trans_lt hslow
  · apply (div_le_iff₀ (sub_pos.mpr hℓ1)).mpr
    have hb := mul_le_mul_of_nonneg_right hℓ1.le hδ.le
    nlinarith

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Holonomy_CompactHolonomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal

lemma complexRep_norm_le_two (z : Torus) : ‖complexRep z‖≤2 := by
  have h1 := circleRep_mem z.1
  have h2 := circleRep_mem z.2
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  change |circleRep z.1|+|circleRep z.2|≤2
  rw [abs_of_nonneg h1.1,abs_of_nonneg h2.1]
  linarith [h1.2,h2.2]

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal

lemma positive_compact_neighborhood {C : Set ℂ} (hC : IsCompact C) (hpos : 0<volume C) :
    ∃ w∈C, ∀ P : ℂ → Prop, (∀ᶠ v in 𝓝[C] w, P v) →
      ∃ K : Set ℂ, K⊆C ∧ IsCompact K ∧ 0<volume K ∧ ∀ v∈K,P v := by
  have hpos' : 0<(volume.restrict C) C := by simpa only [Measure.restrict_apply hC.measurableSet,inter_self] using hpos
  obtain ⟨w,hwC,hwSupp⟩ := Measure.nonempty_inter_support_of_pos hpos'
  refine ⟨w,hwC,?_⟩
  intro P hP
  obtain ⟨a,ha,hak⟩ := Metric.mem_nhdsWithin_iff.mp hP
  let K := C∩Metric.closedBall w (a/2)
  have hb : Metric.ball w (a/2)∈𝓝 w := Metric.ball_mem_nhds _ (by linarith)
  have hbp : 0<volume (Metric.ball w (a/2)∩C) := by
    have h := ((Measure.mem_support_iff_forall w).mp hwSupp) _ hb
    simpa only [Measure.restrict_apply measurableSet_ball] using h
  refine ⟨K,inter_subset_left,hC.inter_right Metric.isClosed_closedBall,?_,?_⟩
  · apply hbp.trans_le (measure_mono _)
    rintro v ⟨hv,hvC⟩
    exact ⟨hvC,Metric.ball_subset_closedBall hv⟩
  · intro v hv
    apply hak
    exact ⟨(Metric.mem_ball).mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hv.2) (by linarith)),hv.1⟩

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_BoundedBirkhoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology

lemma ae_unstableVector_reversal_stable (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area,0 < standardLyapunov k hk z →
      wedge (unstableVector k (standardReversal z)) (tangentReversal (stableVector k z))=0 := by
  filter_upwards [measurePreserving_standardReversal.quasiMeasurePreserving.ae
    (ae_stableVector_reversal_unstable k hk),standardLyapunov_reversal_ae k hk] with z hz he hp
  simpa only [standardReversal_involutive] using hz (by rwa [he])

lemma fineSize_eq_delta_mul (k χ ε δ : ℝ) (z : Torus) :
    fineSize k χ ε δ z=δ*fineSize k χ ε 1 z := by
  unfold fineSize fineScale
  ring

lemma fineFrame_eq_delta_smul (k χ ε δ : ℝ) (z : Torus) (p : RealPlane) :
    fineFrame k χ ε δ z p=δ•fineFrame k χ ε 1 z p := by
  simp only [fineFrame,flatFrame,ContinuousLinearMap.comp_apply,smul_apply,
    fineSize_eq_delta_mul k χ ε δ z,smul_smul]

lemma fineInverse_eq_inv_delta_smul (k χ ε δ : ℝ) (z : Torus) (p : ℂ) :
    fineInverse k χ ε δ z p=δ⁻¹•fineInverse k χ ε 1 z p := by
  simp only [fineInverse,flatInverse,ContinuousLinearMap.comp_apply,smul_apply,
    fineSize_eq_delta_mul k χ ε δ z,mul_inv_rev,map_smul,smul_smul]
  congr 1
  ring

lemma fine_relative_frame_independent_delta (k χ ε : ℝ) {δ : ℝ} (hδ : δ≠0)
    (z z' : Torus) (T : ℂ →L[ℝ] ℂ) (p : RealPlane) :
    fineInverse k χ ε δ z (T (fineFrame k χ ε δ z' p))=
      fineInverse k χ ε 1 z (T (fineFrame k χ ε 1 z' p)) := by
  rw [fineFrame_eq_delta_smul,map_smul,map_smul,fineInverse_eq_inv_delta_smul,smul_smul,mul_inv_cancel₀ hδ,one_smul]

lemma tangentReversal_wedge (s u : ℂ) : wedge (tangentReversal s) (tangentReversal u)=-wedge s u := by
  simp only [wedge,tangentReversal_re,tangentReversal_im]
  ring

lemma fineFrame_first (k χ ε δ : ℝ) (z : Torus) :
    fineFrame k χ ε δ z (1,0)=(fineSize k χ ε δ z/(2*stableScale k χ z))•stableVector k z := by
  simp only [fineFrame,flatFrame,ContinuousLinearMap.comp_apply,smul_apply,
    lyapunovFrame,planeFrame_apply,pairToComplex_apply,
    zero_div,zero_smul,add_zero,smul_smul]
  congr 1
  ring

lemma fineFrame_second (k χ ε δ : ℝ) (z : Torus) :
    fineFrame k χ ε δ z (0,1)=(fineSize k χ ε δ z/(2*unstableScale k χ z))•unstableVector k z := by
  simp only [fineFrame,flatFrame,ContinuousLinearMap.comp_apply,smul_apply,
    lyapunovFrame,planeFrame_apply,pairToComplex_apply,
    zero_div,zero_smul,zero_add,smul_smul]
  congr 1
  ring

lemma fineInverse_first_zero (k χ ε δ : ℝ) (z : Torus) {p : ℂ}
    (hp : wedge p (unstableVector k z)=0) : (fineInverse k χ ε δ z p).1=0 := by
  simp [fineInverse,flatInverse,lyapunovCoframe,planeCoframe_apply,hp]

lemma fineInverse_second_zero (k χ ε δ : ℝ) (z : Torus) {p : ℂ}
    (hp : wedge (stableVector k z) p=0) : (fineInverse k χ ε δ z p).2=0 := by
  simp [fineInverse,flatInverse,lyapunovCoframe,planeCoframe_apply,hp]

theorem fine_reversal_frame_swap (k χ ε : ℝ) (z : Torus)
    (hr : wedge (stableVector k z) (unstableVector k z)≠0)
    (hr' : wedge (stableVector k (standardReversal z)) (unstableVector k (standardReversal z))≠0)
    (hline : wedge (unstableVector k z) (tangentReversal (stableVector k (standardReversal z)))=0)
    (hline' : wedge (unstableVector k (standardReversal z)) (tangentReversal (stableVector k z))=0) :
    ∃ α β : ℝ,α≠0 ∧ β≠0 ∧ ∀ δ : ℝ,δ≠0 → ∀ p : RealPlane,
      fineInverse k χ ε δ z (tangentReversal (fineFrame k χ ε δ (standardReversal z) p))=(β*p.2,α*p.1) := by
  let M := (fineInverse k χ ε 1 z).comp (tangentReversal.comp (fineFrame k χ ε 1 (standardReversal z)))
  have hfirst : (M (1,0)).1=0 := by
    apply fineInverse_first_zero
    change wedge (tangentReversal (fineFrame k χ ε 1 (standardReversal z) (1,0))) (unstableVector k z)=0
    rw [fineFrame_first,map_smul,wedge_smul_left]
    have h : wedge (tangentReversal (stableVector k (standardReversal z))) (unstableVector k z)=0 := by
      rw [wedge_swap,hline,neg_zero]
    rw [h,mul_zero]
  have hsecond : (M (0,1)).2=0 := by
    apply fineInverse_second_zero
    change wedge (stableVector k z) (tangentReversal (fineFrame k χ ε 1 (standardReversal z) (0,1)))=0
    rw [fineFrame_second,map_smul,wedge_smul_right]
    have h := tangentReversal_wedge (unstableVector k (standardReversal z)) (tangentReversal (stableVector k z))
    rw [tangentReversal_involutive,hline',neg_zero] at h
    rw [wedge_swap,h,neg_zero,mul_zero]
  have hi : Function.Injective M := by
    intro p q hpq
    have h := congrArg (fun v => fineInverse k χ ε 1 (standardReversal z)
      (tangentReversal (fineFrame k χ ε 1 z v))) hpq
    simpa only [M,ContinuousLinearMap.comp_apply,
      fineFrame_inverse k χ ε (by norm_num : (0 : ℝ)<1) z hr,tangentReversal_involutive,
      fineInverse_frame k χ ε (by norm_num : (0 : ℝ)<1) (standardReversal z) hr'] using h
  let α := (M (1,0)).2
  let β := (M (0,1)).1
  have hα : α≠0 := by
    intro he
    have hz : M (1,0)=M 0 := by rw [map_zero]; exact Prod.ext hfirst he
    have h := hi hz
    norm_num at h
  have hβ : β≠0 := by
    intro he
    have hz : M (0,1)=M 0 := by rw [map_zero]; exact Prod.ext he hsecond
    have h := hi hz
    norm_num at h
  refine ⟨α,β,hα,hβ,?_⟩
  intro δ hδ p
  rw [fine_relative_frame_independent_delta k χ ε hδ]
  change M p=(_,_)
  have hp : p=p.1•((1,0) : RealPlane)+p.2•((0,1) : RealPlane) := by ext <;> simp
  rw [hp,map_add,map_smul,map_smul]
  apply Prod.ext <;> simp [hfirst,hsecond,α,β,mul_comm]

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal

theorem compact_reversible_fineRegular_block (k : ℝ) (hk : 0≤k) {χ ε : ℝ} (hχ : 0<χ) (hε : 0<ε)
    {r : ℝ≥0∞} (hr : r<area (spectralGapRegion k hk χ)) :
    ∃ K : Set Torus, K⊆spectralGapRegion k hk χ ∧ IsCompact K ∧ r<area K ∧
      ContinuousOn (fun z => (orbitChartData k χ ε z,orbitChartData k χ ε (standardReversal z))) K ∧
      ∀ z∈K,
        (∀ n : ℕ, FineRegular k χ ε ((standardMap k)^[n] z) ∧
          FineRegular k χ ε ((inverseMap k)^[n] z)) ∧
        (∀ n : ℕ, FineRegular k χ ε ((standardMap k)^[n] (standardReversal z)) ∧
          FineRegular k χ ε ((inverseMap k)^[n] (standardReversal z))) ∧
        wedge (stableVector k z) (tangentReversal (stableVector k (standardReversal z)))≠0 ∧
        wedge (unstableVector k z) (tangentReversal (stableVector k (standardReversal z)))=0 ∧
        wedge (unstableVector k (standardReversal z)) (tangentReversal (stableVector k z))=0 := by
  let μ := area.restrict (spectralGapRegion k hk χ)
  have hrev := (measurePreserving_reversal_spectralGapRegion k hk χ).quasiMeasurePreserving.ae
    (ae_fineRegular_all_iterates k hk hχ hε)
  have htrans := ae_restrict_of_ae (μ := area) (s := spectralGapRegion k hk χ) (ae_reversal_tangent_transverse k hk)
  have hline := ae_restrict_of_ae (μ := area) (s := spectralGapRegion k hk χ) (ae_stableVector_reversal_unstable k hk)
  have hlineR := ae_restrict_of_ae (μ := area) (s := spectralGapRegion k hk χ) (ae_unstableVector_reversal_stable k hk)
  have hg := measurableSet_spectralGapRegion k hk χ
  have hall : ∀ᵐ z ∂μ,
      (∀ n : ℕ, FineRegular k χ ε ((standardMap k)^[n] z) ∧ FineRegular k χ ε ((inverseMap k)^[n] z)) ∧
      (∀ n : ℕ, FineRegular k χ ε ((standardMap k)^[n] (standardReversal z)) ∧
        FineRegular k χ ε ((inverseMap k)^[n] (standardReversal z))) ∧
      wedge (stableVector k z) (tangentReversal (stableVector k (standardReversal z)))≠0 ∧
      wedge (unstableVector k z) (tangentReversal (stableVector k (standardReversal z)))=0 ∧
        wedge (unstableVector k (standardReversal z)) (tangentReversal (stableVector k z))=0 := by
    filter_upwards [ae_fineRegular_all_iterates k hk hχ hε,hrev,htrans,hline,hlineR,ae_restrict_mem hg] with z hz hr ht hl hlR hzg
    have hp : 0 < standardLyapunov k hk z := hχ.trans hzg
    exact ⟨hz,hr,ht hp,hl hp,hlR hp⟩
  obtain ⟨B,hBae,hB,hBG⟩ := IsMeasurablyGenerated.exists_measurable_subset hall
  have hfull : (B∩spectralGapRegion k hk χ : Set Torus) =ᵐ[area] spectralGapRegion k hk χ := by
    filter_upwards [(ae_restrict_iff' hg).mp hBae] with z hz
    apply propext
    exact ⟨And.right,fun h => ⟨hz h,h⟩⟩
  have hm : area (B∩spectralGapRegion k hk χ)=area (spectralGapRegion k hk χ) := measure_congr hfull
  let : PolishSpace LyapunovChartData := inferInstance
  let : PolishSpace (LyapunovChartData × LyapunovChartData) := by constructor
  let : TopologicalSpace.IsCompletelyMetrizableSpace (ℕ → LyapunovChartData × LyapunovChartData) :=
    @TopologicalSpace.IsCompletelyMetrizableSpace.pi_countable ℕ _
      (fun _ => LyapunovChartData × LyapunovChartData) _ (fun _ => inferInstance)
  let : PolishSpace (ℕ → LyapunovChartData × LyapunovChartData) := { toSecondCountableTopology := inferInstance, toIsCompletelyMetrizableSpace := inferInstance }
  let : SecondCountableTopology (ℕ → LyapunovChartData × LyapunovChartData) := inferInstance
  let : PolishSpace ((ℕ → LyapunovChartData × LyapunovChartData) × (ℕ → LyapunovChartData × LyapunovChartData)) :=
    { toSecondCountableTopology := inferInstance, toIsCompletelyMetrizableSpace := inferInstance }
  let : BorelSpace LyapunovChartData := inferInstance
  let : BorelSpace (LyapunovChartData × LyapunovChartData) := inferInstance
  let : BorelSpace (ℕ → LyapunovChartData × LyapunovChartData) := inferInstance
  let : BorelSpace ((ℕ → LyapunovChartData × LyapunovChartData) × (ℕ → LyapunovChartData × LyapunovChartData)) := inferInstance
  have hdata : Measurable (fun z => (orbitChartData k χ ε z,orbitChartData k χ ε (standardReversal z))) :=
    (measurable_orbitChartData k χ ε).prodMk ((measurable_orbitChartData k χ ε).comp measurePreserving_standardReversal.measurable)
  obtain ⟨K,hKA,hK,hcont,hKr⟩ := measurable_compact_continuity_block area hdata (hB.inter hg)
    (r := r) (by rwa [hm])
  exact ⟨K,fun z hz => (hKA hz).2,hK,hKr,hcont,fun z hz => hBG (hKA hz).1⟩

theorem compact_lift_reversible_block (k : ℝ) (hk : 0≤k) {χ ε : ℝ} (hχ : 0<χ) (hε : 0<ε)
    (hgap : 0<area (spectralGapRegion k hk χ)) :
    ∃ C : Set ℂ, IsCompact C ∧ 0<volume C ∧
      (∀ v∈C,complexProjection v∈spectralGapRegion k hk χ) ∧
      ContinuousOn (fun v => (orbitChartData k χ ε (complexProjection v),
        orbitChartData k χ ε (complexProjection (tangentReversal v)))) C ∧
      ∀ v∈C,
        (∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] v)) ∧
          FineRegular k χ ε (complexProjection ((standardInverseLift k)^[n] v))) ∧
        (∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] (tangentReversal v))) ∧
          FineRegular k χ ε (complexProjection ((standardInverseLift k)^[n] (tangentReversal v)))) ∧
        wedge (stableVector k (complexProjection v))
          (tangentReversal (stableVector k (complexProjection (tangentReversal v))))≠0 ∧
        wedge (unstableVector k (complexProjection v))
          (tangentReversal (stableVector k (complexProjection (tangentReversal v))))=0 ∧
        wedge (unstableVector k (complexProjection (tangentReversal v)))
          (tangentReversal (stableVector k (complexProjection v)))=0 := by
  obtain ⟨K,hKG,hK,hKpos,hdata,hreg⟩ := compact_reversible_fineRegular_block k hk hχ hε hgap
  let C : Set ℂ := complexProjection ⁻¹' K ∩ Metric.closedBall 0 2
  have hC : IsCompact C := (isCompact_closedBall (0 : ℂ) 2).inter_left
    (hK.isClosed.preimage continuous_complexProjection)
  have hKC : area K≤volume C := area_le_volume_of_complexRep_subset hK.measurableSet (by
    intro z hz
    exact ⟨by simpa only [mem_preimage,complexProjection_complexRep] using hz,
      by simpa only [Metric.mem_closedBall,dist_zero_right] using complexRep_norm_le_two z⟩)
  refine ⟨C,hC,hKpos.trans_le hKC,fun v hv => hKG hv.1,?_,?_⟩
  · simpa only [complexProjection_tangentReversal,Function.comp_def] using
      hdata.comp continuous_complexProjection.continuousOn (fun _ hv => hv.1)
  · intro v hv
    have h := hreg (complexProjection v) hv.1
    simpa only [complexProjection_iterate,complexProjection_inverse_iterate,complexProjection_tangentReversal] using h

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_FineChartGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

lemma shrink_fine_holonomy_delta {χ ε δ₀ τ : ℝ} (hδ₀ : 0<δ₀) (hδ₀' : δ₀≤1/2)
    (hq₀ : Real.exp (-χ+ε)+δ₀<1)
    (hslow₀ : Real.exp (4*ε)*(Real.exp (-χ+ε)+δ₀)<1) (hτ : 0<τ) :
    ∃ δ : ℝ,0<δ ∧ δ≤1/2 ∧ Real.exp (-χ+ε)+δ<1 ∧
      Real.exp (4*ε)*(Real.exp (-χ+ε)+δ)<1 ∧
      Real.exp (-χ+ε)*δ/(1-Real.exp (-χ+ε))≤τ := by
  let ℓ := Real.exp (-χ+ε)
  have hℓ : 0<ℓ := Real.exp_pos _
  have hℓ1 : ℓ<1 := by dsimp only [ℓ]; linarith
  let δ := min δ₀ (τ*(1-ℓ)/ℓ)
  have hδ : 0<δ := lt_min hδ₀ (div_pos (mul_pos hτ (sub_pos.mpr hℓ1)) hℓ)
  have hd : δ≤δ₀ := min_le_left _ _
  refine ⟨δ,hδ,hd.trans hδ₀',by dsimp only [ℓ] at *; linarith,?_,?_⟩
  · nlinarith [Real.exp_pos (4*ε)]
  · apply (div_le_iff₀ (sub_pos.mpr hℓ1)).mpr
    have h := (le_div_iff₀ hℓ).mp (show δ≤τ*(1-ℓ)/ℓ from min_le_right _ _)
    nlinarith

lemma small_chart_radius (S R : ℝ) (hS : 0≤S) (hR : 0<R) :
    ∃ r : ℝ,0 < r ∧ r≤1/12 ∧ (4*S*r)/(100*R)+r≤1 := by
  let a := (4*S)/(100*R)
  have ha : 0≤a := by dsimp [a]; positivity
  let r := 1/(24*(1+a))
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r,hr,?_,?_⟩
  · dsimp only [r]
    apply (div_le_iff₀ (by positivity : 0<24*(1+a))).mpr
    nlinarith
  · have he : (4*S*r)/(100*R)+r=r*(1+a) := by dsimp only [a]; ring
    rw [he]
    dsimp only [r]
    have : 1+a≠0 := by positivity
    field_simp
    norm_num

end StandardMapEntropy
end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)

@[simp] lemma coordinates_chart (p : RealPlane) : B.coordinates (B.chart p)=p := by
  rw [coordinates,chart,add_sub_cancel_left,fineInverse_frame k χ B.ε B.δ_pos _ B.centre_regular]

end ReversibleRectangleBlock

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_CurvedHolonomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
attribute [local instance] Measure.Subtype.measureSpace

namespace ReversibleRectangleBlock
variable {k χ : ℝ} (B : ReversibleRectangleBlock k χ)

@[simp] lemma coordinates_label (p : B.coordinateCarrier) : B.coordinates (B.label p)=(p : RealPlane) :=
  B.coordinates_chart p

end ReversibleRectangleBlock
end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_PowerAtomCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Topology
open scoped Topology ENNReal
open NonlinearStable

theorem exists_reversibleRectangleBlock_q44_oai (k : ℝ) (hk : 0≤k) {χ : ℝ} (hχ : 0<χ)
    (hgap : 0<area (spectralGapRegion k hk χ)) : Nonempty (ReversibleRectangleBlock k χ) := by
  obtain ⟨ε,δ₀,hε,hδ₀,hδ₀',hq₀,hslow₀,_⟩ := fine_holonomy_parameters hχ (by norm_num : (0 : ℝ)<1)
  obtain ⟨C,hC,hCpos,hCG,hdata,hreg⟩ := compact_lift_reversible_block k hk hχ hε hgap
  obtain ⟨w,hwC,hw⟩ := positive_compact_neighborhood hC hCpos
  have hwreg : wedge (stableVector k (complexProjection w)) (unstableVector k (complexProjection w))≠0 :=
    (hreg w hwC).1 0 |>.1.1
  have hwRreg : wedge (stableVector k (complexProjection (tangentReversal w)))
      (unstableVector k (complexProjection (tangentReversal w)))≠0 := (hreg w hwC).2.1 0 |>.1.1
  obtain ⟨α,β,hα,hβ,hswap⟩ := fine_reversal_frame_swap k χ ε (complexProjection w) hwreg
    (by simpa only [complexProjection_tangentReversal] using hwRreg)
    (by simpa only [complexProjection_tangentReversal] using (hreg w hwC).2.2.2.1)
    (by simpa only [complexProjection_tangentReversal] using (hreg w hwC).2.2.2.2)
  let η := min (1/16) (|α|/(16*|β|))
  have hη : 0<η := lt_min (by norm_num) (div_pos (abs_pos.mpr hα) (by positivity))
  have hηsmall : η≤1/16 := min_le_left _ _
  have hηscale : (|β|/|α|)*((8/3)*η)≤1/2 := by
    have hh := (le_div_iff₀ (by positivity : 0<16*|β|)).mp
      (show η≤|α|/(16*|β|) from min_le_right _ _)
    have he : (|β|/|α|)*((8/3)*η)=(|β| *((8/3)*η))/|α| := by ring
    rw [he]
    apply (div_le_iff₀ (abs_pos.mpr hα)).mpr
    nlinarith [abs_pos.mpr hα]
  obtain ⟨δ,hδ,hδ',hq,hslow,hslope⟩ := shrink_fine_holonomy_delta hδ₀ hδ₀' hq₀ hslow₀ hη
  let R := codingRadius k χ ε δ (complexProjection w)/2
  let R' := codingRadius k χ ε δ (complexProjection (tangentReversal w))/2
  have hR : 0<R := half_pos (codingRadius_pos k χ ε hδ _)
  have hR' : 0<R' := half_pos (codingRadius_pos k χ ε hδ _)
  obtain ⟨r,hr,hrsmall,hsize⟩ := small_chart_radius (fineScale k ε δ) R (fineScale_pos k ε hδ).le hR
  obtain ⟨r',hr',hrsmall',hsize'⟩ := small_chart_radius (fineScale k ε δ) R' (fineScale_pos k ε hδ).le hR'
  let ρ := min (r/8) (|α| *r'/8)
  have hρ : 0<ρ := lt_min (by positivity) (by positivity)
  have hρr : ρ ≤ r/8 := min_le_left _ _
  have hρr' : ρ≤|α| *r'/8 := min_le_right _ _
  have hdc : Continuous (fun v : C => (orbitChartData k χ ε (complexProjection v),
      orbitChartData k χ ε (complexProjection (tangentReversal v)))) :=
    continuousOn_iff_continuous_domRestrict.mp hdata
  have hd0 : Continuous (fun v : C => lyapunovChartData k χ ε (complexProjection v)) :=
    ((continuous_apply 0).comp hdc.fst).fst
  have hdR0 : Continuous (fun v : C => lyapunovChartData k χ ε (complexProjection (tangentReversal v))) :=
    ((continuous_apply 0).comp hdc.snd).fst
  have hF : ContinuousOn (fun v => fineFrame k χ ε δ (complexProjection v)) C :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_fineFrame_of_data k χ ε δ _ hd0)
  have hI : ContinuousOn (fun v => fineInverse k χ ε δ (complexProjection v)) C :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_fineInverse_of_data k χ ε δ hδ _ hd0)
  have hFR : ContinuousOn (fun v => fineFrame k χ ε δ (complexProjection (tangentReversal v))) C :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_fineFrame_of_data k χ ε δ _ hdR0)
  have hIR : ContinuousOn (fun v => fineInverse k χ ε δ (complexProjection (tangentReversal v))) C :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_fineInverse_of_data k χ ε δ hδ _ hdR0)
  have hrad : ContinuousOn (fun v => codingRadius k χ ε δ (complexProjection v)) C :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_const.mul (hd0.snd.snd.pow 2))
  have hradR : ContinuousOn (fun v => codingRadius k χ ε δ (complexProjection (tangentReversal v))) C :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_const.mul (hdR0.snd.snd.pow 2))
  have hIF : (fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection w))=
      ContinuousLinearMap.id ℝ Plane := by
    apply ContinuousLinearMap.ext
    exact fineInverse_frame k χ ε hδ _ hwreg
  have hIFR : (fineInverse k χ ε δ (complexProjection (tangentReversal w))).comp
      (fineFrame k χ ε δ (complexProjection (tangentReversal w)))=ContinuousLinearMap.id ℝ Plane := by
    apply ContinuousLinearMap.ext
    exact fineInverse_frame k χ ε hδ _ hwRreg
  have hclose : ∀ᶠ v in 𝓝[C] w,‖(fineInverse k χ ε δ (complexProjection w)).comp
      (fineFrame k χ ε δ (complexProjection v))-ContinuousLinearMap.id ℝ Plane‖<η := by
    have hc : ContinuousWithinAt (fun v => ‖(fineInverse k χ ε δ (complexProjection w)).comp
        (fineFrame k χ ε δ (complexProjection v))-ContinuousLinearMap.id ℝ Plane‖) C w := (((continuousOn_const.clm_comp hF).sub continuousOn_const).norm w hwC)
    apply hc.eventually (p := fun y : ℝ => y<η)
    simp only [hIF,sub_self,norm_zero]
    exact eventually_lt_nhds hη
  have hcloseR : ∀ᶠ v in 𝓝[C] w,‖(fineInverse k χ ε δ (complexProjection (tangentReversal w))).comp
      (fineFrame k χ ε δ (complexProjection (tangentReversal v)))-ContinuousLinearMap.id ℝ Plane‖<η := by
    have hc : ContinuousWithinAt (fun v => ‖(fineInverse k χ ε δ (complexProjection (tangentReversal w))).comp
        (fineFrame k χ ε δ (complexProjection (tangentReversal v)))-ContinuousLinearMap.id ℝ Plane‖) C w := (((continuousOn_const.clm_comp hFR).sub continuousOn_const).norm w hwC)
    apply hc.eventually (p := fun y : ℝ => y<η)
    simp only [hIFR,sub_self,norm_zero]
    exact eventually_lt_nhds hη
  have hco : ∀ᶠ v in 𝓝[C] w,‖(fineInverse k χ ε δ (complexProjection v)).comp
      (fineFrame k χ ε δ (complexProjection w))-ContinuousLinearMap.id ℝ Plane‖<1/4 := by
    have hc : ContinuousWithinAt (fun v => ‖(fineInverse k χ ε δ (complexProjection v)).comp
        (fineFrame k χ ε δ (complexProjection w))-ContinuousLinearMap.id ℝ Plane‖) C w := (((hI.clm_comp continuousOn_const).sub continuousOn_const).norm w hwC)
    apply hc.eventually (p := fun y : ℝ => y<1/4)
    simp only [hIF,sub_self,norm_zero]
    exact eventually_lt_nhds (by norm_num)
  have hcoR : ∀ᶠ v in 𝓝[C] w,‖(fineInverse k χ ε δ (complexProjection (tangentReversal v))).comp
      (fineFrame k χ ε δ (complexProjection (tangentReversal w)))-ContinuousLinearMap.id ℝ Plane‖<1/4 := by
    have hc : ContinuousWithinAt (fun v => ‖(fineInverse k χ ε δ (complexProjection (tangentReversal v))).comp
        (fineFrame k χ ε δ (complexProjection (tangentReversal w)))-ContinuousLinearMap.id ℝ Plane‖) C w := (((hIR.clm_comp continuousOn_const).sub continuousOn_const).norm w hwC)
    apply hc.eventually (p := fun y : ℝ => y<1/4)
    simp only [hIFR,sub_self,norm_zero]
    exact eventually_lt_nhds (by norm_num)
  have hRl : ∀ᶠ v in 𝓝[C] w,R < codingRadius k χ ε δ (complexProjection v) := by
    apply (hrad w hwC).eventually
    exact eventually_gt_nhds (by dsimp only [R]; linarith [codingRadius_pos k χ ε hδ (complexProjection w)])
  have hRRl : ∀ᶠ v in 𝓝[C] w,R' < codingRadius k χ ε δ (complexProjection (tangentReversal v)) := by
    apply (hradR w hwC).eventually
    exact eventually_gt_nhds (by dsimp only [R']; linarith [codingRadius_pos k χ ε hδ (complexProjection (tangentReversal w))])
  have hcentral : ∀ᶠ v in 𝓝[C] w,‖fineInverse k χ ε δ (complexProjection w) (v-w)‖<ρ/100 := by
    have hc : Continuous (fun v : ℂ => ‖fineInverse k χ ε δ (complexProjection w) (v-w)‖) := by fun_prop
    apply (hc.continuousWithinAt (s := C) (x := w)).eventually (p := fun y : ℝ => y<ρ/100)
    simp only [sub_self,map_zero,norm_zero]
    exact eventually_lt_nhds (by positivity)
  have hcentralR : ∀ᶠ v in 𝓝[C] w,‖fineInverse k χ ε δ (complexProjection (tangentReversal w))
      (tangentReversal v-tangentReversal w)‖ < r'/4 := by
    have hc : Continuous (fun v : ℂ => ‖fineInverse k χ ε δ (complexProjection (tangentReversal w))
        (tangentReversal v-tangentReversal w)‖) := by fun_prop
    apply (hc.continuousWithinAt (s := C) (x := w)).eventually (p := fun y : ℝ => y < r'/4)
    simp only [sub_self,map_zero,norm_zero]
    exact eventually_lt_nhds (by positivity)
  obtain ⟨K,hKC,hK,hKpos,hKP⟩ := hw
    (fun v => R < codingRadius k χ ε δ (complexProjection v) ∧
      R' < codingRadius k χ ε δ (complexProjection (tangentReversal v)) ∧
      ‖(fineInverse k χ ε δ (complexProjection w)).comp (fineFrame k χ ε δ (complexProjection v))-
        ContinuousLinearMap.id ℝ Plane‖<η ∧
      ‖(fineInverse k χ ε δ (complexProjection (tangentReversal w))).comp
        (fineFrame k χ ε δ (complexProjection (tangentReversal v)))-ContinuousLinearMap.id ℝ Plane‖<η ∧
      ‖(fineInverse k χ ε δ (complexProjection v)).comp (fineFrame k χ ε δ (complexProjection w))-
        ContinuousLinearMap.id ℝ Plane‖<1/4 ∧
      ‖(fineInverse k χ ε δ (complexProjection (tangentReversal v))).comp
        (fineFrame k χ ε δ (complexProjection (tangentReversal w)))-ContinuousLinearMap.id ℝ Plane‖<1/4 ∧
      ‖fineInverse k χ ε δ (complexProjection w) (v-w)‖<ρ/100 ∧
      ‖fineInverse k χ ε δ (complexProjection (tangentReversal w)) (tangentReversal v-tangentReversal w)‖ < r'/4)
    (hRl.and (hRRl.and (hclose.and (hcloseR.and (hco.and (hcoR.and (hcentral.and hcentralR)))))))
  exact ⟨{
    ε := ε,δ := δ,ε_pos := hε,δ_pos := hδ,δ_small := hδ',contraction := hq,slow := hslow,
    carrier := K,compact := hK,positive := hKpos,centre := w,centre_regular := hwreg,reverse_regular := hwRreg,
    α := α,β := β,α_ne := hα,β_ne := hβ,
    swap := by simpa only [complexProjection_tangentReversal] using hswap δ hδ.ne',
    η := η,η_pos := hη,η_small := hηsmall,slope := hslope,reverse_slope := hηscale,
    r := r,r' := r',R := R,R' := R',ρ := ρ,r_pos := hr,r'_pos := hr',R_pos := hR,R'_pos := hR',ρ_pos := hρ,
    r_small := hrsmall,r'_small := hrsmall',ρ_small := hρr,ρ_reverse := hρr',size := hsize,reverse_size := hsize',
    data := hdata.mono hKC,
    regular := fun v hv n => ((hreg v (hKC hv)).1 n).1,
    reversed := fun v hv n => ((hreg v (hKC hv)).2.1 n).1,
    radius := fun v hv => (hKP v hv).1.le,
    reverse_radius := fun v hv => (hKP v hv).2.1.le,
    frames := fun v hv => (hKP v hv).2.2.1.le,
    reverse_frames := fun v hv => (hKP v hv).2.2.2.1.le,
    coframes := fun v hv => (hKP v hv).2.2.2.2.1.le,
    reverse_coframes := fun v hv => (hKP v hv).2.2.2.2.2.1.le,
    central := fun v hv => (hKP v hv).2.2.2.2.2.2.1.le,
    reverse_central := fun v hv => (hKP v hv).2.2.2.2.2.2.2.le }⟩

end StandardMapEntropy

end
end

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.exists_reversibleRectangleBlock_q44_oai := @OAI.StandardMapEntropy.exists_reversibleRectangleBlock_q44_oai
