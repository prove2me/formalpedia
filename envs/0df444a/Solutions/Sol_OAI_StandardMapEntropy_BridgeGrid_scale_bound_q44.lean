-- Prove2me | solution 1 for OAI.StandardMapEntropy.BridgeGrid.scale_bound_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:22:29.389703+00:00
-- url     : https://prove2.me/submissions/1831e83b-67f7-4909-86aa-aab824a6f780

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002
import Theorems.Thm_OAI_StandardMapEntropy_middle_observation_product_q44

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

lemma drawdown_nonneg (z : ℕ → ℝ) (c : ℝ) (n : ℕ) : 0 ≤ drawdown z c n := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

lemma drawdown_ge_drop (z : ℕ → ℝ) (c : ℝ) (j l : ℕ) (hl : l ≤ j) :
    z l - z j + c * ((j : ℝ) - (l : ℝ)) ≤ drawdown z c j := by
  induction j with
  | zero =>
    have : l = 0 := by omega
    simp [this, drawdown]
  | succ j ih =>
    by_cases hlj : l = j + 1
    · simpa [hlj] using drawdown_nonneg z c (j + 1)
    · have hl' : l ≤ j := by omega
      have hi := ih hl'
      have hm : drawdown z c j + c + z j - z (j + 1) ≤ drawdown z c (j + 1) :=
        le_max_right _ _
      push_cast
      nlinarith only [hi, hm]

lemma drawdown_pos_of_bad (z : ℕ → ℝ) (c : ℝ) (j : ℕ)
    (h : ∃ l < j, z j - z l < c * ((j : ℝ) - (l : ℝ))) :
    0 < drawdown z c j := by
  obtain ⟨l, hlj, hdrop⟩ := h
  have hg := drawdown_ge_drop z c j l hlj.le
  linarith

lemma drawdown_step_account (z : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (hz : z (n + 1) - z n ≤ 1) :
    (if 0 < drawdown z c (n + 1) then 1 - c else 0) ≤
      1 - (z (n + 1) - z n) + drawdown z c n - drawdown z c (n + 1) := by
  split_ifs with hp
  · have he : drawdown z c (n + 1) = drawdown z c n + c + z n - z (n + 1) := by
      change max 0 (drawdown z c n + c + z n - z (n + 1)) = _
      apply max_eq_right
      change 0 < max 0 (drawdown z c n + c + z n - z (n + 1)) at hp
      rcases lt_max_iff.mp hp with hp | hp
      · exact False.elim ((lt_irrefl _) hp)
      · exact hp.le
    rw [he]
    linarith
  · have he : drawdown z c (n + 1) = 0 :=
      le_antisymm (not_lt.mp hp) (drawdown_nonneg z c _)
    rw [he]
    linarith [drawdown_nonneg z c n]

lemma drawdown_account_sum (z : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (1 - (z (n + 1) - z n) + drawdown z c n - drawdown z c (n + 1))) =
      (N : ℝ) - (z N - z 0) - drawdown z c N := by
  induction N with
  | zero => simp [drawdown]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma drawdown_count (z : ℕ → ℝ) (c : ℝ) (N : ℕ)
    (hz : ∀ n < N, z (n + 1) - z n ≤ 1) :
    (((Finset.range N).filter (fun n => 0 < drawdown z c (n + 1))).card : ℝ) * (1 - c) ≤
      (N : ℝ) - (z N - z 0) := by
  classical
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun n hn =>
    drawdown_step_account z c n (hz n (Finset.mem_range.mp hn)))
  rw [drawdown_account_sum] at hsum
  have hc :
      (((Finset.range N).filter (fun n => 0 < drawdown z c (n + 1))).card : ℝ) * (1 - c) =
      ∑ n ∈ Finset.range N, if 0 < drawdown z c (n + 1) then 1 - c else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← hc] at hsum
  linarith [drawdown_nonneg z c N]

theorem shortfall_count (z : ℕ → ℝ) (c : ℝ) (hc : c < 1) (N : ℕ)
    (hz : ∀ n < N, z (n + 1) - z n ≤ 1) :
    (((Finset.range N).filter fun n =>
      ∃ l < n + 1, z (n + 1) - z l < c * ((n + 1 : ℕ) - (l : ℝ))).card : ℝ) ≤
      ((N : ℝ) - (z N - z 0)) / (1 - c) := by
  classical
  have hsub : ((Finset.range N).filter fun n =>
        ∃ l < n + 1, z (n + 1) - z l < c * ((n + 1 : ℕ) - (l : ℝ))) ⊆
      ((Finset.range N).filter fun n => 0 < drawdown z c (n + 1)) := by
    intro n hn
    obtain ⟨hnN, hbad⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hnN, drawdown_pos_of_bad z c (n + 1) hbad⟩
  have hcard :
      (((Finset.range N).filter fun n =>
        ∃ l < n + 1, z (n + 1) - z l < c * ((n + 1 : ℕ) - (l : ℝ))).card : ℝ) ≤
      (((Finset.range N).filter fun n => 0 < drawdown z c (n + 1))).card :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  apply (le_div_iff₀ (sub_pos.mpr hc)).mpr
  exact (mul_le_mul_of_nonneg_right hcard (sub_nonneg.mpr hc.le)).trans
    (drawdown_count z c N hz)

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
lemma torusShortfall_shift (k : ℝ) (z : Torus) (a b : ℤ) (n : ℕ) :
    torusShortfall k (torusIter k b z) a n=torusShortfall k z (a+b) n := by
  have he : torusSegmentCoefficient k (torusIter k b z) a=torusSegmentCoefficient k z (a+b) := by
    funext i
    unfold torusSegmentCoefficient
    rw [← torusIter_add]
    congr 3
    ring
  simp only [torusShortfall,torusSegmentTransfer,he]
lemma continuous_shortfall_observation (k : ℝ) (hk : 0 ≤ k) {R : ℕ}
    (a : Fin R → ℤ) (n : Fin R → ℕ) (F : (Fin R → ℝ) → ℝ) (hF : Continuous F) :
    Continuous (fun z => F (fun i => torusShortfall k z (a i) (n i))) :=
  hF.comp (continuous_pi (fun i => continuous_torusShortfall k hk (a i) (n i)))
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
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MiddleCount
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

lemma bridgeMiddle_bounds (N i : ℕ) (hN : 100 ≤ N) (hi : i∈bridgeMiddle N) :
    2 ≤ i ∧ 2 ≤ N-i ∧ (N:ℝ)/3-1 ≤ (i:ℝ) ∧ (N:ℝ)/3-1 ≤ (N-i:ℕ) ∧ i ≤ N := by
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hi
  have hdiv := Nat.mod_lt N (by norm_num : 0 < 3)
  have hdiv' := Nat.mod_lt (2*N) (by norm_num : 0 < 3)
  have he := Nat.mod_add_div N 3
  have he' := Nat.mod_add_div (2*N) 3
  have h1 : 2 ≤ i := by omega
  have h2 : 2 ≤ N-i := by omega
  have h3 : N ≤ 3*i+2 := by omega
  have h4 : N ≤ 3*(N-i)+2 := by omega
  refine ⟨h1,h2,?_,?_,by omega⟩
  · have : (N:ℝ) ≤ 3*(i:ℝ)+2 := by exact_mod_cast h3
    linarith
  · have : (N:ℝ) ≤ 3*(N-i:ℕ)+2 := by exact_mod_cast h4
    linarith
lemma shortfall_count_sample (z : ℕ → ℝ) (c : ℝ) (hc : c < 1) (N : ℕ)
    (hz : ∀ j < N, z (j+1)-z j ≤ 1) (S : Finset ℕ)
    (hS : ∀ j∈S, 1 ≤ j ∧ j ≤ N ∧ ∃ l < j, z j-z l < c*((j:ℝ)-(l:ℝ))) :
    (S.card:ℝ) ≤ ((N:ℝ)-(z N-z 0))/(1-c) := by
  classical
  let D := (Finset.range N).filter fun j => ∃ l < j+1, z (j+1)-z l < c*((j+1:ℕ)-(l:ℝ))
  have hcard : S.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn (fun j => j-1)
    · intro j hj
      obtain ⟨hj1,hjN,l,hl,hbad⟩ := hS j hj
      change j-1∈D
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega),l,by omega,?_⟩
      simpa only [Nat.sub_add_cancel hj1] using hbad
    · intro i hi j hj he
      have := (hS i hi).1
      have := (hS j hj).1
      dsimp only at he
      omega
  exact (Nat.cast_le.mpr hcard).trans (shortfall_count z c hc N hz)
lemma middle_log_good_count (z : ℕ → ℝ) (N : ℕ) (hN : 100 ≤ N)
    (hz : ∀ j < N, z (j+1)-z j ≤ 1)
    (htotal : (999/1000:ℝ)*(N:ℝ) ≤ z N-z 0) :
    (N:ℝ)/5 ≤ (bridgeMiddleGood z N).card := by
  classical
  change (N:ℝ)/5 ≤ ((bridgeMiddle N).filter (MiddleLogGood z N)).card
  let S := bridgeMiddle N
  let E := S.filter fun i => ∃ j < i, z i-z j < (49/50:ℝ)*((i:ℝ)-(j:ℝ))
  let F := S.filter fun i => ∃ j, i < j ∧ j ≤ N ∧ z j-z i < (49/50:ℝ)*((j:ℝ)-(i:ℝ))
  let zr : ℕ → ℝ := fun j => z N-z (N-j)
  have hE : (E.card:ℝ) ≤ ((N:ℝ)-(z N-z 0))/(1-(49/50:ℝ)) := by
    apply shortfall_count_sample z (49/50) (by norm_num) N hz E
    intro i hi
    obtain ⟨hi,hb⟩ := Finset.mem_filter.mp hi
    have hh := bridgeMiddle_bounds N i hN hi
    exact ⟨by omega,hh.2.2.2.2,hb⟩
  have hzr : ∀ j < N, zr (j+1)-zr j ≤ 1 := by
    intro j hj
    have hh := hz (N-j-1) (by omega)
    have he : N-j-1+1=N-j := by omega
    have he' : N-(j+1)=N-j-1 := by omega
    dsimp [zr]
    rw [he] at hh
    rw [he']
    linarith
  have hF : (F.card:ℝ) ≤ ((N:ℝ)-(z N-z 0))/(1-(49/50:ℝ)) := by
    let D := F.image (fun i => N-i)
    have hinj : Set.InjOn (fun i => N-i) (↑F : Set ℕ) := by
      intro i hi j hj he
      dsimp only at he
      have hiN := (bridgeMiddle_bounds N i hN (Finset.mem_filter.mp hi).1).2.2.2.2
      have hjN := (bridgeMiddle_bounds N j hN (Finset.mem_filter.mp hj).1).2.2.2.2
      omega
    have hcD : D.card=F.card := Finset.card_image_of_injOn hinj
    have hh := shortfall_count_sample zr (49/50) (by norm_num) N hzr D (by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hi,l,hil,hlN,hbad⟩ := Finset.mem_filter.mp hi
      have hiN := (bridgeMiddle_bounds N i hN hi).2.2.2.2
      have hi2 := (bridgeMiddle_bounds N i hN hi).2.1
      refine ⟨by omega,by omega,N-l,by omega,?_⟩
      dsimp [zr]
      rw [Nat.sub_sub_self hiN,Nat.sub_sub_self hlN,Nat.cast_sub hiN,Nat.cast_sub hlN]
      linarith)
    rw [hcD] at hh
    simpa [zr] using hh
  have hbad : S.filter (fun i => ¬MiddleLogGood z N i)=E∪F := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_union,MiddleLogGood,E,F,not_and_or,not_forall,not_le,exists_prop]
    exact and_or_left
  norm_num at hE hF
  have hcardE : (E.card:ℝ) ≤ (N:ℝ)/20 := by linarith
  have hcardF : (F.card:ℝ) ≤ (N:ℝ)/20 := by linarith
  have hcardbad : ((S.filter (fun i => ¬MiddleLogGood z N i)).card:ℝ) ≤ (N:ℝ)/10 := by
    rw [hbad]
    have hh : ((E∪F).card:ℝ) ≤ (E.card:ℝ)+(F.card:ℝ) := by exact_mod_cast Finset.card_union_le E F
    linarith
  have hScard : (N:ℝ)/3-2 ≤ (S.card:ℝ) := by
    have he : S.card=2*N/3-N/3 := by simp [S,bridgeMiddle,Nat.card_Icc]
    rw [he]
    have hx : N ≤ 3*(2*N/3-N/3)+6 := by omega
    have hx' : (N:ℝ) ≤ 3*(2*N/3-N/3:ℕ)+6 := by exact_mod_cast hx
    linarith
  have hpartition : ((S.filter (MiddleLogGood z N)).card:ℝ)+
      ((S.filter (fun i => ¬MiddleLogGood z N i)).card:ℝ)=(S.card:ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s:=S) (p:=MiddleLogGood z N)
  have hNN : (100:ℝ) ≤ N := by exact_mod_cast hN
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_GridBridge
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
lemma bridgeAreaScale_pos : 0 < bridgeAreaScale := by
  unfold bridgeAreaScale
  have hs : (0:ℝ≥0∞) < 1/32 := by norm_num
  positivity
lemma bridgeLocalConstant_ne_top : bridgeLocalConstant ≠ ∞ := by
  unfold bridgeLocalConstant
  finiteness
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MiddlePrefixBridge
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
lemma isClosed_torusPrefixGrowth (k : ℝ) (B : ℕ) : IsClosed {z | torusPrefixGrowth k B z} := by
  simp only [torusPrefixGrowth,ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_torusSegmentTransfer k 0 i).norm
lemma measurableSet_middlePrefixEvent (k : ℝ) (Bp Bm : ℕ) : MeasurableSet (middlePrefixEvent k Bp Bm) :=
  ((isClosed_torusPrefixGrowth k Bp).inter ((isClosed_torusPrefixGrowth k Bm).preimage continuous_swap)).measurableSet
lemma middleBridgeConstant_ne_top : middleBridgeConstant ≠ ∞ := by
  exact ENNReal.div_ne_top (ENNReal.mul_ne_top (by norm_num) bridgeLocalConstant_ne_top) bridgeAreaScale_pos.ne'
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_VectorGrowth
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
lemma transferVector_norm_pos (v : ℕ → ℝ) (u : ℂ) (hu : u≠0) (j : ℕ) :
    0 < ‖transferProduct v j u‖ := by
  apply norm_pos_iff.mpr
  intro he
  have hh := congrArg (transferProductInv v j) he
  simp only [transferProductInv_inverse,map_zero] at hh
  exact hu hh
lemma transferVectorLog_step (M : ℝ) (hM : 1 < M) (v : ℕ → ℝ)
    (u : ℂ) (hu : u≠0) (j : ℕ) (hv : |v (j+1)|+1≤M) :
    transferVectorLog M v u (j+1)-transferVectorLog M v u j≤1 := by
  have hp := transferVector_norm_pos v u hu j
  have hp' := transferVector_norm_pos v u hu (j+1)
  have hs : ‖transferProduct v (j+1) u‖≤M*‖transferProduct v j u‖ := by
    change ‖transferStep (v (j+1)) (transferProduct v j u)‖≤_
    exact ((transferStep _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((transferStep_norm _).trans hv) (norm_nonneg _))
  have hl := Real.log_le_log hp' hs
  rw [Real.log_mul (by linarith : M≠0) hp.ne'] at hl
  unfold transferVectorLog
  rw [← sub_div]
  exact (div_le_one (Real.log_pos hM)).mpr (by linarith)
lemma transferVectorLog_interval (M : ℝ) (hM : 1 < M) (v : ℕ → ℝ)
    (u : ℂ) (hu : u≠0) (i l : ℕ) (c : ℝ)
    (hgood : c*(l:ℝ)≤transferVectorLog M v u (i+l)-transferVectorLog M v u i) :
    M^(c*(l:ℝ))≤‖transferProduct (fun j => v (i+j)) l‖ := by
  have hi := transferVector_norm_pos v u hu i
  have hil := transferVector_norm_pos v u hu (i+l)
  have hD : 0 < ‖transferProduct (fun j => v (i+j)) l‖ := by
    have := (transferProduct_area (fun j => v (i+j)) l).singular_pair.choose_spec.2.2.2.2
    linarith
  have hb : ‖transferProduct v (i+l) u‖≤
      ‖transferProduct (fun j => v (i+j)) l‖*‖transferProduct v i u‖ := by
    rw [transferProduct_concat]
    exact (transferProduct _ _).le_opNorm _
  have hl := Real.log_le_log hil hb
  rw [Real.log_mul hD.ne' hi.ne'] at hl
  apply (Real.rpow_le_iff_le_log (by linarith) hD).mpr
  unfold transferVectorLog at hgood
  rw [← sub_div] at hgood
  have hh := (le_div_iff₀ (Real.log_pos hM)).mp hgood
  linarith
lemma torus_middle_prefix_of_vector (k : ℝ) (hk : 0≤k) (z : Torus) (N i : ℕ)
    (hi : i≤N) (u : ℂ) (hu : u≠0)
    (hg : MiddleLogGood (transferVectorLog (growthBase k) (torusSegmentCoefficient k z 0) u) N i) :
    torusPrefixGrowth k (N-i) (torusIter k (i:ℤ) z) ∧
      torusPrefixGrowth k i (torusIter k (i:ℤ) z).swap := by
  have hM : 1 < growthBase k := by linarith [growthBase_ge_four k hk]
  constructor
  · intro l hl hli
    rw [torusSegmentTransfer_shift,zero_add]
    change growthBase k^((49/50:ℝ)*(l:ℝ))≤‖transferProduct (torusSegmentCoefficient k z (i:ℤ)) l‖
    rw [← zero_add (i:ℤ),← torusSegmentCoefficient_shift]
    apply transferVectorLog_interval (growthBase k) hM _ u hu i l (49/50)
    have hh := hg.2 (i+l) (by omega) (by omega)
    simpa only [Nat.cast_add,add_sub_cancel_left] using hh
  · intro l hl hli
    rw [torusSegmentTransfer_reverse_norm,torusSegmentTransfer_shift]
    change growthBase k^((49/50:ℝ)*(l:ℝ))≤‖transferProduct (torusSegmentCoefficient k z (-(l:ℤ)+(i:ℤ))) l‖
    have hei : -(l:ℤ)+(i:ℤ)=0+((i-l:ℕ):ℤ) := by omega
    rw [hei,← torusSegmentCoefficient_shift]
    apply transferVectorLog_interval (growthBase k) hM _ u hu (i-l) l (49/50)
    have hh := hg.1 (i-l) (by omega)
    rw [Nat.sub_add_cancel hli]
    simpa only [Nat.cast_sub hli,sub_sub_cancel] using hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeAveraging
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
lemma measurableSet_torusFastBridge (k : ℝ) (N : ℕ) : MeasurableSet {z | torusFastBridge k z N} :=
  (isClosed_le continuous_const (continuous_torusSegmentTransfer k 0 N).norm).measurableSet
lemma torus_good_middles_count (k : ℝ) (hk : 0≤k) (N : ℕ) (hN : 100≤N)
    (z : Torus) (hz : torusFastBridge k z N) :
    (N:ℝ)/5≤(torusGoodMiddles k z N).card := by
  classical
  obtain ⟨u,hu,huN⟩ := exists_unit_opNorm (torusSegmentTransfer k z 0 N)
  have hu0 : u≠0 := by intro he; simp [he] at hu
  have hM : 1 < growthBase k := by linarith [growthBase_ge_four k hk]
  have hlog := Real.log_pos hM
  let zlog := transferVectorLog (growthBase k) (torusSegmentCoefficient k z 0) u
  have htotal : (999/1000:ℝ)*(N:ℝ)≤zlog N-zlog 0 := by
    have hh := Real.le_log_of_rpow_le (by linarith : 0 < growthBase k) hz
    dsimp only [zlog,transferVectorLog]
    change _≤Real.log ‖torusSegmentTransfer k z 0 N u‖/Real.log (growthBase k)-Real.log ‖u‖/Real.log (growthBase k)
    rw [huN,hu,Real.log_one,zero_div,sub_zero]
    exact (le_div_iff₀ hlog).mpr hh
  have hcount := middle_log_good_count zlog N hN (fun j _ =>
    transferVectorLog_step (growthBase k) hM _ u hu0 j (by
      obtain ⟨w,rfl⟩ := liftProjection_surjective z
      rw [torusSegmentCoefficient_lift]
      exact liftSegmentCoefficient_bound k hk w 0 (j+1))) htotal
  apply hcount.trans
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,hg⟩ := Finset.mem_filter.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨hi,?_⟩
  exact torus_middle_prefix_of_vector k hk z N i (bridgeMiddle_bounds N i hN hi).2.2.2.2 u hu0 hg
lemma lintegral_count_cover {X ι : Type*} [MeasurableSpace X] (μ : Measure X) (s : Finset ι)
    (E : ι → Set X) (hE : ∀ i∈s, MeasurableSet (E i)) (F : Set X) (hF : MeasurableSet F)
    (w : X → ℝ≥0∞) (hw : Measurable w) (a : ℝ)
    (hcount : ∀ z∈F, a≤(s.filter (fun i => z∈E i)).card) :
    ENNReal.ofReal a*(∫⁻ z in F, w z ∂μ)≤∑ i∈s, ∫⁻ z in E i, w z ∂μ := by
  classical
  have hpoint (z : X) : ENNReal.ofReal a*F.indicator w z≤∑ i∈s, (E i).indicator w z := by
    by_cases hz : z∈F
    · rw [Set.indicator_of_mem hz]
      have he : (∑ i∈s, (E i).indicator w z)=((s.filter (fun i => z∈E i)).card:ℝ≥0∞)*w z := by
        simp only [Set.indicator_apply]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul]
      rw [he]
      apply mul_le_mul_of_nonneg_right _ bot_le
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hcount z hz)
    · simp only [Set.indicator_of_notMem hz,mul_zero]
      exact bot_le
  have hh := lintegral_mono hpoint (μ:=μ)
  rw [lintegral_const_mul _ (hw.indicator hF)] at hh
  rw [lintegral_indicator hF] at hh
  rw [lintegral_finsetSum _ (fun i hi => hw.indicator (hE i hi))] at hh
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_indicator (hE i hi) _
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MiddleObservationBridge
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
lemma shortfallObservation_shift (k : ℝ) {R : ℕ} (a : Fin R → ℤ) (n : Fin R → ℕ)
    (F : (Fin R → ℝ) → ℝ) (b : ℤ) (z : Torus) :
    shortfallObservation k a n F (torusIter k b z)=shortfallObservation k (fun j => a j+b) n F z := by
  unfold shortfallObservation
  congr 1
  funext j
  exact torusShortfall_shift k z (a j) b (n j)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_FastBridge
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
lemma fastBridgeConstant_ne_top : fastBridgeConstant≠∞ := by
  exact ENNReal.mul_ne_top (by norm_num) middleBridgeConstant_ne_top
lemma actual_fast_bridge_product (k : ℝ) (hc : BridgeScalarControl k)
    (N r : ℕ) (hN : 100 ≤ N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
    {Rw Rh : ℕ} (aw : Fin Rw → ℤ) (nw : Fin Rw → ℕ) (Fw : (Fin Rw → ℝ) → ℝ)
    (ah : Fin Rh → ℤ) (nh : Fin Rh → ℕ) (Fh : (Fin Rh → ℝ) → ℝ)
    (hnw : ∀ j, 0 < nw j) (hnh : ∀ j, 0 < nh j) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hlenw : ∀ j, nw j ≤ 2*r) (hlenh : ∀ j, nh j ≤ 2*r)
    (hwinw : ∀ j l, 1 ≤ l → l ≤ nw j → (aw j+(l:ℤ)-1).natAbs ≤ r)
    (hwinh : ∀ j l, 1 ≤ l → l ≤ nh j → (ah j+(l:ℤ)-1-(N:ℤ)).natAbs ≤ r)
    (hW0 : ∀ z, 0 ≤ shortfallObservation k aw nw Fw z)
    (hlog : 1 ≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L ≤ growthBase k)
    (h : ℝ) (hδ : growthBase k^(-(1/10:ℝ)*(N:ℝ)) < h/2) :
    (∫⁻ z in {z | torusFastBridge k z N} ∩ {z | h < shortfallObservation k ah nh Fh z},
      ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area) ≤
      fastBridgeConstant*((∫⁻ z, ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area)+
        ENNReal.ofReal (growthBase k^(-(1/10:ℝ)*(N:ℝ))))*
          area {z | h/2 < shortfallObservation k ah nh Fh z} := by
  classical
  let W := shortfallObservation k aw nw Fw
  let H := shortfallObservation k ah nh Fh
  have hW : Continuous W := continuous_shortfall_observation k hc.nonneg _ _ _ hFw.continuous
  have hH : Continuous H := continuous_shortfall_observation k hc.nonneg _ _ _ hFh.continuous
  let E : ℕ → Set Torus := fun i => (torusIter k (i:ℤ) ⁻¹' middlePrefixEvent k (N-i) i) ∩ {z | h < H z}
  let F : Set Torus := {z | torusFastBridge k z N} ∩ {z | h < H z}
  have hE (i : ℕ) : MeasurableSet (E i) :=
    ((measurableSet_middlePrefixEvent k (N-i) i).preimage (continuous_torusIter k _).measurable).inter
      (isOpen_lt continuous_const hH).measurableSet
  have hF : MeasurableSet F := (measurableSet_torusFastBridge k N).inter (isOpen_lt continuous_const hH).measurableSet
  have hEeq : E = (fun i : ℕ => (torusIter k (i:ℤ) ⁻¹' middlePrefixEvent k (N-i) i) ∩ {z | h < H z}) := rfl
  clear_value E
  have hcovers := lintegral_count_cover area (bridgeMiddle N) E (fun i _ => hE i) F hF
    (fun z => ENNReal.ofReal (W z)) hW.measurable.ennreal_ofReal ((N:ℝ)/5) (by
      intro z hz
      have hcount := torus_good_middles_count k hc.nonneg N hN z hz.1
      apply hcount.trans
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro i hi
      simp only [torusGoodMiddles,Finset.mem_filter] at hi
      rw [Finset.mem_filter]
      refine ⟨hi.1,?_⟩
      rw [hEeq]
      exact ⟨hi.2,hz.2⟩)
  let K := middleBridgeConstant*((∫⁻ z, ENNReal.ofReal (W z) ∂area)+
      ENNReal.ofReal (growthBase k^(-(1/10:ℝ)*(N:ℝ))))*area {z | h/2 < H z}
  have hsum : (∑ i∈bridgeMiddle N, ∫⁻ z in E i, ENNReal.ofReal (W z) ∂area) ≤ (N:ℝ≥0∞)*K := by
    calc
      _ ≤ ∑ _i∈bridgeMiddle N, K := Finset.sum_le_sum fun i hi => by
        rw [hEeq]
        exact middle_observation_product_q44 k hc N r i hN hi hr aw nw Fw ah nh Fh hnw hnh L hFw hFh
          hlenw hlenh hwinw hwinh hW0 hlog hLM h hδ
      _ = ((bridgeMiddle N).card:ℝ≥0∞)*K := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ bot_le
        apply Nat.cast_le.mpr
        calc
          (bridgeMiddle N).card ≤ (Finset.range N).card := Finset.card_le_card (by
            intro i hi
            have hb := bridgeMiddle_bounds N i hN hi
            exact Finset.mem_range.mpr (by omega))
          _ = N := Finset.card_range N
  have hpos : 0 < (N:ℝ)/5 := by
    have : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  have hetop : ENNReal.ofReal ((N:ℝ)/5)≠∞ := ENNReal.ofReal_ne_top
  have hemul : (N:ℝ≥0∞)*K=ENNReal.ofReal ((N:ℝ)/5)*(5*K) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<5),ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
    calc
      _ = ((N:ℝ≥0∞)/5*5)*K := by rw [ENNReal.div_mul_cancel (by norm_num : (5:ℝ≥0∞)≠0) (by norm_num : (5:ℝ≥0∞)≠∞)]
      _ = _ := by ac_rfl
  have htot := hcovers.trans hsum
  rw [hemul] at htot
  have hfinal := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hpos).ne' hetop).mp htot
  simpa only [F,W,H,K,fastBridgeConstant,mul_assoc] using hfinal
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeRealBound
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
lemma strict_markov_real {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (H : X → ℝ) (hi : Integrable H μ) (h0 : ∀ x,0≤H x) (h : ℝ) (hh : 0<h) :
    μ {x | h<H x} ≤ ENNReal.ofReal ((∫ x,H x ∂μ)/h) := by
  have hb := meas_ge_le_lintegral_div hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (ENNReal.ofReal_ne_zero_iff.mpr hh) ENNReal.ofReal_ne_top
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall h0)] at hb
  have hs : {x | h<H x} ⊆ {x | ENNReal.ofReal h≤ENNReal.ofReal (H x)} := fun x hx => ENNReal.ofReal_le_ofReal hx.le
  exact (measure_mono hs).trans (hb.trans_eq (ENNReal.ofReal_div_of_pos hh).symm)
lemma real_integral_bound_of_lintegral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (W : X → ℝ) (hi : Integrable W μ) (h0 : ∀ x,0≤W x) (E : Set X)
    (C : ℝ) (hC : 0≤C) (hb : (∫⁻ x in E,ENNReal.ofReal (W x) ∂μ)≤ENNReal.ofReal C) :
    (∫ x in E,W x ∂μ) ≤ C := by
  rw [←ofReal_integral_eq_lintegral_ofReal hi.restrict (Eventually.of_forall h0)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hb
lemma bridgeRealConstant_nonneg : 0≤bridgeRealConstant := ENNReal.toReal_nonneg
lemma actual_fast_bridge_real (k : ℝ) (hc : BridgeScalarControl k)
    (N r : ℕ) (hN : 100 ≤ N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
    {Rw Rh : ℕ} (aw : Fin Rw → ℤ) (nw : Fin Rw → ℕ) (Fw : (Fin Rw → ℝ) → ℝ)
    (ah : Fin Rh → ℤ) (nh : Fin Rh → ℕ) (Fh : (Fin Rh → ℝ) → ℝ)
    (hnw : ∀ j, 0 < nw j) (hnh : ∀ j, 0 < nh j) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hlenw : ∀ j, nw j ≤ 2*r) (hlenh : ∀ j, nh j ≤ 2*r)
    (hwinw : ∀ j l, 1 ≤ l → l ≤ nw j → (aw j+(l:ℤ)-1).natAbs ≤ r)
    (hwinh : ∀ j l, 1 ≤ l → l ≤ nh j → (ah j+(l:ℤ)-1-(N:ℤ)).natAbs ≤ r)
    (hW0 : ∀ z, 0 ≤ shortfallObservation k aw nw Fw z)
    (hH0 : ∀ z, 0 ≤ shortfallObservation k ah nh Fh z)
    (hlog : 1 ≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L ≤ growthBase k)
    (h : ℝ) (hh : 0<h) (hδ : growthBase k^(-(1/10:ℝ)*(N:ℝ)) < h/2) :
    (∫ z in {z | torusFastBridge k z N} ∩ {z | h < shortfallObservation k ah nh Fh z},
      shortfallObservation k aw nw Fw z ∂area) ≤
      bridgeRealConstant*((∫ z,shortfallObservation k aw nw Fw z ∂area)+
        growthBase k^(-(1/10:ℝ)*(N:ℝ)))*((∫ z,shortfallObservation k ah nh Fh z ∂area)/(h/2)) := by
  have hW := continuous_shortfall_observation k hc.nonneg aw nw Fw hFw.continuous
  have hH := continuous_shortfall_observation k hc.nonneg ah nh Fh hFh.continuous
  have hiW := hW.integrable_of_hasCompactSupport (μ := area) (HasCompactSupport.of_compactSpace _)
  have hiH := hH.integrable_of_hasCompactSupport (μ := area) (HasCompactSupport.of_compactSpace _)
  have hb := actual_fast_bridge_product k hc N r hN hr aw nw Fw ah nh Fh hnw hnh L hFw hFh
    hlenw hlenh hwinw hwinh hW0 hlog hLM h hδ
  have hd0 : 0≤growthBase k^(-(1/10:ℝ)*(N:ℝ)) := Real.rpow_nonneg (by linarith [growthBase_ge_four k hc.nonneg]) _
  have hiW0 := integral_nonneg_of_ae (μ := area) (Eventually.of_forall hW0)
  have hiH0 := integral_nonneg_of_ae (μ := area) (Eventually.of_forall hH0)
  apply real_integral_bound_of_lintegral area _ hiW hW0 _ _
    (mul_nonneg (mul_nonneg bridgeRealConstant_nonneg (add_nonneg hiW0 hd0)) (div_nonneg hiH0 (by linarith)))
  have hm := strict_markov_real area _ hiH hH0 (h/2) (by linarith)
  apply (hb.trans (mul_le_mul_of_nonneg_left hm bot_le)).trans_eq
  change fastBridgeConstant*((∫⁻ z,ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area)+ENNReal.ofReal (growthBase k^(-(1/10:ℝ)*(N:ℝ))))*ENNReal.ofReal ((∫ z,shortfallObservation k ah nh Fh z ∂area)/(h/2))=_
  rw [←ofReal_integral_eq_lintegral_ofReal (f := shortfallObservation k aw nw Fw) hiW (Eventually.of_forall hW0),
    ←ENNReal.ofReal_add hiW0 hd0]
  conv_lhs => rw [show fastBridgeConstant=ENNReal.ofReal bridgeRealConstant from (ENNReal.ofReal_toReal fastBridgeConstant_ne_top).symm]
  rw [
    ←ENNReal.ofReal_mul bridgeRealConstant_nonneg,←ENNReal.ofReal_mul (mul_nonneg bridgeRealConstant_nonneg (add_nonneg hiW0 hd0))]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeSamples
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
lemma continuous_arrayObservation {R : ℕ} (a b : Fin R → DyadicTime)
    (F : (Fin R → ℝ) → ℝ) (hF : Continuous F) : Continuous (arrayObservation a b F) :=
  hF.comp (continuous_pi fun i => continuous_arrayShortfall (a i) (b i))
lemma arrayObservation_sample {R : ℕ} (k : ℝ) (hk : 0≤ k) (n : ℕ) (hn : 0< n)
    (a b : Fin R → DyadicTime) (A : Fin R → ℤ) (m : Fin R → ℕ) (hm : ∀i,0< m i)
    (ha : ∀i,(n:ℝ)*(a i:ℝ)=(A i:ℝ)) (hb : ∀i,(n:ℝ)*(b i:ℝ)=(A i:ℝ)+(m i:ℝ))
    (F : (Fin R → ℝ) → ℝ) (z : Torus) :
    arrayObservation a b F (sampleArray k hk z n hn)=shortfallObservation k A m F z := by
  unfold arrayObservation shortfallObservation
  congr 1
  funext i
  exact shortfall_sample_aligned k hk z n hn (a i) (b i) (A i) (m i) (hm i) (ha i) (hb i)
lemma array_fast_sample (k : ℝ) (hk : 0≤ k) (z : Torus) (n : ℕ) (hn : 0< n)
    (u v : DyadicTime) (a : ℤ) (N : ℕ)
    (hu : (n:ℝ)*(u:ℝ)=(a:ℝ)) (hv : (n:ℝ)*(v:ℝ)=(a:ℝ)+(N:ℝ))
    (hf : (999/1000:ℝ)*((v:ℝ)-(u:ℝ))< (sampleArray k hk z n hn).val u v) :
    torusFastBridge k (torusIter k a z) N := by
  change _< rescaledDistance k z n u v at hf
  rw [rescaledDistance_aligned k z n u v a (a+(N:ℤ)) hu (by push_cast; exact hv),
    productDistance_forward] at hf
  have hshift := torusSegmentTransfer_shift k z 0 a N
  rw [zero_add] at hshift
  unfold torusFastBridge
  rw [hshift,Real.rpow_le_iff_le_log (by linarith [growthBase_ge_four k hk])
    (lt_of_lt_of_le zero_lt_one (torusSegmentTransfer_norm_bounds k hk z a N).1)]
  have hnp : (0:ℝ)< n := by exact_mod_cast hn
  have hg : 0< Real.log (growthBase k) := log_growthBase_pos k hk
  have hl : (n:ℝ)*((v:ℝ)-(u:ℝ))=N := by linarith
  have he := (lt_div_iff₀ hnp).mp hf
  have he' := (lt_div_iff₀ hg).mp he
  nlinarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgePattern
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
lemma sample_bridge_integral (k : ℝ) (hc : BridgeScalarControl k)
    (n N r : ℕ) (hn : 0< n) (hN : 100≤ N) (hr : (r:ℝ)≤ (N:ℝ)/1000)
    (u v : DyadicTime) (b : ℤ) (hu : (n:ℝ)*(u:ℝ)=(b:ℝ)) (hv : (n:ℝ)*(v:ℝ)=(b:ℝ)+(N:ℝ))
    {Rw Rh : ℕ} (sw tw : Fin Rw → DyadicTime) (sh th : Fin Rh → DyadicTime)
    (aw : Fin Rw → ℤ) (nw : Fin Rw → ℕ) (Fw : (Fin Rw → ℝ) → ℝ)
    (ah : Fin Rh → ℤ) (nh : Fin Rh → ℕ) (Fh : (Fin Rh → ℝ) → ℝ)
    (hnw : ∀j,0< nw j) (hnh : ∀j,0< nh j)
    (hsw : ∀j,(n:ℝ)*(sw j:ℝ)=((aw j+b):ℤ))
    (htw : ∀j,(n:ℝ)*(tw j:ℝ)=((aw j+b):ℤ)+(nw j:ℝ))
    (hsh : ∀j,(n:ℝ)*(sh j:ℝ)=((ah j+b):ℤ))
    (hth : ∀j,(n:ℝ)*(th j:ℝ)=((ah j+b):ℤ)+(nh j:ℝ))
    (L : NNReal) (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hlenw : ∀j,nw j≤ 2*r) (hlenh : ∀j,nh j≤ 2*r)
    (hwinw : ∀j l,1≤ l → l≤ nw j → (aw j+(l:ℤ)-1).natAbs≤ r)
    (hwinh : ∀j l,1≤ l → l≤ nh j → (ah j+(l:ℤ)-1-(N:ℤ)).natAbs≤ r)
    (hW0 : ∀z,0≤ shortfallObservation k aw nw Fw z)
    (hH0 : ∀z,0≤ shortfallObservation k ah nh Fh z)
    (hlog : 1≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L≤ growthBase k)
    (η : ℝ) (hη : 0<η) (hδ : growthBase k^(-(1/10:ℝ)*(N:ℝ))<η/2)
    (F : DistanceArray → ℝ) (hF : Continuous F) (D : ℝ) (hD : 0≤ D)
    (hFW : ∀d,F d≤ D*arrayObservation sw tw Fw d)
    (hzero : ∀d,¬((999/1000:ℝ)*((v:ℝ)-(u:ℝ))< d.val u v ∧ η< arrayObservation sh th Fh d) → F d=0) :
    (∫ d,F d ∂sampleLaw k hc.nonneg n hn)≤ D*bridgeRealConstant*
      ((∫ d,arrayObservation sw tw Fw d ∂sampleLaw k hc.nonneg n hn)+growthBase k^(-(1/10:ℝ)*(N:ℝ)))*
      ((∫ d,arrayObservation sh th Fh d ∂sampleLaw k hc.nonneg n hn)/(η/2)) := by
  let W := shortfallObservation k aw nw Fw
  let H := shortfallObservation k ah nh Fh
  let E := {z | torusFastBridge k z N} ∩ {z | η< H z}
  have hW : Continuous W := continuous_shortfall_observation k hc.nonneg _ _ _ hFw.continuous
  have hH : Continuous H := continuous_shortfall_observation k hc.nonneg _ _ _ hFh.continuous
  have hiW := hW.integrable_of_hasCompactSupport (μ := area) (HasCompactSupport.of_compactSpace _)
  have hE : MeasurableSet E := (measurableSet_torusFastBridge k N).inter (isOpen_lt continuous_const hH).measurableSet
  have heW (z : Torus) : arrayObservation sw tw Fw (sampleArray k hc.nonneg z n hn)=W (torusIter k b z) := by
    rw [arrayObservation_sample k hc.nonneg n hn sw tw (fun j => aw j+b) nw hnw hsw htw Fw]
    exact (shortfallObservation_shift k aw nw Fw b z).symm
  have heH (z : Torus) : arrayObservation sh th Fh (sampleArray k hc.nonneg z n hn)=H (torusIter k b z) := by
    rw [arrayObservation_sample k hc.nonneg n hn sh th (fun j => ah j+b) nh hnh hsh hth Fh]
    exact (shortfallObservation_shift k ah nh Fh b z).symm
  have hiI : Integrable (fun z => E.indicator W (torusIter k b z)) area :=
    (measurePreserving_torusIter k b).integrable_comp_of_integrable (hiW.indicator hE)
  have hbound : (∫ z,F (sampleArray k hc.nonneg z n hn) ∂area)≤ D*(∫ z in E,W z ∂area) := by
    rw [←integral_indicator hE,←integral_torusIter k b (E.indicator W),←integral_const_mul]
    apply integral_mono ((hF.comp (continuous_sampleArray k hc.nonneg n hn)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (hiI.const_mul D)
    intro z
    dsimp only [Function.comp_apply]
    by_cases hz : torusIter k b z∈E
    · rw [indicator_of_mem hz]
      simpa only [heW] using hFW (sampleArray k hc.nonneg z n hn)
    · rw [indicator_of_notMem hz,mul_zero]
      have hfz : F (sampleArray k hc.nonneg z n hn)=0 := hzero _ (by
        intro h
        apply hz
        exact ⟨array_fast_sample k hc.nonneg z n hn u v b N hu hv h.1,by simpa only [Set.mem_ofPred_eq,←heH z] using h.2⟩)
      exact hfz.le
  have hwint : (∫ d,arrayObservation sw tw Fw d ∂sampleLaw k hc.nonneg n hn)=∫ z,W z ∂area := by
    rw [integral_sampleLaw k hc.nonneg n hn _ (continuous_arrayObservation sw tw Fw hFw.continuous)]
    simp_rw [heW]
    exact integral_torusIter k b W
  have hhint : (∫ d,arrayObservation sh th Fh d ∂sampleLaw k hc.nonneg n hn)=∫ z,H z ∂area := by
    rw [integral_sampleLaw k hc.nonneg n hn _ (continuous_arrayObservation sh th Fh hFh.continuous)]
    simp_rw [heH]
    exact integral_torusIter k b H
  rw [integral_sampleLaw k hc.nonneg n hn F hF,hwint,hhint]
  have hb := actual_fast_bridge_real k hc N r hN hr aw nw Fw ah nh Fh hnw hnh L hFw hFh hlenw hlenh
    hwinw hwinh hW0 hH0 hlog hLM η hη hδ
  exact hbound.trans ((mul_le_mul_of_nonneg_left hb hD).trans_eq (by dsimp only [W,H]; ring))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeDecay
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
lemma bridge_error_geom (M : ℝ) (hM : (2:ℝ)^10≤ M) (N j : ℕ) (_hN : 1≤ N) :
    M^(-(1/10:ℝ)*((N*2^j:ℕ):ℝ))≤ (1/2:ℝ)^(N*2^j) := by
  have hMp : 0< M := lt_of_lt_of_le (by norm_num) hM
  have hbase : M^(-(1/10:ℝ))≤ (1/2:ℝ) := by
    rw [Real.rpow_neg hMp.le]
    apply (inv_le_comm₀ (Real.rpow_pos_of_pos hMp _) (by norm_num)).mpr
    have hh := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤ 2^10) hM (by norm_num : (0:ℝ)≤ 1/10)
    norm_num [←Real.rpow_natCast,←Real.rpow_mul] at hh
    simpa using hh
  rw [Real.rpow_mul_natCast hMp.le]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hMp.le _) hbase _
lemma half_pow_nat_le_inverse (N : ℕ) (hN : 1≤ N) : (1/2:ℝ)^N≤ 1/(N:ℝ) := by
  have hh : (N:ℝ)≤ (2:ℝ)^N := by exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n := N)))
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by exact_mod_cast hN) hh
lemma bridge_error_inverse (M : ℝ) (hM : (2:ℝ)^10≤ M) (N j : ℕ) (hN : 1≤ N) :
    M^(-(1/10:ℝ)*((N*2^j:ℕ):ℝ))≤ 1/((N*2^j:ℕ):ℝ) :=
  (bridge_error_geom M hM N j hN).trans (half_pow_nat_le_inverse _ (by have : 0 < N*2^j := Nat.mul_pos (by omega) (by positivity); omega))
lemma bridge_error_sum (M : ℝ) (hM : (2:ℝ)^10≤ M) (N l : ℕ) (hN : 1≤ N) :
    (∑j∈Finset.range l,M^(-(1/10:ℝ)*((N*2^j:ℕ):ℝ)))≤ 2/(N:ℝ) := by
  calc
    _ ≤ ∑j∈Finset.range l,1/((N*2^j:ℕ):ℝ) := Finset.sum_le_sum (fun j _ => bridge_error_inverse M hM N j hN)
    _ = (1/(N:ℝ))*∑j∈Finset.range l,(1/2:ℝ)^j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      rw [div_pow,one_pow,one_div_mul_one_div]
    _ ≤ (1/(N:ℝ))*2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le l) (by positivity)
    _ = _ := by ring
lemma window_indices {a b : ℤ} {m r : ℕ}
    (ha : -(r:ℤ)≤ a-b) (hb : a+(m:ℤ)-b≤ r)
    (l : ℕ) (hl : 1≤ l) (hlm : l≤ m) : (a+(l:ℤ)-1-b).natAbs≤ r := by
  apply Nat.cast_le (α := ℤ) |>.mp
  rw [Int.natCast_natAbs,abs_le]
  constructor <;> omega
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeGrid
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

lemma aligned_scale (p l : ℕ) (s : DyadicTime) (a : ℤ)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ)) :
    ((2^(p+l):ℕ):ℝ)*(s:ℝ)=((a*2^l:ℤ):ℝ) := by
  push_cast at hs ⊢
  rw [pow_add]
  nlinarith [congrArg (fun x : ℝ => x*(2:ℝ)^l) hs]
lemma aligned_scale_end (p l : ℕ) (s : DyadicTime) (a : ℤ) (m : ℕ)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ)+(m:ℝ)) :
    ((2^(p+l):ℕ):ℝ)*(s:ℝ)=((a*2^l:ℤ):ℝ)+((m*2^l:ℕ):ℝ) := by
  have hh := aligned_scale p l s (a+(m:ℤ)) (by simpa only [Int.cast_add,Int.cast_natCast] using hs)
  push_cast at hh ⊢
  nlinarith
lemma observation_nonneg_aligned {R : ℕ} (k : ℝ) (hk : 0≤ k) (n : ℕ) (hn : 0< n)
    (s t : Fin R → DyadicTime) (a : Fin R → ℤ) (m : Fin R → ℕ) (hm : ∀i,0< m i)
    (hs : ∀i,(n:ℝ)*(s i:ℝ)=(a i:ℝ)) (ht : ∀i,(n:ℝ)*(t i:ℝ)=(a i:ℝ)+(m i:ℝ))
    (F : (Fin R → ℝ) → ℝ) (hF0 : ∀d,0≤ arrayObservation s t F d) :
    ∀z,0≤ shortfallObservation k a m F z := by
  intro z
  rw [←arrayObservation_sample k hk n hn s t a m hm hs ht F]
  exact hF0 _
lemma length_from_window (a : ℤ) (m r : ℕ) (h1 : -(r:ℤ)≤ a) (h2 : a+(m:ℤ)≤ r) : m≤ 2*r := by omega
lemma BridgeGrid.sample_bound {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (k : ℝ) (hc : BridgeScalarControl k) (l : ℕ)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hW0 : ∀d,0≤ arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤ arrayObservation B.sh B.th Fh d)
    (hlog : 1≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L≤ growthBase k)
    (η : ℝ) (hη : 0<η) (hδ : growthBase k^(-(1/10:ℝ)*((B.N*2^l:ℕ):ℝ))<η/2)
    (F : DistanceArray → ℝ) (hF : Continuous F) (D : ℝ) (hD : 0≤ D)
    (hFW : ∀d,F d≤ D*arrayObservation B.sw B.tw Fw d)
    (hzero : ∀d,¬((999/1000:ℝ)*((B.v:ℝ)-(B.u:ℝ))< d.val B.u B.v ∧ η< arrayObservation B.sh B.th Fh d) → F d=0) :
    (∫ d,F d ∂sampleLaw k hc.nonneg (2^(B.p+l)) (by positivity))≤ D*bridgeRealConstant*
      ((∫ d,arrayObservation B.sw B.tw Fw d ∂sampleLaw k hc.nonneg (2^(B.p+l)) (by positivity))+
        growthBase k^(-(1/10:ℝ)*((B.N*2^l:ℕ):ℝ)))*
      ((∫ d,arrayObservation B.sh B.th Fh d ∂sampleLaw k hc.nonneg (2^(B.p+l)) (by positivity))/(η/2)) := by
  have hp : (0:ℤ)≤ 2^l := by positivity
  have h1 : 1≤ 2^l := Nat.one_le_pow l 2 (by omega)
  have hwL (j) : -((B.r*2^l:ℕ):ℤ)≤ B.aw j*2^l := by
    have hh := mul_le_mul_of_nonneg_right (B.hwleft j) hp
    push_cast; nlinarith
  have hwR (j) : B.aw j*2^l+((B.nw j*2^l:ℕ):ℤ)≤ ((B.r*2^l:ℕ):ℤ) := by
    have hh := mul_le_mul_of_nonneg_right (B.hwright j) hp
    push_cast; nlinarith
  have hhL (j) : -((B.r*2^l:ℕ):ℤ)≤ B.ah j*2^l-((B.N*2^l:ℕ):ℤ) := by
    have hh := mul_le_mul_of_nonneg_right (B.hhleft j) hp
    push_cast; nlinarith
  have hhR (j) : B.ah j*2^l+((B.nh j*2^l:ℕ):ℤ)-((B.N*2^l:ℕ):ℤ)≤ ((B.r*2^l:ℕ):ℤ) := by
    have hh := mul_le_mul_of_nonneg_right (B.hhright j) hp
    push_cast; nlinarith
  have hsw (j) : ((2^(B.p+l):ℕ):ℝ)*(B.sw j:ℝ)=(((B.aw j*2^l+B.b*2^l):ℤ):ℝ) := by
    simpa only [add_mul] using aligned_scale B.p l (B.sw j) (B.aw j+B.b) (B.hsw j)
  have htw (j) : ((2^(B.p+l):ℕ):ℝ)*(B.tw j:ℝ)=(((B.aw j*2^l+B.b*2^l):ℤ):ℝ)+((B.nw j*2^l:ℕ):ℝ) := by
    simpa only [add_mul] using aligned_scale_end B.p l (B.tw j) (B.aw j+B.b) (B.nw j) (B.htw j)
  have hsh (j) : ((2^(B.p+l):ℕ):ℝ)*(B.sh j:ℝ)=(((B.ah j*2^l+B.b*2^l):ℤ):ℝ) := by
    simpa only [add_mul] using aligned_scale B.p l (B.sh j) (B.ah j+B.b) (B.hsh j)
  have hth (j) : ((2^(B.p+l):ℕ):ℝ)*(B.th j:ℝ)=(((B.ah j*2^l+B.b*2^l):ℤ):ℝ)+((B.nh j*2^l:ℕ):ℝ) := by
    simpa only [add_mul] using aligned_scale_end B.p l (B.th j) (B.ah j+B.b) (B.nh j) (B.hth j)
  have hnonnegW : ∀z,0≤ shortfallObservation k (fun j => B.aw j*2^l) (fun j => B.nw j*2^l) Fw z := by
    intro z
    have hh := observation_nonneg_aligned k hc.nonneg (2^(B.p+l)) (by positivity) B.sw B.tw
      (fun j => B.aw j*2^l+B.b*2^l) (fun j => B.nw j*2^l) (fun j => Nat.mul_pos (B.pw j) (by positivity)) hsw htw Fw hW0
      (torusIter k (-(B.b*2^l)) z)
    rw [←shortfallObservation_shift,←torusIter_add,add_neg_cancel,torusIter_zero] at hh
    exact hh
  have hnonnegH : ∀z,0≤ shortfallObservation k (fun j => B.ah j*2^l) (fun j => B.nh j*2^l) Fh z := by
    intro z
    have hh := observation_nonneg_aligned k hc.nonneg (2^(B.p+l)) (by positivity) B.sh B.th
      (fun j => B.ah j*2^l+B.b*2^l) (fun j => B.nh j*2^l) (fun j => Nat.mul_pos (B.ph j) (by positivity)) hsh hth Fh hH0
      (torusIter k (-(B.b*2^l)) z)
    rw [←shortfallObservation_shift,←torusIter_add,add_neg_cancel,torusIter_zero] at hh
    exact hh
  apply sample_bridge_integral k hc (2^(B.p+l)) (B.N*2^l) (B.r*2^l) (by positivity)
    (le_trans B.large (Nat.le_mul_of_pos_right _ (by positivity)))
    (by push_cast; nlinarith [mul_le_mul_of_nonneg_right B.narrow (show (0:ℝ)≤ 2^l by positivity)])
    B.u B.v (B.b*2^l) (aligned_scale B.p l B.u B.b B.hu) (aligned_scale_end B.p l B.v B.b B.N B.hv)
    B.sw B.tw B.sh B.th (fun j => B.aw j*2^l) (fun j => B.nw j*2^l) Fw
    (fun j => B.ah j*2^l) (fun j => B.nh j*2^l) Fh
    (fun j => Nat.mul_pos (B.pw j) (by positivity)) (fun j => Nat.mul_pos (B.ph j) (by positivity))
    hsw htw hsh hth L hFw hFh
    (fun j => length_from_window _ _ _ (hwL j) (hwR j))
    (fun j => length_from_window (B.ah j*2^l-((B.N*2^l:ℕ):ℤ)) _ _ (hhL j) (by linarith [hhR j]))
    (fun j x hx hx' => by simpa only [sub_zero] using window_indices (a := B.aw j*2^l) (b := 0) (r := B.r*2^l) (by simpa only [sub_zero] using hwL j) (by simpa only [sub_zero] using hwR j) x hx hx')
    (fun j x hx hx' => window_indices (hhL j) (hhR j) x hx hx')
    hnonnegW hnonnegH hlog hLM η hη hδ F hF D hD hFW hzero
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ProductSum
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open scoped BigOperators
namespace StandardMapEntropy
lemma sum_product_error (s : Finset ℕ) (A B E : ℕ → ℝ) (C ε T : ℝ)
    (hC : 0≤ C) (hε : 0≤ ε)
    (hA : ∀j∈s,0≤ A j) (hB : ∀j∈s,0≤ B j) (hE : ∀j∈s,0≤ E j)
    (hAC : ∀j∈s,A j≤ C*ε) (hBC : ∀j∈s,B j≤ C*ε)
    (hT : (∑j∈s,A j)≤ T*ε ∨ (∑j∈s,B j)≤ T*ε) :
    (∑j∈s,(A j+E j)*B j)≤ C*ε*(T*ε+∑j∈s,E j) := by
  have hp : (∑j∈s,A j*B j)≤ C*ε*(T*ε) := by
    rcases hT with hT|hT
    · calc
        _ ≤ ∑j∈s,A j*(C*ε) := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hBC j hj) (hA j hj))
        _ = (∑j∈s,A j)*(C*ε) := by rw [Finset.sum_mul]
        _ ≤ (T*ε)*(C*ε) := mul_le_mul_of_nonneg_right hT (mul_nonneg hC hε)
        _ = _ := mul_comm _ _
    · calc
        _ ≤ ∑j∈s,(C*ε)*B j := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hAC j hj) (hB j hj))
        _ = C*ε*(∑j∈s,B j) := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left hT (mul_nonneg hC hε)
  have he : (∑j∈s,E j*B j)≤ C*ε*(∑j∈s,E j) := by
    calc
      _ ≤ ∑j∈s,E j*(C*ε) := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hBC j hj) (hE j hj))
      _ = _ := by rw [←Finset.sum_mul]; ring
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib,mul_add]
  exact add_le_add hp he
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeAggregate
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
lemma BridgeGrid.scale_bound_q44_oai {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (k : ℝ) (hc : BridgeScalarControl k) (lo len : ℕ) (ε : ℝ) (hε : 0< ε)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hW0 : ∀d,0≤ arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤ arrayObservation B.sh B.th Fh d)
    (hlog : 1≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L≤ growthBase k)
    (hM : (2:ℝ)^10≤ growthBase k) (η : ℝ) (hη : 0<η)
    (hδ : 1/((B.N*2^lo:ℕ):ℝ)<η/2)
    (F : DistanceArray → ℝ) (hF : Continuous F) (D : ℝ) (hD : 0≤ D)
    (hFW : ∀d,F d≤ D*arrayObservation B.sw B.tw Fw d)
    (hzero : ∀d,¬((999/1000:ℝ)*((B.v:ℝ)-(B.u:ℝ))< d.val B.u B.v ∧ η< arrayObservation B.sh B.th Fh d) → F d=0)
    (C T : ℝ) (hC : 0≤ C)
    (hbW : ∀j<len,(∫ d,arrayObservation B.sw B.tw Fw d ∂sampleLaw k hc.nonneg (2^(B.p+lo+j)) (by positivity))≤ C*ε)
    (hbH : ∀j<len,(∫ d,arrayObservation B.sh B.th Fh d ∂sampleLaw k hc.nonneg (2^(B.p+lo+j)) (by positivity))≤ C*ε)
    (hT : (∫d,arrayObservation B.sw B.tw Fw d ∂scaleLaw k hc.nonneg (B.p+lo) len ε)≤ T ∨
      (∫d,arrayObservation B.sh B.th Fh d ∂scaleLaw k hc.nonneg (B.p+lo) len ε)≤ T) :
    (∫d,F d ∂scaleLaw k hc.nonneg (B.p+lo) len ε)≤
      (D*bridgeRealConstant/(η/2))*C*(T*ε+2/((B.N*2^lo:ℕ):ℝ)) := by
  let A (j : ℕ) := ∫d,arrayObservation B.sw B.tw Fw d ∂sampleLaw k hc.nonneg (2^(B.p+lo+j)) (by positivity)
  let H (j : ℕ) := ∫d,arrayObservation B.sh B.th Fh d ∂sampleLaw k hc.nonneg (2^(B.p+lo+j)) (by positivity)
  let E (j : ℕ) := growthBase k^(-(1/10:ℝ)*((B.N*2^(lo+j):ℕ):ℝ))
  let V (j : ℕ) := ∫d,F d ∂sampleLaw k hc.nonneg (2^(B.p+lo+j)) (by positivity)
  have hNp : 1≤ B.N*2^lo := by
    have hN : 0< B.N := by have := B.large; omega
    have hh : 0< B.N*2^lo := Nat.mul_pos hN (by positivity)
    omega
  have hE0 (j) : 0≤ E j := by apply Real.rpow_nonneg; linarith [growthBase_ge_four k hc.nonneg]
  have hEb (j) : E j≤1/((B.N*2^lo:ℕ):ℝ) := by
    have hh := bridge_error_inverse (growthBase k) hM (B.N*2^lo) j hNp
    have he : B.N*2^(lo+j)=(B.N*2^lo)*2^j := by rw [pow_add,mul_assoc]
    dsimp [E]
    rw [he]
    apply hh.trans
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.le_mul_of_pos_right (B.N*2^lo) (by positivity : 0<2^j)
  have hEs : (∑j∈Finset.range len,E j)≤2/((B.N*2^lo:ℕ):ℝ) := by
    simpa only [E,pow_add,mul_assoc] using bridge_error_sum (growthBase k) hM (B.N*2^lo) len hNp
  have hV (j) : V j≤ (D*bridgeRealConstant/(η/2))*((A j+E j)*H j) := by
    have hh := B.sample_bound k hc (lo+j) Fw Fh L hFw hFh hW0 hH0 hlog hLM η hη ((hEb j).trans_lt hδ)
      F hF D hD hFW hzero
    dsimp only [V,A,E,H]
    simpa only [Nat.add_assoc,mul_div_assoc,mul_assoc,div_mul_eq_mul_div] using hh
  have hT' : (∑j∈Finset.range len,A j)≤T*ε ∨ (∑j∈Finset.range len,H j)≤T*ε := by
    rcases hT with hT|hT
    · left
      rw [integral_scaleLaw k hc.nonneg (B.p+lo) len ε hε _ (continuous_arrayObservation _ _ _ hFw.continuous)] at hT
      exact (div_le_iff₀ hε).mp hT
    · right
      rw [integral_scaleLaw k hc.nonneg (B.p+lo) len ε hε _ (continuous_arrayObservation _ _ _ hFh.continuous)] at hT
      exact (div_le_iff₀ hε).mp hT
  have hp := sum_product_error (Finset.range len) A H E C ε T hC hε.le
    (fun j _ => integral_nonneg hW0) (fun j _ => integral_nonneg hH0) (fun j _ => hE0 j)
    (fun j hj => hbW j (Finset.mem_range.mp hj)) (fun j hj => hbH j (Finset.mem_range.mp hj)) hT'
  have hd : 0≤ D*bridgeRealConstant/(η/2) := div_nonneg (mul_nonneg hD bridgeRealConstant_nonneg) (by linarith)
  rw [integral_scaleLaw k hc.nonneg (B.p+lo) len ε hε F hF]
  apply (div_le_iff₀ hε).mpr
  calc
    _ ≤ ∑j∈Finset.range len,(D*bridgeRealConstant/(η/2))*((A j+E j)*H j) := Finset.sum_le_sum (fun j _ => hV j)
    _ = (D*bridgeRealConstant/(η/2))*(∑j∈Finset.range len,(A j+E j)*H j) := by rw [Finset.mul_sum]
    _ ≤ (D*bridgeRealConstant/(η/2))*(C*ε*(T*ε+∑j∈Finset.range len,E j)) := mul_le_mul_of_nonneg_left hp hd
    _ ≤ (D*bridgeRealConstant/(η/2))*(C*ε*(T*ε+2/((B.N*2^lo:ℕ):ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add le_rfl hEs) (mul_nonneg hC hε.le)) hd
    _ = _ := by ring
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.BridgeGrid.scale_bound_q44_oai := @OAI.StandardMapEntropy.BridgeGrid.scale_bound_q44_oai
