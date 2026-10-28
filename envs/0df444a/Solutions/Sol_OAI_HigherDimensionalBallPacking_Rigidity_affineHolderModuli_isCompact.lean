-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.affineHolderModuli_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T16:57:43.465178+00:00
-- url     : https://prove2.me/submissions/e68cfac3-5fba-4c99-96f1-6b82cae40b41

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp005
import Definitions.Def_OAIQ10Bp006
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_homotopy_affine_curve_compactness

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CompatibleStructures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HigherDimensionalBallPacking
open scoped ContDiff

noncomputable section
open scoped Topology
open Set Function Filter

namespace Rigidity

theorem standardForm_J_pos {n : ℕ} {v : Phase n} (hv : v ≠ 0) :
    0 < standardForm v (standardJ n v) := by
  rw [standardForm_J_self]
  have hi : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hi
  have hpos : 0 < Complex.normSq (v i) := Complex.normSq_pos.mpr hi
  exact hpos.trans_le (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j))
    (Finset.mem_univ i))

end Rigidity
end
end HigherDimensionalBallPacking

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity

theorem stdDot_symm {n : ℕ} (v w : Phase n) : stdDot n v w = stdDot n w v := by
  simp only [stdDot_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem stdDot_pos {n : ℕ} {v : Phase n} (hv : v ≠ 0) : 0 < stdDot n v v := by
  rw [← standardForm_J_right]
  exact standardForm_J_pos hv

theorem stdDot_nonneg {n : ℕ} (v : Phase n) : 0 ≤ stdDot n v v := by
  by_cases hv : v = 0
  · subst v
    simp
  · exact (stdDot_pos hv).le

theorem standardForm_skew {n : ℕ} (v w : Phase n) :
    standardForm v w = -standardForm w v := by
  unfold standardForm
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem compatible_metric_symm {n : ℕ} {J : End n} (hJ : Compatible J)
    (v w : Phase n) : standardForm v (J w) = standardForm w (J v) := by
  calc
    standardForm v (J w) = standardForm (J v) (J (J w)) := (hJ.2.1 v (J w)).symm
    _ = -standardForm (J v) w := by rw [hJ.1, standardForm_neg_right]
    _ = standardForm w (J v) := by rw [standardForm_skew, neg_neg]

theorem compatible_of_sq_symmetric_positive {n : ℕ} {J : End n}
    (hJsq : ∀ v, J (J v) = -v)
    (hsym : ∀ v w, standardForm v (J w) = standardForm w (J v))
    (hpos : ∀ v, v ≠ 0 → 0 < standardForm v (J v)) : Compatible J := by
  refine ⟨hJsq, ?_, hpos⟩
  intro v w
  rw [hsym, hJsq, standardForm_neg_right, standardForm_skew, neg_neg]

theorem relativeOperator_selfadjoint {n : ℕ} {J : End n} (hJ : Compatible J)
    (v w : Phase n) :
    stdDot n (relativeOperator J v) w = stdDot n v (relativeOperator J w) := by
  rw [stdDot_symm, stdDot_relativeOperator, stdDot_relativeOperator]
  exact compatible_metric_symm hJ w v

theorem relativeOperator_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {v : Phase n} (hv : v ≠ 0) : 0 < stdDot n v (relativeOperator J v) := by
  rw [stdDot_relativeOperator]
  exact hJ.2.2 v hv

theorem cayleyP_invertible {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : (cayleyP J b a).IsInvertible := by
  have hi : Injective (cayleyP J b a) := by
    apply (injective_iff_map_eq_zero (cayleyP J b a)).mpr
    intro v hv
    by_contra hne
    have hp := stdDot_pos hne
    have hA := relativeOperator_positive hJ hne
    have he : stdDot n v (cayleyP J b a v) =
        b * stdDot n v (relativeOperator J v) + a * stdDot n v v := by
      simp only [cayleyP_apply, map_add, map_smul, smul_eq_mul]
    rw [hv] at he
    simp only [map_zero] at he
    have hn := mul_nonneg hb hA.le
    have hh := mul_pos ha hp
    linarith
  have hs := (LinearMap.injective_iff_surjective (f := (cayleyP J b a).toLinearMap)).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective (cayleyP J b a)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs), rfl⟩

theorem cayleyP_commute {n : ℕ} (J : End n) (a b : ℝ) (v : Phase n) :
    cayleyP J b a (cayleyP J a b v) = cayleyP J a b (cayleyP J b a v) := by
  simp only [cayleyP_apply, map_add, map_smul]
  module

theorem cayleyP_J_identity {n : ℕ} {J : End n} (hJ : Compatible J)
    (a b : ℝ) (v : Phase n) :
    cayleyP J a b (standardJ n (cayleyP J a b v)) =
      cayleyP J b a (standardJ n (cayleyP J b a v)) := by
  simp only [cayleyP_apply, map_add, map_smul, relativeOperator_J_relativeOperator hJ]
  module

theorem cayleyP_stdDot_identity {n : ℕ} {J : End n} (hJ : Compatible J)
    (a b : ℝ) (v w : Phase n) :
    stdDot n (cayleyP J b a v) (cayleyP J a b w) =
      stdDot n (cayleyP J a b v) (cayleyP J b a w) := by
  simp only [cayleyP_apply, map_add, map_smul,
    add_apply, smul_apply, smul_eq_mul]
  rw [relativeOperator_selfadjoint hJ v w]
  ring

theorem cayleyP_stdDot_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) {v : Phase n} (hv : v ≠ 0) :
    0 < stdDot n (cayleyP J b a v) (cayleyP J a b v) := by
  have he : stdDot n (cayleyP J b a v) (cayleyP J a b v) =
      a * b * (stdDot n (relativeOperator J v) (relativeOperator J v) + stdDot n v v) +
      (a ^ 2 + b ^ 2) * stdDot n v (relativeOperator J v) := by
    simp only [cayleyP_apply, map_add, map_smul,
      add_apply, smul_apply, smul_eq_mul]
    rw [relativeOperator_selfadjoint hJ v v]
    ring
  rw [he]
  have hfirst : 0 ≤ a * b *
      (stdDot n (relativeOperator J v) (relativeOperator J v) + stdDot n v v) :=
    mul_nonneg (mul_nonneg ha.le hb) (add_nonneg (stdDot_nonneg _) (stdDot_nonneg _))
  have hcoeff : 0 < a ^ 2 + b ^ 2 := by nlinarith [sq_pos_of_pos ha, sq_nonneg b]
  exact add_pos_of_nonneg_of_pos hfirst (mul_pos hcoeff (relativeOperator_positive hJ hv))

theorem cayleyOperator_on_denominator {n : ℕ} {J : End n} {a b : ℝ}
    (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyOperator J a b (cayleyP J b a v) = cayleyP J a b v := by
  obtain ⟨e,he⟩ := hQ
  simp only [cayleyOperator, ←he, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

theorem denominator_cayleyOperator {n : ℕ} {J : End n} {a b : ℝ}
    (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyP J b a (cayleyOperator J a b v) = cayleyP J a b v := by
  change cayleyP J b a (cayleyP J a b ((cayleyP J b a).inverse v)) = _
  rw [cayleyP_commute]
  obtain ⟨e,he⟩ := hQ
  simp [←he]

theorem cayleyOperator_selfadjoint {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (hQ : (cayleyP J b a).IsInvertible) (v w : Phase n) :
    stdDot n (cayleyOperator J a b v) w = stdDot n v (cayleyOperator J a b w) := by
  obtain ⟨e,he⟩ := hQ
  obtain ⟨x,rfl⟩ := e.surjective v
  obtain ⟨y,rfl⟩ := e.surjective w
  change stdDot n (cayleyOperator J a b ((e : End n) x)) ((e : End n) y) =
    stdDot n ((e : End n) x) (cayleyOperator J a b ((e : End n) y))
  rw [he, cayleyOperator_on_denominator ⟨e,he⟩,
    cayleyOperator_on_denominator ⟨e,he⟩]
  exact (cayleyP_stdDot_identity hJ a b x y).symm

theorem cayleyOperator_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) {v : Phase n} (hv : v ≠ 0) :
    0 < stdDot n v (cayleyOperator J a b v) := by
  obtain ⟨e,he⟩ := cayleyP_invertible hJ ha hb
  obtain ⟨x,rfl⟩ := e.surjective v
  have hx : x ≠ 0 := by simpa using hv
  change 0 < stdDot n ((e : End n) x) (cayleyOperator J a b ((e : End n) x))
  rw [he, cayleyOperator_on_denominator ⟨e,he⟩]
  exact cayleyP_stdDot_positive hJ ha hb hx

theorem cayleyOperator_J_identity {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyOperator J a b (standardJ n (cayleyOperator J a b v)) = standardJ n v := by
  obtain ⟨e,he⟩ := hQ
  obtain ⟨x,rfl⟩ := e.surjective v
  apply e.injective
  change (e : End n) (cayleyOperator J a b (standardJ n (cayleyOperator J a b ((e : End n) x)))) =
    (e : End n) (standardJ n ((e : End n) x))
  rw [he, denominator_cayleyOperator ⟨e,he⟩, cayleyOperator_on_denominator ⟨e,he⟩]
  exact cayleyP_J_identity hJ a b x

theorem compatible_interpolateJ {n : ℕ} {J : End n} (hJ : Compatible J)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Compatible (interpolateJ J t) := by
  have ha : 0 < 1 + t := by linarith [ht.1]
  have hb : 0 ≤ 1 - t := by linarith [ht.2]
  have hQ := cayleyP_invertible hJ ha hb
  apply compatible_of_sq_symmetric_positive
  · intro v
    change standardJ n (cayleyOperator J (1+t) (1-t)
      (standardJ n (cayleyOperator J (1+t) (1-t) v))) = -v
    rw [cayleyOperator_J_identity hJ hQ, standardJ_sq]
  · intro v w
    change standardForm v (standardJ n (cayleyOperator J (1+t) (1-t) w)) =
      standardForm w (standardJ n (cayleyOperator J (1+t) (1-t) v))
    rw [standardForm_J_right, standardForm_J_right,
      ←cayleyOperator_selfadjoint hJ hQ, stdDot_symm]
  · intro v hv
    change 0 < standardForm v (standardJ n (cayleyOperator J (1+t) (1-t) v))
    rw [standardForm_J_right]
    exact cayleyOperator_positive hJ ha hb hv

@[simp] theorem interpolateJ_zero {n : ℕ} {J : End n} (hJ : Compatible J) :
    interpolateJ J 0 = standardJ n := by
  have hQ := cayleyP_invertible hJ (a := 1) (b := 1) (by norm_num) (by norm_num)
  obtain ⟨e,he⟩ := hQ
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator J (1+0) (1-0) ((e : End n) x)) = standardJ n ((e : End n) x)
  simp only [add_zero, sub_zero, he, cayleyOperator_on_denominator ⟨e,he⟩]

@[simp] theorem interpolateJ_one {n : ℕ} {J : End n} (hJ : Compatible J) :
    interpolateJ J 1 = J := by
  have hQ := cayleyP_invertible hJ (a := 2) (b := 0) (by norm_num) (by norm_num)
  obtain ⟨e,he⟩ := hQ
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator J (1+1) (1-1) ((e : End n) x)) = J ((e : End n) x)
  norm_num only [he, show (1:ℝ)+1=2 by norm_num, sub_self,
    cayleyOperator_on_denominator ⟨e,he⟩]
  simp

theorem contDiffAt_interpolateJ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {J : E → End n} {t : E → ℝ} {x : E}
    (hJs : ContDiffAt ℝ ∞ J x) (hts : ContDiffAt ℝ ∞ t x)
    (hJ : Compatible (J x)) (ht : t x ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun y => interpolateJ (J y) (t y)) x := by
  have hA : ContDiffAt ℝ ∞ (fun y => relativeOperator (J y)) x :=
    (contDiffAt_const.clm_comp hJs).neg
  have ha : ContDiffAt ℝ ∞ (fun y => 1 + t y) x := contDiffAt_const.add hts
  have hb : ContDiffAt ℝ ∞ (fun y => 1 - t y) x := contDiffAt_const.sub hts
  have hP : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1+t y) (1-t y)) x :=
    (ha.smul hA).add (hb.smul contDiffAt_const)
  have hQ : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1-t y) (1+t y)) x :=
    (hb.smul hA).add (ha.smul contDiffAt_const)
  have hQi := cayleyP_invertible hJ (show 0 < 1 + t x by linarith [ht.1])
    (show 0 ≤ 1 - t x by linarith [ht.2])
  have hI : ContDiffAt ℝ ∞ (fun y => (cayleyP (J y) (1-t y) (1+t y)).inverse) x :=
    ContDiffAt.comp x (g := ContinuousLinearMap.inverse)
      (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (n := ∞) hQi) hQ
  exact contDiffAt_const.clm_comp (hP.clm_comp hI)

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_Adapted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter

theorem lineHomotopy_compatible {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x : Phase n) :
    Compatible (lineHomotopy J t x) := compatible_interpolateJ (hJ x) ht

@[simp] theorem lineHomotopy_zero {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) (x : Phase n) : lineHomotopy J 0 x = standardJ n :=
  interpolateJ_zero (hJ x)

@[simp] theorem lineHomotopy_one {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) (x : Phase n) : lineHomotopy J 1 x = J x :=
  interpolateJ_one (hJ x)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FreezeJ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity

theorem compatible_standard_frame {n : ℕ} {J : End n} (hJ : Compatible J) :
    ∃ S : Phase n ≃L[ℝ] Phase n, ∀ v,
      S (J v)=Complex.I • S v := by
  obtain ⟨S,hS⟩ := cayleyP_invertible hJ (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) ≤ 1)
  refine ⟨S,?_⟩
  intro v
  change (S : End n) (J v)=standardJ n ((S : End n) v)
  rw [hS]
  simp only [cayleyP_apply,one_smul,relativeOperator_apply,hJ.1,map_add,map_neg,
    standardJ_sq,neg_neg]
  abel

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_HolderCompactness
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.c1HolderGraph_isClosed _root_.OAI.HigherDimensionalBallPacking.Rigidity.c1HolderSpace_complete _root_.OAI.HigherDimensionalBallPacking.Rigidity.compactHolderSpace_complete _root_.OAI.HigherDimensionalBallPacking.Rigidity.compactHolderSubmodule_isClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {K E : Type*} [MetricSpace K] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma holder_norm_le_of_estimate (α : ℝ) (u : HolderSpace K E α) {A H : ℝ}
    (hA : 0 ≤ A) (hH : 0 ≤ H) (h0 : ∀ x, ‖holderValue α u x‖ ≤ A)
    (h1 : ∀ x y, ‖holderValue α u x-holderValue α u y‖ ≤ H*(dist x y)^α) :
    ‖u‖ ≤ max A H := by
  change max ‖u.val.1‖ ‖u.val.2‖ ≤ _
  apply max_le_max
  · exact (BoundedContinuousFunction.norm_le hA).mpr h0
  · apply (BoundedContinuousFunction.norm_le hH).mpr
    intro z
    have hh := h1 z.val.1 z.val.2
    rw [holderSpace_relation α u _ _ z.property,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg dist_nonneg _)] at hh
    exact le_of_mul_le_mul_left (hh.trans_eq (mul_comm _ _))
      (Real.rpow_pos_of_pos (dist_pos.mpr z.property) α)

 

lemma holder_third_interpolation (u : HolderSpace K E ((1:ℝ)/3)) {A L : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (h0 : ∀ x, ‖holderValue ((1:ℝ)/3) u x‖ ≤ A)
    (h1 : ∀ x y, ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖ ≤ L*dist x y) :
    ‖u‖ ≤ max A ((2*A)^((2:ℝ)/3)*L^((1:ℝ)/3)) := by
  apply holder_norm_le_of_estimate _ _ hA (by positivity) h0
  intro x y
  have hb : ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖ ≤ 2*A :=
    (norm_sub_le _ _).trans (by linarith [h0 x,h0 y])
  calc
    ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖ =
      ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖^((2:ℝ)/3)*
        ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖^((1:ℝ)/3) := by
          rw [←Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) (by norm_num)]
          norm_num
    _ ≤ (2*A)^((2:ℝ)/3)*(L*dist x y)^((1:ℝ)/3) := by
      gcongr
      exact h1 x y
    _ = ((2*A)^((2:ℝ)/3)*L^((1:ℝ)/3))*(dist x y)^((1:ℝ)/3) := by
      rw [Real.mul_rpow hL dist_nonneg,mul_assoc]

lemma holder_third_small_sup (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : HolderSpace K E ((1:ℝ)/3),
      (∀ x, ‖holderValue ((1:ℝ)/3) u x‖ ≤ δ) →
      (∀ x y, ‖holderValue ((1:ℝ)/3) u x-holderValue ((1:ℝ)/3) u y‖ ≤ L*dist x y) →
      ‖u‖ < ε := by
  let φ : ℝ → ℝ := fun t => max t ((2*t)^((2:ℝ)/3)*L^((1:ℝ)/3))
  have hc : Continuous φ := continuous_id.max
    (((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤2/3)).comp
      (continuous_const.mul continuous_id)).mul continuous_const)
  have hφ : φ 0=0 := by simp [φ,Real.zero_rpow (by norm_num : (2:ℝ)/3≠0)]
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp hc.continuousAt ε hε
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro u h0 h1
  have hh : φ (δ/2) < ε := by
    have ht := hd (show dist (δ/2) 0 < δ by simpa [Real.dist_eq,abs_of_pos (half_pos hδ),abs_of_pos hδ] using half_lt_self hδ)
    rw [hφ,dist_zero_right] at ht
    exact (le_abs_self _).trans_lt ht
  exact (holder_third_interpolation u (half_pos hδ).le hL h0 h1).trans_lt hh

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_MarkedInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem c1Holder_contDiff (α : ℝ) (u : C1HolderSpace E α) :
    ContDiff ℝ 1 (holderValue α (c1HolderValue α u)) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨holderValue α (c1HolderDeriv α u),
    (holderValue α (c1HolderDeriv α u)).continuous,c1Holder_hasFDerivAt α u⟩

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]


lemma compactCRInverse_rightInverse (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    fderiv ℝ (compactCRInverseValue R u) x Complex.I -
      Complex.I • fderiv ℝ (compactCRInverseValue R u) x 1 = compactHolderValue R u x := by
  let v := compactHolderMap R (((Complex.I/2) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) u
  have hh := cauchyTransform_holder_complexCurl (compactHolderValue R v).continuous
    (compactHolderValue_compactSupport R v) (compactHolderValue_bound R v) (norm_nonneg v)
    (compactHolderValue_holder R v) x
  have he : (compactCRInverseValue R u : ℂ → E) = cauchyTransform (compactHolderValue R v) := by
    funext z
    exact compactHolderCauchyCLM_value R v z
  rw [he]
  have hs : (2*Complex.I) • compactHolderValue R v x = -compactHolderValue R u x := by
    change (2*Complex.I) • ((Complex.I/2) • compactHolderValue R u x) = _
    rw [smul_smul,show (2*Complex.I)*(Complex.I/2)=(-1:ℂ) by ring_nf;simp,neg_one_smul]
  rw [hs] at hh
  change Complex.I • _ - _ = _ at hh
  apply neg_injective
  simpa only [neg_sub] using hh

lemma compactCRInverse_contDiff (R : ℝ) (u : CompactHolderSpace E R) :
    ContDiff ℝ 1 (compactCRInverseValue R u) := c1Holder_contDiff _ _

lemma compactCRInverse_tendsto_zero (R : ℝ) (u : CompactHolderSpace E R) :
    Tendsto (compactCRInverseValue R u) (cocompact ℂ) (𝓝 0) := by
  let v := compactHolderMap R (((Complex.I/2) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) u
  have he : (compactCRInverseValue R u : ℂ → E) = cauchyTransform (compactHolderValue R v) := by
    funext z
    exact compactHolderCauchyCLM_value R v z
  rw [he]
  exact cauchyTransform_tendsto_zero (compactHolderValue R v).continuous
    (compactHolderValue_compactSupport R v)



end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_SchauderBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped Manifold
open MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open MeasureTheory
open scoped Topology
open Finset
open scoped ContDiff Classical
open scoped BoundedContinuousFunction
open Topology
open scoped NNReal

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 theorem compactCRInverse_leftInverse (R : ℝ) (u : C1HolderSpace E ((1:ℝ)/3))
    (g : CompactHolderSpace E R)
    (hc : HasCompactSupport (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)))
    (hCR : ∀ x : ℂ,
      fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) x Complex.I -
        Complex.I • fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) x 1 =
          compactHolderValue R g x) :
    compactCRInverse R g = u := by
  let f : ℂ → E := holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)
  let v : ℂ → E := compactCRInverseValue R g
  have hf : ContDiff ℝ 1 f := c1Holder_contDiff _ _
  have hv : ContDiff ℝ 1 v := compactCRInverse_contDiff _ _
  have hd : Differentiable ℂ (fun x => f x-v x) := by
    intro x
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    refine ⟨(hf.differentiable (by simp) x).sub (hv.differentiable (by simp) x),?_⟩
    change fderiv ℝ (f-v) x Complex.I = Complex.I • fderiv ℝ (f-v) x 1
    rw [fderiv_sub (hf.differentiable (by simp) x) (hv.differentiable (by simp) x)]
    simp only [sub_apply,smul_sub]
    have hu := hCR x
    have hg := compactCRInverse_rightInverse R g x
    change fderiv ℝ f x Complex.I - Complex.I • fderiv ℝ f x 1 = _ at hu
    change fderiv ℝ v x Complex.I - Complex.I • fderiv ℝ v x 1 = _ at hg
    exact sub_eq_sub_iff_sub_eq_sub.mp (hu.trans hg.symm)
  have ht : Tendsto (fun x => f x-v x) (cocompact ℂ) (𝓝 (0:E)) := by
    have hf0 : f =ᶠ[cocompact ℂ] 0 := by
      simpa only [Filter.coclosedCompact_eq_cocompact] using hasCompactSupport_iff_eventuallyEq.mp hc
    have htf : Tendsto f (cocompact ℂ) (𝓝 (0:E)) := tendsto_const_nhds.congr' hf0.symm
    simpa only [sub_zero] using htf.sub (compactCRInverse_tendsto_zero R g)
  have he := hd.eq_const_of_tendsto_cocompact ht
  apply c1HolderValue_injective
  apply holderValue_injective
  apply BoundedContinuousFunction.ext
  intro x
  have hx := congrFun he x
  change f x-v x=0 at hx
  exact (sub_eq_zero.mp hx).symm

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst4
theorem compactCR_coercivity (R : ℝ) (u : C1HolderSpace E ((1:ℝ)/3))
    (g : CompactHolderSpace E R)
    (hc : HasCompactSupport (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)))
    (hCR : ∀ x : ℂ,
      fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) x Complex.I -
        Complex.I • fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) x 1 =
          compactHolderValue R g x) :
    ‖u‖ ≤ ‖compactCRInverse (E := E) R‖*‖g‖ := by
  rw [←compactCRInverse_leftInverse R u g hc hCR]
  exact (compactCRInverse (E := E) R).le_opNorm g

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst9
omit [CompleteSpace E] in
 theorem compactHolderApply_norm [CompleteSpace E] (R : ℝ) (A : CompactHolderSpace (E →L[ℝ] E) R)
    (v : HolderSpace ℂ E ((1:ℝ)/3)) :
    ‖compactHolderApply R A v‖ ≤ 2*‖A‖*‖v‖ :=
  holderApply_norm ((1:ℝ)/3) A.val v

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst6
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst8
theorem compactHolderApply_c1_norm (R : ℝ) (A : CompactHolderSpace (E →L[ℝ] E) R)
    (b : CompactHolderSpace E R) (u : C1HolderSpace E ((1:ℝ)/3)) :
    ‖compactHolderApply R A (c1HolderDx u)+b‖ ≤
      2*‖A‖*‖c1HolderDx (E := E)‖*‖u‖+‖b‖ := by
    calc
      ‖compactHolderApply R A (c1HolderDx u)+b‖ ≤ ‖compactHolderApply R A (c1HolderDx u)‖+‖b‖ := norm_add_le _ _
      _ ≤ 2*‖A‖*‖c1HolderDx u‖+‖b‖ :=
        add_le_add (compactHolderApply_norm R A (c1HolderDx u)) le_rfl
      _ ≤ 2*‖A‖*(‖c1HolderDx (E := E)‖*‖u‖)+‖b‖ :=
        add_le_add (mul_le_mul_of_nonneg_left ((c1HolderDx (E := E)).le_opNorm u)
          (mul_nonneg (by norm_num) (norm_nonneg A))) le_rfl
      _ = _ := by ring

private theorem absorb_half (U C A D B : ℝ) (hU : 0 ≤ U)
    (h : U ≤ C*(2*A*D*U+B)) (hsmall : 2*C*A*D ≤ 1/2) :
    U ≤ 2*C*B := by
  have hm := mul_le_mul_of_nonneg_right hsmall hU
  nlinarith only [h,hm]

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst10
theorem small_principal_coercivity (R : ℝ) (u : C1HolderSpace E ((1:ℝ)/3))
    (A : CompactHolderSpace (E →L[ℝ] E) R) (b : CompactHolderSpace E R)
    (hc : HasCompactSupport (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)))
    (hCR : ∀ z : ℂ,
      fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z Complex.I -
        Complex.I • fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z 1 =
        compactHolderValue R A z
          (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z 1) +
        compactHolderValue R b z)
    (hsmall : 2*‖compactCRInverse (E := E) R‖*‖A‖*‖c1HolderDx (E := E)‖ ≤ 1/2) :
    ‖u‖ ≤ 2*‖compactCRInverse (E := E) R‖*‖b‖ := by
  let g : CompactHolderSpace E R := compactHolderApply R A (c1HolderDx u)+b
  have hg := compactHolderApply_c1_norm R A b u
  have hgCR : ∀ z : ℂ,
      fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z Complex.I -
        Complex.I • fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z 1 =
          compactHolderValue R g z := by
    intro z
    have hgv : compactHolderValue R g z =
        compactHolderValue R A z (holderValue ((1:ℝ)/3) (c1HolderDx u) z)+
        compactHolderValue R b z := rfl
    rw [hgv,c1HolderDx_value]
    exact hCR z
  have h := (compactCR_coercivity R u g hc hgCR).trans
    (mul_le_mul_of_nonneg_left hg (norm_nonneg _))
  exact absorb_half ‖u‖ ‖compactCRInverse (E := E) R‖ ‖A‖ ‖c1HolderDx (E := E)‖
    ‖b‖ (norm_nonneg u) h hsmall

end

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst13
theorem compactSmoothHolder_interpolation {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℂ → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ z, ‖f z‖ ≤ M) (hd : ∀ z, ‖fderiv ℝ f z‖ ≤ L) :
    ‖compactSmoothHolder ((1:ℝ)/3) (by norm_num) (by norm_num) f hf hc‖ ≤
      max M ((2*M)^((2:ℝ)/3)*L^((1:ℝ)/3)) := by
  refine holder_third_interpolation
    (compactSmoothHolder ((1:ℝ)/3) (by norm_num) (by norm_num) f hf hc) hM hL ?_ ?_
  · intro z
    rw [compactSmoothHolder_apply]
    exact hb z
  have hLip : LipschitzWith ⟨L,hL⟩ f :=
    lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp)) (fun z => by
      exact_mod_cast hd z)
  intro x y
  simp only [compactSmoothHolder_apply]
  have hh := hLip.dist_le_mul x y
  rw [dist_eq_norm,dist_eq_norm] at hh
  rw [dist_eq_norm]
  exact hh

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst11
theorem c1Holder_fderiv_holder (u : C1HolderSpace E ((1:ℝ)/3)) (x y : ℂ) :
    ‖fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) x -
      fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) y‖ ≤
      ‖u‖*‖x-y‖^((1:ℝ)/3) := by
  rw [c1Holder_fderiv,c1Holder_fderiv]
  have he := holderSpace_estimate ((1:ℝ)/3) (by norm_num) (c1HolderDeriv ((1:ℝ)/3) u) x y
  have hn : ‖c1HolderDeriv ((1:ℝ)/3) u‖ ≤ ‖u‖ := le_max_right _ _
  rw [dist_eq_norm] at he
  exact he.trans (mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg (norm_nonneg _) _))

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst12
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst14
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst15
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst16
theorem small_principal_smooth_estimate (R : ℝ)
    (f : ℂ → E) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (A : ℂ → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A)
    (b : ℂ → E) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hAs : tsupport A ⊆ Metric.closedBall (0:ℂ) R)
    (hbs : tsupport b ⊆ Metric.closedBall (0:ℂ) R)
    (hCR : ∀ z, fderiv ℝ f z Complex.I - Complex.I • fderiv ℝ f z 1 =
      A z (fderiv ℝ f z 1)+b z)
    (M L B K : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hAv : ∀ z, ‖A z‖ ≤ M) (hAD : ∀ z, ‖fderiv ℝ A z‖ ≤ L)
    (hbv : ∀ z, ‖b z‖ ≤ B) (hbD : ∀ z, ‖fderiv ℝ b z‖ ≤ K)
    (hsmall : 2*‖compactCRInverse (E := E) R‖*(max M ((2*M)^((2:ℝ)/3)*L^((1:ℝ)/3)))*‖c1HolderDx (E := E)‖ ≤ 1/2) :
    ∀ x y, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤
      (2*‖compactCRInverse (E := E) R‖*(max B ((2*B)^((2:ℝ)/3)*K^((1:ℝ)/3))))*‖x-y‖^((1:ℝ)/3) := by
  let u := compactSmoothC1Holder ((1:ℝ)/3) (by norm_num) (by norm_num) f hf hfc
  let AA : CompactHolderSpace (E →L[ℝ] E) R :=
    ⟨compactSmoothHolder ((1:ℝ)/3) (by norm_num) (by norm_num) A hA hAc,by
      intro z hz
      apply image_eq_zero_of_notMem_tsupport
      intro h
      have := hAs h
      simp only [Metric.mem_closedBall,dist_zero_right] at this
      exact (not_le_of_gt hz) this⟩
  let bb : CompactHolderSpace E R :=
    ⟨compactSmoothHolder ((1:ℝ)/3) (by norm_num) (by norm_num) b hb hbc,by
      intro z hz
      apply image_eq_zero_of_notMem_tsupport
      intro h
      have := hbs h
      simp only [Metric.mem_closedBall,dist_zero_right] at this
      exact (not_le_of_gt hz) this⟩
  have hAAn : ‖AA‖ ≤ max M ((2*M)^((2:ℝ)/3)*L^((1:ℝ)/3)) := compactSmoothHolder_interpolation A hA hAc M L hM hL hAv hAD
  have hbbn : ‖bb‖ ≤ max B ((2*B)^((2:ℝ)/3)*K^((1:ℝ)/3)) := compactSmoothHolder_interpolation b hb hbc B K hB hK hbv hbD
  have hsm : 2*‖compactCRInverse (E := E) R‖*‖AA‖*‖c1HolderDx (E := E)‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hAAn (mul_nonneg (by norm_num) (norm_nonneg _))) (norm_nonneg _)).trans hsmall
  have hu := small_principal_coercivity R u AA bb hfc hCR hsm
  intro x y
  exact (c1Holder_fderiv_holder u x y).trans
    (mul_le_mul_of_nonneg_right (hu.trans
      (mul_le_mul_of_nonneg_left hbbn (mul_nonneg (by norm_num) (norm_nonneg _))))
      (Real.rpow_nonneg (norm_nonneg _) _))

end

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_fderiv_smul_bound {χ : E → ℝ} {f : E → F} {z : E}
    (hχ : DifferentiableAt ℝ χ z) (hf : DifferentiableAt ℝ f z) :
    ‖fderiv ℝ (fun x => χ x • f x) z‖ ≤
      |χ z| *‖fderiv ℝ f z‖+‖fderiv ℝ χ z‖*‖f z‖ := by
  change ‖fderiv ℝ (χ • f) z‖ ≤ _
  rw [fderiv_smul hχ hf]
  exact (norm_add_le _ _).trans_eq (by
    rw [norm_smul,Real.norm_eq_abs,ContinuousLinearMap.norm_smulRight_apply])

theorem norm_fderiv_apply_bound {A : E → F →L[ℝ] G} {f : E → F} {z : E}
    (hA : DifferentiableAt ℝ A z) (hf : DifferentiableAt ℝ f z) :
    ‖fderiv ℝ (fun x => A x (f x)) z‖ ≤
      ‖A z‖*‖fderiv ℝ f z‖+‖fderiv ℝ A z‖*‖f z‖ := by
  rw [fderiv_clm_apply hA hf]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (A z).opNorm_comp_le _
  · exact ((fderiv ℝ A z).flip.le_opNorm (f z)).trans_eq (by rw [ContinuousLinearMap.opNorm_flip])

theorem cutoff_smul_bounds {χ : E → ℝ} {f : E → F}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    {S : Set E} (hS : tsupport χ ⊆ S)
    {C D M L : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hχv : ∀ z, |χ z| ≤ C) (hχD : ∀ z, ‖fderiv ℝ χ z‖ ≤ D)
    (hfv : ∀ z ∈ S, ‖f z‖ ≤ M) (hfD : ∀ z ∈ S, ‖fderiv ℝ f z‖ ≤ L) :
    (∀ z, ‖χ z • f z‖ ≤ C*M) ∧
      ∀ z, ‖fderiv ℝ (fun x => χ x • f x) z‖ ≤ C*L+D*M := by
  constructor
  · intro z
    by_cases hz : z ∈ tsupport χ
    · rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hχv z) (hfv z (hS hz)) (norm_nonneg _) hC
    · rw [image_eq_zero_of_notMem_tsupport hz,zero_smul,norm_zero]
      exact mul_nonneg hC hM
  · intro z
    by_cases hz : z ∈ tsupport χ
    · apply (norm_fderiv_smul_bound (hχ.differentiable (by simp) z)
        (hf.differentiable (by simp) z)).trans
      exact add_le_add
        (mul_le_mul (hχv z) (hfD z (hS hz)) (norm_nonneg _) hC)
        (mul_le_mul (hχD z) (hfv z (hS hz)) (norm_nonneg _) hD)
    · have hz' : z ∉ tsupport (fun x => χ x • f x) :=
        fun hh => hz (tsupport_smul_subset_left χ f hh)
      rw [fderiv_of_notMem_tsupport ℝ hz',norm_zero]
      exact add_nonneg (mul_nonneg hC hL) (mul_nonneg hD hM)

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cutoffCR_equation (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (A : ℂ → E →L[ℝ] E) (u : ℂ → E) (hu : ContDiff ℝ ∞ u)
    (hCR : ∀ z ∈ tsupport χ, fderiv ℝ u z Complex.I - Complex.I • fderiv ℝ u z 1 =
      A z (fderiv ℝ u z 1)) (z : ℂ) :
    fderiv ℝ (fun w => χ w • u w) z Complex.I -
      Complex.I • fderiv ℝ (fun w => χ w • u w) z 1 =
      A z (fderiv ℝ (fun w => χ w • u w) z 1)+cutoffCRRemainder χ A u z := by
  change fderiv ℝ (χ • u) z Complex.I - Complex.I • fderiv ℝ (χ • u) z 1 =
    A z (fderiv ℝ (χ • u) z 1)+cutoffCRRemainder χ A u z
  rw [fderiv_smul (hχ.differentiable (by simp) z) (hu.differentiable (by simp) z)]
  by_cases hz : z ∈ tsupport χ
  · simp only [add_apply,smul_apply,
      ContinuousLinearMap.smulRight_apply,map_add,map_smul,smul_add,cutoffCRRemainder]
    rw [sub_eq_iff_eq_add.mp (hCR z hz),smul_add,smul_comm (χ z) Complex.I]
    abel
  · rw [image_eq_zero_of_notMem_tsupport hz]
    simp only [ContinuousLinearMap.smulRight_apply,zero_smul,zero_add,cutoffCRRemainder,
      fderiv_of_notMem_tsupport ℝ hz,zero_apply,map_zero,smul_zero,sub_zero,add_zero]

theorem scalarDirection_smooth (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (w : ℂ) :
    ContDiff ℝ ∞ (scalarDirection χ w) :=
  (hχ.fderiv_right (by simp)).clm_apply contDiff_const

theorem scalarDirection_support (χ : ℂ → ℝ) (w : ℂ) :
    tsupport (scalarDirection χ w) ⊆ tsupport χ := by
  apply closure_minimal (support_subset_iff'.mpr ?_) (isClosed_tsupport χ)
  intro z hz
  simp only [scalarDirection,fderiv_of_notMem_tsupport ℝ hz,zero_apply]

theorem scalarDirection_norm (χ : ℂ → ℝ) (w z : ℂ) :
    |scalarDirection χ w z| ≤ ‖fderiv ℝ χ z‖*‖w‖ :=
  (fderiv ℝ χ z).le_opNorm w

theorem scalarDirection_fderiv_norm (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (w z : ℂ) :
    ‖fderiv ℝ (scalarDirection χ w) z‖ ≤ ‖fderiv ℝ (fderiv ℝ χ) z‖*‖w‖ := by
  change ‖fderiv ℝ (fun y => fderiv ℝ χ y w) z‖ ≤ _
  have hd : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right (by simp)
  have hh := norm_fderiv_apply_bound (A := fderiv ℝ χ) (f := fun _ : ℂ => w)
    (hd.differentiable (by simp) z) (differentiableAt_const (c := w))
  simpa only [fderiv_const_apply,norm_zero,mul_zero,zero_add] using hh

theorem cutoffCRRemainder_smooth (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (A : ℂ → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A)
    (u : ℂ → E) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (cutoffCRRemainder χ A u) :=
  (((scalarDirection_smooth χ hχ Complex.I).smul hu).sub
    (((scalarDirection_smooth χ hχ 1).smul hu).const_smul Complex.I)).sub
      (hA.clm_apply ((scalarDirection_smooth χ hχ 1).smul hu))

theorem cutoffCRRemainder_support (χ : ℂ → ℝ) (A : ℂ → E →L[ℝ] E) (u : ℂ → E) :
    tsupport (cutoffCRRemainder χ A u) ⊆ tsupport χ := by
  apply closure_minimal (support_subset_iff'.mpr ?_) (isClosed_tsupport χ)
  intro z hz
  simp only [cutoffCRRemainder,fderiv_of_notMem_tsupport ℝ hz,
    zero_apply,zero_smul,smul_zero,map_zero,sub_zero]

theorem cutoff_direction_product_bounds (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (u : ℂ → E) (hu : ContDiff ℝ ∞ u)
    {D L : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hχD : ∀ z, ‖fderiv ℝ χ z‖ ≤ D)
    (hχDD : ∀ z, ‖fderiv ℝ (fderiv ℝ χ) z‖ ≤ D)
    (huv : ∀ z ∈ tsupport χ, ‖u z‖ ≤ 1)
    (huD : ∀ z ∈ tsupport χ, ‖fderiv ℝ u z‖ ≤ L)
    (w : ℂ) (hw : ‖w‖=1) :
    (∀ z, ‖scalarDirection χ w z • u z‖ ≤ D) ∧
      ∀ z, ‖fderiv ℝ (fun x => scalarDirection χ w x • u x) z‖ ≤ D*(L+1) := by
  have h1 : ∀ z, |scalarDirection χ w z| ≤ D := fun z => by
    simpa only [hw,mul_one] using (scalarDirection_norm χ w z).trans
      (mul_le_mul_of_nonneg_right (hχD z) (norm_nonneg w))
  have h2 : ∀ z, ‖fderiv ℝ (scalarDirection χ w) z‖ ≤ D := fun z => by
    simpa only [hw,mul_one] using (scalarDirection_fderiv_norm χ hχ w z).trans
      (mul_le_mul_of_nonneg_right (hχDD z) (norm_nonneg w))
  have hh := cutoff_smul_bounds (scalarDirection_smooth χ hχ w) hu
    (scalarDirection_support χ w) hD hD (show (0:ℝ) ≤ 1 by norm_num) hL h1 h2 huv huD
  simpa only [mul_one,mul_add] using hh

theorem cutoffCRRemainder_bounds (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (A : ℂ → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A)
    (u : ℂ → E) (hu : ContDiff ℝ ∞ u)
    {D L K : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hχD : ∀ z, ‖fderiv ℝ χ z‖ ≤ D)
    (hχDD : ∀ z, ‖fderiv ℝ (fderiv ℝ χ) z‖ ≤ D)
    (huv : ∀ z ∈ tsupport χ, ‖u z‖ ≤ 1)
    (huD : ∀ z ∈ tsupport χ, ‖fderiv ℝ u z‖ ≤ L)
    (hAv : ∀ z, ‖A z‖ ≤ 1) (hAD : ∀ z, ‖fderiv ℝ A z‖ ≤ K) :
    (∀ z, ‖cutoffCRRemainder χ A u z‖ ≤ 3*D) ∧
      ∀ z, ‖fderiv ℝ (cutoffCRRemainder χ A u) z‖ ≤ 3*D*(L+1)+K*D := by
  let qI : ℂ → E := fun z => scalarDirection χ Complex.I z • u z
  let q1 : ℂ → E := fun z => scalarDirection χ 1 z • u z
  have hqIs : ContDiff ℝ ∞ qI := (scalarDirection_smooth χ hχ Complex.I).smul hu
  have hq1s : ContDiff ℝ ∞ q1 := (scalarDirection_smooth χ hχ 1).smul hu
  have hqI := cutoff_direction_product_bounds χ hχ u hu hD hL hχD hχDD huv huD
    Complex.I Complex.norm_I
  have hq1 := cutoff_direction_product_bounds χ hχ u hu hD hL hχD hχDD huv huD
    1 (norm_one : ‖(1:ℂ)‖=1)
  change (∀ z, ‖qI z‖ ≤ D) ∧ ∀ z, ‖fderiv ℝ qI z‖ ≤ D*(L+1) at hqI
  change (∀ z, ‖q1 z‖ ≤ D) ∧ ∀ z, ‖fderiv ℝ q1 z‖ ≤ D*(L+1) at hq1
  have hg : cutoffCRRemainder χ A u = qI - Complex.I • q1 - fun z => A z (q1 z) := rfl
  have ha (z : ℂ) : ‖A z (q1 z)‖ ≤ D := by
    exact ((A z).le_opNorm _).trans ((mul_le_mul (hAv z) (hq1.1 z)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul D))
  have haD (z : ℂ) : ‖fderiv ℝ (fun x => A x (q1 x)) z‖ ≤ D*(L+1)+K*D := by
    apply (norm_fderiv_apply_bound (hA.differentiable (by simp) z)
      (hq1s.differentiable (by simp) z)).trans
    have h1 := mul_le_mul (hAv z) (hq1.2 z) (norm_nonneg _) (show (0:ℝ) ≤ 1 by norm_num)
    have h2 := mul_le_mul (hAD z) (hq1.1 z) (norm_nonneg _) hK
    simpa only [one_mul] using add_le_add h1 h2
  constructor
  · intro z
    rw [hg]
    change ‖qI z-Complex.I • q1 z-A z (q1 z)‖ ≤ _
    have hh := (norm_sub_le (qI z-Complex.I • q1 z) (A z (q1 z))).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
    rw [norm_smul Complex.I (q1 z),Complex.norm_I,one_mul] at hh
    linarith [hqI.1 z,hq1.1 z,ha z]
  · intro z
    rw [hg,fderiv_sub (f := qI - Complex.I • q1) (g := fun z => A z (q1 z)) ((hqIs.sub (hq1s.const_smul Complex.I)).differentiable (by simp) z)
      ((hA.clm_apply hq1s).differentiable (by simp) z),
      fderiv_sub (f := qI) (g := Complex.I • q1) (hqIs.differentiable (by simp) z)
        ((hq1s.const_smul Complex.I).differentiable (by simp) z),
      fderiv_const_smul (hq1s.differentiable (by simp) z) Complex.I]
    have hh := (norm_sub_le (fderiv ℝ qI z-Complex.I • fderiv ℝ q1 z)
      (fderiv ℝ (fun x => A x (q1 x)) z)).trans (add_le_add (norm_sub_le _ _) le_rfl)
    rw [norm_smul Complex.I (fderiv ℝ q1 z),Complex.norm_I,one_mul] at hh
    nlinarith only [hh,hqI.2 z,hq1.2 z,haD z]

end

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst17
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst18
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst19
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.schauderBoundsInst20
theorem cutoff_smallCR_schauder (R : ℝ)
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Metric.closedBall (0:ℂ) R)
    (A : ℂ → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A)
    (hAs : tsupport A ⊆ Metric.closedBall (0:ℂ) R)
    (u : ℂ → E) (hu : ContDiff ℝ ∞ u)
    {D L K M : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (hχD : ∀ z, ‖fderiv ℝ χ z‖ ≤ D)
    (hχDD : ∀ z, ‖fderiv ℝ (fderiv ℝ χ) z‖ ≤ D)
    (huv : ∀ z ∈ tsupport χ, ‖u z‖ ≤ 1)
    (huD : ∀ z ∈ tsupport χ, ‖fderiv ℝ u z‖ ≤ L)
    (hAv : ∀ z, ‖A z‖ ≤ M) (hAD : ∀ z, ‖fderiv ℝ A z‖ ≤ K)
    (hCR : ∀ z ∈ tsupport χ, fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1 =
      A z (fderiv ℝ u z 1))
    (hsmall : 2*‖compactCRInverse (E := E) R‖*
      max M ((2*M)^((2:ℝ)/3)*K^((1:ℝ)/3))*‖c1HolderDx (E := E)‖ ≤ 1/2) :
    ∀ x y, ‖fderiv ℝ (fun z => χ z • u z) x-fderiv ℝ (fun z => χ z • u z) y‖ ≤
      localSchauderBound E R D L K*‖x-y‖^((1:ℝ)/3) := by
  let b := cutoffCRRemainder χ A u
  have hbs : tsupport b ⊆ tsupport χ := cutoffCRRemainder_support χ A u
  have hbc : HasCompactSupport b := hχc.of_isClosed_subset (isClosed_tsupport b) hbs
  have hbb := cutoffCRRemainder_bounds χ hχ A hA u hu hD hL hK hχD hχDD huv huD
    (fun z => (hAv z).trans hM1) hAD
  exact small_principal_smooth_estimate R (fun z => χ z • u z) (hχ.smul hu)
    hχc.smul_right A hA hAc b (cutoffCRRemainder_smooth χ hχ A hA u hu) hbc hAs
    (hbs.trans hχs) (cutoffCR_equation χ hχ A u hu hCR)
    M K (3*D) (3*D*(L+1)+K*D) hM hK (by positivity) (by positivity)
    hAv hAD hbb.1 hbb.2 hsmall

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_GradientLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity

theorem exists_nested_complex_cutoffs :
    ∃ (χ θ : ℂ → ℝ) (D : ℝ), 0 ≤ D ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      tsupport χ ⊆ Metric.closedBall (0:ℂ) 2 ∧
      tsupport θ ⊆ Metric.closedBall (0:ℂ) 3 ∧
      χ =ᶠ[𝓝 0] (fun _ => (1:ℝ)) ∧
      (∀ z ∈ tsupport χ, θ z=1) ∧
      (∀ z, |χ z| ≤ 1 ∧ |θ z| ≤ 1) ∧
      (∀ z, ‖fderiv ℝ χ z‖ ≤ D ∧ ‖fderiv ℝ (fderiv ℝ χ) z‖ ≤ D ∧
        ‖fderiv ℝ θ z‖ ≤ D) := by
  let χ : ContDiffBump (0:ℂ) := ⟨1,2,by norm_num,by norm_num⟩
  let θ : ContDiffBump (0:ℂ) := ⟨2,3,by norm_num,by norm_num⟩
  have hχ : ContDiff ℝ ∞ (χ : ℂ → ℝ) := χ.contDiff
  have hθ : ContDiff ℝ ∞ (θ : ℂ → ℝ) := θ.contDiff
  have hχD : ContDiff ℝ ∞ (fderiv ℝ (χ : ℂ → ℝ)) := hχ.fderiv_right (by simp)
  obtain ⟨D₁,hD₁,hB₁⟩ := ((χ.hasCompactSupport.fderiv ℝ).isCompact_range
    (hχ.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  have hbD2 : Bornology.IsBounded (range (fderiv ℝ (fderiv ℝ (χ : ℂ → ℝ)))) :=
    (((χ.hasCompactSupport.fderiv ℝ).fderiv ℝ).isCompact_range
      (hχD.continuous_fderiv (by simp))).isBounded
  obtain ⟨D₂,hD₂,hB₂⟩ := hbD2.exists_pos_norm_le
  obtain ⟨D₃,hD₃,hB₃⟩ := ((θ.hasCompactSupport.fderiv ℝ).isCompact_range
    (hθ.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  refine ⟨χ,θ,D₁+D₂+D₃,by positivity,hχ,χ.hasCompactSupport,hθ,θ.hasCompactSupport,?_,?_,?_,?_,?_,?_⟩
  · rw [χ.tsupport_eq]
  · rw [θ.tsupport_eq]
  · exact χ.eventuallyEq_one
  · intro z hz
    rw [χ.tsupport_eq] at hz
    exact θ.one_of_mem_closedBall hz
  · intro z
    constructor
    · rw [abs_of_nonneg χ.nonneg]
      exact χ.le_one
    · rw [abs_of_nonneg θ.nonneg]
      exact θ.le_one
  · intro z
    have h1 := hB₁ _ (mem_range_self z)
    have h2 := hB₂ _ (mem_range_self z)
    have h3 := hB₃ _ (mem_range_self z)
    exact ⟨by linarith,by linarith,by linarith⟩


 

 

 

open scoped Topology ContDiff
open Set Filter Function
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem derivative_bound_of_holder_and_values (f : E → F)
    (hf : Differentiable ℝ f) {M C r α : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hr : 0 < r) (hα : 0 ≤ α)
    (hv : ∀ z ∈ Metric.closedBall (0:E) r, ‖f z‖ ≤ M)
    (hD : ∀ z ∈ Metric.closedBall (0:E) r,
      ‖fderiv ℝ f z-fderiv ℝ f 0‖ ≤ C*‖z‖^α) :
    ‖fderiv ℝ f 0‖ ≤ 2*M/r+C*r^α := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hvn
  have hrv : r • v ∈ Metric.closedBall (0:E) r := by
    simp [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr,hvn]
  have h0 : (0:E) ∈ Metric.closedBall (0:E) r := Metric.mem_closedBall_self hr.le
  have herr := (convex_closedBall (0:E) r).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ => hf z) (φ := fderiv ℝ f 0) (C := C*r^α)
    (fun z hz => (hD z hz).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (by simpa using hz) hα) hC)) h0 hrv
  simp only [sub_zero,norm_smul,Real.norm_eq_abs,abs_of_pos hr,hvn,mul_one] at herr
  have hval : ‖f (r • v)-f 0‖ ≤ 2*M :=
    (norm_sub_le _ _).trans (by linarith [hv (r • v) hrv,hv 0 h0])
  have hsum := norm_sub_le (f (r • v)-f 0)
    (f (r • v)-f 0-(fderiv ℝ f 0) (r • v))
  rw [sub_sub_cancel] at hsum
  rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hsum
  rw [map_smul] at herr
  have hbound : r*‖(fderiv ℝ f 0) v‖ ≤ 2*M+(C*r^α)*r := by linarith
  have hh : ‖(fderiv ℝ f 0) v‖ ≤ (2*M+(C*r^α)*r)/r :=
    (le_div_iff₀ hr).mpr (by nlinarith)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

theorem norm_fderiv_tendsto_zero_of_holder {f : ℕ → E → F}
    (hf : ∀ j, Differentiable ℝ (f j)) {C α : ℝ} (hC : 0 ≤ C) (hα : 0 < α)
    (hD : ∀ᶠ j in atTop, ∀ x y, ‖fderiv ℝ (f j) x-fderiv ℝ (f j) y‖ ≤ C*‖x-y‖^α)
    (hv : TendstoUniformlyOn f (fun _ => (0:F)) atTop (Metric.closedBall (0:E) 1)) :
    Tendsto (fun j => ‖fderiv ℝ (f j) 0‖) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun j => ha.trans_le (norm_nonneg _))
  intro ε hε
  have hpow : Tendsto (fun r : ℝ => C*r^α) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.zero_rpow (ne_of_gt hα)] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => C) (𝓝[>] 0) (𝓝 C)).mul
        ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.mono_left nhdsWithin_le_nhds))
  have hs := hpow.eventually (gt_mem_nhds (show 0 < ε/2 by linarith))
  have hs' : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 :=
    (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r,hr,hr1,hsmall⟩ := (hpos.and (hs'.and hs)).exists
  have hδ : 0 < ε*r/8 := by positivity
  have hev := (Metric.tendstoUniformlyOn_iff.mp hv) (ε*r/8) hδ
  filter_upwards [hev,hD] with j hj hjD
  have hb := derivative_bound_of_holder_and_values (f j) (hf j) (M := ε*r/8)
    (C := C) hδ.le hC hr hα.le
    (fun z hz => le_of_lt (by
      have hh := hj z (Metric.closedBall_subset_closedBall hr1.le hz)
      simpa [dist_eq_norm] using hh))
    (fun z _ => by simpa using hjD z 0)
  have hid : 2*(ε*r/8)/r=ε/4 := by field_simp; ring
  rw [hid] at hb
  linarith

end

 

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private theorem exists_small_principal_const (B K : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      B*max δ ((2*δ)^((2:ℝ)/3)*K^((1:ℝ)/3)) ≤ 1/2 := by
  let g : ℝ → ℝ := fun r => B*max r ((2*r)^((2:ℝ)/3)*K^((1:ℝ)/3))
  have hg : Continuous g := by
    exact continuous_const.mul (continuous_id.max
      (((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 2/3)).comp
        (continuous_const.mul continuous_id)).mul continuous_const))
  have hg0 : g 0=0 := by simp [g,Real.zero_rpow (show (2:ℝ)/3 ≠ 0 by norm_num)]
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, g r < 1/2 := by
    have ht : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
      hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact ht.eventually (gt_mem_nhds (show g 0 < (1:ℝ)/2 by rw [hg0]; norm_num))
  have hr1 : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 :=
    (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hr0 : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r,h0,h1,hg⟩ := (hr0.and (hr1.and hev)).exists
  exact ⟨r,h0,h1.le,hg.le⟩

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.gradientLimitsC1NormedAddCommGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.gradientLimitsC1NormedSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.gradientLimitsCompactNormedAddCommGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.gradientLimitsCompactNormedSpace
theorem smallCR_sequence_derivative_zero
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (A : ℕ → ℂ → E →L[ℝ] E) (hA : ∀ j, ContDiff ℝ ∞ (A j))
    {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    (huD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (u j) z‖ ≤ L)
    (hAD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (A j) z‖ ≤ K)
    (hCR : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      fderiv ℝ (u j) z Complex.I-Complex.I • fderiv ℝ (u j) z 1=
        A j z (fderiv ℝ (u j) z 1))
    (hu0 : TendstoUniformlyOn u (fun _ => (0:E)) atTop (Metric.closedBall (0:ℂ) 3))
    (hA0 : TendstoUniformlyOn A (fun _ => (0:E →L[ℝ] E)) atTop (Metric.closedBall (0:ℂ) 3)) :
    Tendsto (fun j => ‖fderiv ℝ (u j) 0‖) atTop (𝓝 0) := by
  obtain ⟨χ,θ,D,hD,hχ,hχc,hθ,hθc,hχ2,hθ3,hχ1,hθ1,hχθ,hd⟩ := exists_nested_complex_cutoffs
  have hχ3 : tsupport χ ⊆ Metric.closedBall (0:ℂ) 3 :=
    hχ2.trans (Metric.closedBall_subset_closedBall (by norm_num))
  let B := 2*‖compactCRInverse (E := E) 3‖*‖c1HolderDx (E := E)‖
  obtain ⟨δ,hδ,hδ1,hsmall⟩ := exists_small_principal_const B (K+D)
  have hu1 : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖u j z‖ ≤ 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu0 1 (by norm_num)] with j hj
    intro z hz
    exact le_of_lt (by simpa [dist_eq_norm] using hj z hz)
  have hAδ : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖A j z‖ ≤ δ := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hA0 δ hδ] with j hj
    intro z hz
    exact le_of_lt (by simpa [dist_eq_norm] using hj z hz)
  let v : ℕ → ℂ → E := fun j z => χ z • u j z
  have hv : ∀ j, ContDiff ℝ ∞ (v j) := fun j => hχ.smul (hu j)
  have hv0 : TendstoUniformlyOn v (fun _ => (0:E)) atTop (Metric.closedBall (0:ℂ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu0 ε hε] with j hj
    intro z hz
    simp only [dist_zero_left,v,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hχθ z).1 (norm_nonneg _)).trans_lt (by
      simpa only [one_mul,dist_zero_left] using hj z
        (Metric.closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 3) hz))
  have hvD : ∀ᶠ j in atTop, ∀ x y,
      ‖fderiv ℝ (v j) x-fderiv ℝ (v j) y‖ ≤
        localSchauderBound E 3 D L (K+D)*‖x-y‖^((1:ℝ)/3) := by
    filter_upwards [huD,hAD,hCR,hu1,hAδ] with j hjD hjAD hjCR hj1 hjAδ
    let AA : ℂ → E →L[ℝ] E := fun z => θ z • A j z
    have hAA : ContDiff ℝ ∞ AA := hθ.smul (hA j)
    have hAAc : HasCompactSupport AA := hθc.smul_right
    have hAAs : tsupport AA ⊆ Metric.closedBall (0:ℂ) 3 :=
      (tsupport_smul_subset_left θ (A j)).trans hθ3
    have hb := cutoff_smul_bounds hθ (hA j) hθ3 (C := 1) (D := D) (M := δ) (L := K)
      (by norm_num) hD hδ.le hK (fun z => (hχθ z).2) (fun z => (hd z).2.2) hjAδ hjAD
    have hAAv : ∀ z, ‖AA z‖ ≤ δ := by simpa only [one_mul] using hb.1
    have hAAD : ∀ z, ‖fderiv ℝ AA z‖ ≤ K+D := by
      intro z
      exact (hb.2 z).trans (by nlinarith)
    apply cutoff_smallCR_schauder 3 χ hχ hχc hχ3 AA hAA hAAc hAAs (u j) (hu j)
      hD hL (add_nonneg hK hD) hδ.le hδ1 (fun z => (hd z).1)
      (fun z => (hd z).2.1) (fun z hz => hj1 z (hχ3 hz)) (fun z hz => hjD z (hχ3 hz))
      hAAv hAAD
    · intro z hz
      rw [show AA z=A j z by simp only [AA,hθ1 z hz,one_smul]]
      exact hjCR z (hχ3 hz)
    · dsimp [B] at hsmall
      nlinarith only [hsmall]
  have hC : 0 ≤ localSchauderBound E 3 D L (K+D) := by
    dsimp [localSchauderBound]
    positivity
  have hlim := norm_fderiv_tendsto_zero_of_holder (fun j => (hv j).differentiable (by simp))
    hC (by norm_num : (0:ℝ) < 1/3) hvD hv0
  convert hlim using 1
  all_goals try with_reducible_and_instances rfl
  funext j
  congr 1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hχ1] with z hz
  simp only [v,hz,one_smul]

end

 

 

 

open scoped Topology
open Set Filter Function
section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem locally_uniform_comp_uniform_constant
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℕ → E → F} {v : E → F}
    (hv : TendstoLocallyUniformly f v atTop) {x : E} (hvc : ContinuousAt v x)
    {g : ℕ → G → E} {K : Set G}
    (hg : TendstoUniformlyOn g (fun _ => x) atTop K) :
    TendstoUniformlyOn (fun j z => f j (g j z)) (fun _ => v x) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he := show {p : F × F | dist p.1 p.2 < ε/2} ∈ uniformity F from
    Metric.dist_mem_uniformity (by linarith)
  obtain ⟨U,hU,hUf⟩ := hv _ he x
  obtain ⟨V,hV,hVc⟩ := Metric.continuousAt_iff.mp hvc (ε/2) (by linarith)
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp hU
  have hmin : 0 < min δ V := lt_min hδ hV
  filter_upwards [hUf,Metric.tendstoUniformlyOn_iff.mp hg (min δ V) hmin] with j hj hjg
  intro z hz
  have hgdist : dist (g j z) x < min δ V := by simpa [dist_comm] using hjg z hz
  have hmem : g j z ∈ U := hδU (hgdist.trans_le (min_le_left _ _))
  have h1 := hj (g j z) hmem
  have h2 := hVc (lt_of_lt_of_le hgdist (min_le_right _ _))
  have ht := dist_triangle (v x) (v (g j z)) (f j (g j z))
  rw [dist_comm (v x) (v (g j z))] at ht
  linarith

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem continuousAt_comp_uniform_constant
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : E → F} {x : E}
    (hg : ContinuousAt g x) {u : ℕ → G → E} {K : Set G}
    (hu : TendstoUniformlyOn u (fun _ => x) atTop K) :
    TendstoUniformlyOn (fun j z => g (u j z)) (fun _ => g x) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ,hδ,hb⟩ := Metric.continuousAt_iff.mp hg ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu δ hδ] with j hj
  intro z hz
  rw [dist_comm]
  exact hb (by simpa [dist_comm] using hj z hz)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem uniform_constant_prod
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {x : ℕ → E} {p : E} (hx : Tendsto x atTop (𝓝 p))
    {u : ℕ → G → F} {q : F} {K : Set G}
    (hu : TendstoUniformlyOn u (fun _ => q) atTop K) :
    TendstoUniformlyOn (fun j z => (x j,u j z)) (fun _ => (p,q)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hx ε hε,Metric.tendstoUniformlyOn_iff.mp hu ε hε] with j hj hju
  intro z hz
  rw [Prod.dist_eq]
  exact max_lt (by simpa [dist_comm] using hj) (hju z hz)

theorem affine_rescale_uniform_constant {x : ℕ → E} {c : E}
    (hx : Tendsto x atTop (𝓝 c)) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    {K : Set E} (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun j z => x j+r j • z) (fun _ => c) atTop K := by
  obtain ⟨M,hM,hMb⟩ := hK.exists_pos_norm_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall : ∀ᶠ j in atTop, dist (x j) c+|r j| * M < ε := by
    have ht : Tendsto (fun j => dist (x j) c+|r j| * M) atTop (𝓝 0) := by
      simpa using (hx.dist (tendsto_const_nhds (x := c))).add (hr.abs.mul_const M)
    exact ht.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall] with j hj
  intro z hz
  rw [dist_comm,dist_eq_norm]
  have he : x j+r j • z-c=(x j-c)+r j • z := by abel
  rw [he]
  apply (norm_add_le _ _).trans_lt
  rw [norm_smul,Real.norm_eq_abs]
  apply lt_of_le_of_lt _ hj
  rw [dist_eq_norm]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hMb z hz) (abs_nonneg _))

theorem rescaled_maps_uniform_constant {f : ℕ → E → F} {v : E → F}
    (hv : TendstoLocallyUniformly f v atTop) {x : ℕ → E} {c : E}
    (hvc : ContinuousAt v c) (hx : Tendsto x atTop (𝓝 c))
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) {K : Set E} (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun j z => f j (x j+r j • z)) (fun _ => v c) atTop K :=
  locally_uniform_comp_uniform_constant hv hvc (affine_rescale_uniform_constant hx hr hK)

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function
section
open HigherDimensionalBallPacking.Rigidity

theorem lineHomotopy_contDiffAt {n : ℕ} {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    {y : ℝ × Phase n} (hy : y.1 ∈ Icc (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (fun y : ℝ × Phase n => lineHomotopy J y.1 y.2) y :=
  contDiffAt_interpolateJ (hJs.contDiffAt.comp y contDiffAt_snd)
    contDiffAt_fst (hJ y.2) hy

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function
section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem rescaleMap_smooth {u : ℂ → F} (hu : ContDiff ℝ ∞ u) (x : ℂ) (r : ℝ) :
    ContDiff ℝ ∞ (rescaleMap u x r) := by
  exact ContDiff.comp (g := u) (f := fun z : ℂ => x+r • z) hu
    (contDiff_const.add (contDiff_id.const_smul r))

theorem rescaleMap_fderiv {u : ℂ → F} (hu : Differentiable ℝ u) (x : ℂ) (r : ℝ) (z : ℂ) :
    fderiv ℝ (rescaleMap u x r) z=r • fderiv ℝ u (x+r • z) := by
  have hd : HasFDerivAt (fun z : ℂ => x+r • z) (r • ContinuousLinearMap.id ℝ ℂ) z :=
    by
      have hh := (hasFDerivAt_const (𝕜 := ℝ) x z).add ((hasFDerivAt_id (𝕜 := ℝ) z).const_smul r)
      simp only [zero_add] at hh
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      rfl
  have he := (HasFDerivAt.comp (g := u) (f := fun z : ℂ => x+r • z) z
    (hu (x+r • z)).hasFDerivAt hd).fderiv
  simp only [Function.comp_def,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_id] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  rfl

theorem rescaleMap_norm_fderiv {u : ℂ → F} (hu : Differentiable ℝ u)
    (x : ℂ) (r : ℝ) (z : ℂ) :
    ‖fderiv ℝ (rescaleMap u x r) z‖=|r| * ‖fderiv ℝ u (x+r • z)‖ := by
  rw [rescaleMap_fderiv hu,norm_smul,Real.norm_eq_abs]

theorem weighted_rescale_bounds {u : ℂ → F} (hu : Differentiable ℝ u)
    {x c : ℂ} {R : ℝ} (hg : 0 < ‖fderiv ℝ u x‖)
    (hm : 6 ≤ (R-dist x c)*‖fderiv ℝ u x‖)
    (hb : ∀ y ∈ Metric.closedBall x ((R-dist x c)/2),
      ‖fderiv ℝ u y‖ ≤ 2*‖fderiv ℝ u x‖) :
    ‖fderiv ℝ (rescaleMap u x ‖fderiv ℝ u x‖⁻¹) 0‖=1 ∧
      ∀ z ∈ Metric.closedBall (0:ℂ) 3,
        ‖fderiv ℝ (rescaleMap u x ‖fderiv ℝ u x‖⁻¹) z‖ ≤ 2 := by
  have hr : 0 ≤ ‖fderiv ℝ u x‖⁻¹ := inv_nonneg.mpr hg.le
  constructor
  · rw [rescaleMap_norm_fderiv hu,abs_of_nonneg hr,smul_zero,add_zero,inv_mul_cancel₀ hg.ne']
  · intro z hz
    have hhalf : ‖fderiv ℝ u x‖⁻¹*3 ≤ (R-dist x c)/2 := by
      have hh := mul_le_mul_of_nonneg_right hm hr
      rw [mul_assoc,mul_inv_cancel₀ hg.ne',mul_one] at hh
      linarith
    have hmem : x+‖fderiv ℝ u x‖⁻¹ • z ∈ Metric.closedBall x ((R-dist x c)/2) := by
      rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg hr]
      exact (mul_le_mul_of_nonneg_left (by simpa using hz : ‖z‖ ≤ 3) hr).trans hhalf
    rw [rescaleMap_norm_fderiv hu,abs_of_nonneg hr]
    calc
      _ ≤ ‖fderiv ℝ u x‖⁻¹*(2*‖fderiv ℝ u x‖) := mul_le_mul_of_nonneg_left (hb _ hmem) hr
      _ = 2 := by rw [mul_left_comm,inv_mul_cancel₀ hg.ne',mul_one]

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function
section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem weighted_gradient_maximum (f : ℂ → F) (hf : ContDiff ℝ ∞ f)
    (c : ℂ) {R : ℝ} (hR : 0 < R) (hgrad : 0 < ‖fderiv ℝ f c‖) :
    ∃ x ∈ Metric.ball c R,
      R*‖fderiv ℝ f c‖ ≤ (R-dist x c)*‖fderiv ℝ f x‖ ∧
      ‖fderiv ℝ f c‖ ≤ ‖fderiv ℝ f x‖ ∧
      ∀ y ∈ Metric.closedBall x ((R-dist x c)/2),
        ‖fderiv ℝ f y‖ ≤ 2*‖fderiv ℝ f x‖ := by
  let g : ℂ → ℝ := fun z => (R-dist z c)*‖fderiv ℝ f z‖
  have hg : Continuous g :=
    (continuous_const.sub (continuous_id.dist continuous_const)).mul
      ((hf.continuous_fderiv (by simp)).norm)
  obtain ⟨x,hx,hxm⟩ := (isCompact_closedBall c R).exists_isMaxOn
    (Metric.nonempty_closedBall.mpr hR.le) hg.continuousOn
  have hcm : c ∈ Metric.closedBall c R := Metric.mem_closedBall_self hR.le
  have hcx : R*‖fderiv ℝ f c‖ ≤ (R-dist x c)*‖fderiv ℝ f x‖ := by
    simpa only [Set.mem_ofPred_eq,g,dist_self,sub_zero] using hxm hcm
  have hxp : 0 < R-dist x c := by
    have hm : 0 < (R-dist x c)*‖fderiv ℝ f x‖ := (mul_pos hR hgrad).trans_le hcx
    exact pos_of_mul_pos_left hm (norm_nonneg _)
  have hxmem : x ∈ Metric.ball c R := by
    rw [Metric.mem_ball]
    linarith
  have hgx : ‖fderiv ℝ f c‖ ≤ ‖fderiv ℝ f x‖ := by
    apply le_of_mul_le_mul_left (a := R)
    · calc
        R*‖fderiv ℝ f c‖ ≤ (R-dist x c)*‖fderiv ℝ f x‖ := hcx
        _ ≤ R*‖fderiv ℝ f x‖ := mul_le_mul_of_nonneg_right (by linarith [dist_nonneg (x := x) (y := c)]) (norm_nonneg _)
    · exact hR
  refine ⟨x,hxmem,hcx,hgx,?_⟩
  intro y hy
  have hyx : dist y x ≤ (R-dist x c)/2 := Metric.mem_closedBall.mp hy
  have hyc : dist y c ≤ (R+dist x c)/2 := by
    have hh := dist_triangle y x c
    linarith
  have hymem : y ∈ Metric.closedBall c R := by
    rw [Metric.mem_closedBall]
    linarith
  have hxy := hxm hymem
  change (R-dist y c)*‖fderiv ℝ f y‖ ≤ (R-dist x c)*‖fderiv ℝ f x‖ at hxy
  have hb : ((R-dist x c)/2)*‖fderiv ℝ f y‖ ≤
      (R-dist y c)*‖fderiv ℝ f y‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hh := hb.trans hxy
  nlinarith

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function
open HigherDimensionalBallPacking.Rigidity

theorem locally_uniform_reindex {E F : Type*} [TopologicalSpace E] [UniformSpace F]
    {u : ℕ → E → F} {v : E → F} (hv : TendstoLocallyUniformly u v atTop)
    {a : ℕ → ℕ} (ha : Tendsto a atTop atTop) :
    TendstoLocallyUniformly (fun j => u (a j)) v atTop := by
  intro V hV x
  obtain ⟨U,hU,hUV⟩ := hv V hV x
  exact ⟨U,hU,ha.eventually hUV⟩

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_FramedCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped Manifold
open MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open MeasureTheory
open scoped Topology
open Finset
open scoped ContDiff Classical
open scoped BoundedContinuousFunction
open Topology
open scoped NNReal

namespace HigherDimensionalBallPacking.Rigidity.FramedCR
open HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Filter Function
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem centeredFrame_smooth [FiniteDimensional ℂ E] [CompleteSpace E]
    (S : E ≃L[ℝ] E) (p : E)
    {u : ℂ → E} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (centeredFrame S p u) :=
  S.contDiff.comp (hu.sub contDiff_const)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem centeredFrame_fderiv [FiniteDimensional ℂ E] [CompleteSpace E]
    (S : E ≃L[ℝ] E) (p : E)
    {u : ℂ → E} (hu : Differentiable ℝ u) (z : ℂ) :
    fderiv ℝ (centeredFrame S p u) z=S.toContinuousLinearMap.comp (fderiv ℝ u z) := by
  exact (S.hasFDerivAt.comp z ((hu z).hasFDerivAt.sub_const p)).fderiv

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem frozenCoefficient_smooth [FiniteDimensional ℂ E] [CompleteSpace E]
    (S : E ≃L[ℝ] E) (J : (E →L[ℝ] E))
    {B : ℂ → (E →L[ℝ] E)} (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (frozenCoefficient S J B) :=
  contDiff_const.clm_comp ((hB.sub contDiff_const).clm_comp contDiff_const)

theorem frozen_CR_equation  (S : E ≃L[ℝ] E) (J : (E →L[ℝ] E))
    (hS : ∀ v, S (J v)=Complex.I • S v) (p : E)
    {u : ℂ → E} (hu : Differentiable ℝ u) (B : ℂ → (E →L[ℝ] E)) {z : ℂ}
    (hCR : fderiv ℝ u z Complex.I=B z (fderiv ℝ u z 1)) :
    fderiv ℝ (centeredFrame S p u) z Complex.I-
      Complex.I • fderiv ℝ (centeredFrame S p u) z 1=
      frozenCoefficient S J B z (fderiv ℝ (centeredFrame S p u) z 1) := by
  rw [centeredFrame_fderiv S p hu z]
  change S (fderiv ℝ u z Complex.I)-Complex.I • S (fderiv ℝ u z 1)=
    S ((B z-J) (S.symm (S (fderiv ℝ u z 1))))
  simp only [S.symm_apply_apply,sub_apply,map_sub,hCR,hS]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem frozenCoefficient_fderiv [FiniteDimensional ℂ E] [CompleteSpace E]
    (S : E ≃L[ℝ] E) (J : (E →L[ℝ] E))
    {B : ℂ → (E →L[ℝ] E)} (hB : Differentiable ℝ B) (z : ℂ) :
    fderiv ℝ (frozenCoefficient S J B) z=(frameConjugation S).comp (fderiv ℝ B z) :=
  ((frameConjugation S).hasFDerivAt.comp z ((hB z).hasFDerivAt.sub_const J)).fderiv

theorem frozen_CR_no_gradient_loss 
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (B : ℕ → ℂ → (E →L[ℝ] E)) (hB : ∀ j, ContDiff ℝ ∞ (B j))
    (p : E) (J : (E →L[ℝ] E)) (hJ : HasFrame J)
    {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    (huD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (u j) z‖ ≤ L)
    (hBD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (B j) z‖ ≤ K)
    (hCR : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      fderiv ℝ (u j) z Complex.I=B j z (fderiv ℝ (u j) z 1))
    (hu0 : TendstoUniformlyOn u (fun _ => p) atTop (Metric.closedBall (0:ℂ) 3))
    (hB0 : TendstoUniformlyOn B (fun _ => J) atTop (Metric.closedBall (0:ℂ) 3)) :
    Tendsto (fun j => ‖fderiv ℝ (u j) 0‖) atTop (𝓝 0) := by
  obtain ⟨S,hS⟩ := hJ
  let U : ℕ → ℂ → E := fun j => centeredFrame S p (u j)
  let A : ℕ → ℂ → (E →L[ℝ] E) := fun j => frozenCoefficient S J (B j)
  have hU : ∀ j, ContDiff ℝ ∞ (U j) := fun j => centeredFrame_smooth S p (hu j)
  have hA : ∀ j, ContDiff ℝ ∞ (A j) := fun j => frozenCoefficient_smooth S J (hB j)
  have hUD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      ‖fderiv ℝ (U j) z‖ ≤ ‖S.toContinuousLinearMap‖*L := by
    filter_upwards [huD] with j hj
    intro z hz
    rw [show fderiv ℝ (U j) z=S.toContinuousLinearMap.comp (fderiv ℝ (u j) z) from
      centeredFrame_fderiv S p ((hu j).differentiable (by simp)) z]
    exact (S.toContinuousLinearMap.opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_left (hj z hz) (norm_nonneg _))
  have hAD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      ‖fderiv ℝ (A j) z‖ ≤ ‖frameConjugation S‖*K := by
    filter_upwards [hBD] with j hj
    intro z hz
    rw [show fderiv ℝ (A j) z=(frameConjugation S).comp (fderiv ℝ (B j) z) from
      frozenCoefficient_fderiv S J ((hB j).differentiable (by simp)) z]
    exact ((frameConjugation S).opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_left (hj z hz) (norm_nonneg _))
  have hACR : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      fderiv ℝ (U j) z Complex.I-Complex.I • fderiv ℝ (U j) z 1=
        A j z (fderiv ℝ (U j) z 1) := by
    filter_upwards [hCR] with j hj
    intro z hz
    exact frozen_CR_equation S J hS p ((hu j).differentiable (by simp)) (B j) (hj z hz)
  have hU0 : TendstoUniformlyOn U (fun _ => (0:E)) atTop (Metric.closedBall (0:ℂ) 3) := by
    have hc : ContinuousAt (fun x : E => S (x-p)) p :=
      S.continuous.continuousAt.comp (continuousAt_id.sub continuousAt_const)
    convert continuousAt_comp_uniform_constant hc hu0 using 1
    all_goals try with_reducible_and_instances rfl
    all_goals try simp only [U,sub_self,map_zero]
    all_goals rfl
  have hA0 : TendstoUniformlyOn A (fun _ => (0:(E →L[ℝ] E))) atTop (Metric.closedBall (0:ℂ) 3) := by
    have hc : ContinuousAt (fun x : (E →L[ℝ] E) => frameConjugation S (x-J)) J :=
      (frameConjugation S).continuous.continuousAt.comp (continuousAt_id.sub continuousAt_const)
    convert continuousAt_comp_uniform_constant hc hB0 using 1
    all_goals try with_reducible_and_instances rfl
    all_goals try simp only [A,frameConjugation_apply,sub_self,map_zero]
    all_goals rfl
  have hlim := smallCR_sequence_derivative_zero U hU A hA
    (mul_nonneg (norm_nonneg S.toContinuousLinearMap) hL)
    (mul_nonneg (norm_nonneg (frameConjugation S)) hK) hUD hAD hACR hU0 hA0
  apply squeeze_zero (fun j => norm_nonneg _)
    (fun j => show ‖fderiv ℝ (u j) 0‖ ≤ ‖S.symm.toContinuousLinearMap‖*‖fderiv ℝ (U j) 0‖ from ?_)
    (by simpa using hlim.const_mul ‖S.symm.toContinuousLinearMap‖)
  have he : fderiv ℝ (u j) 0=S.symm.toContinuousLinearMap.comp (fderiv ℝ (U j) 0) := by
    rw [show fderiv ℝ (U j) 0=S.toContinuousLinearMap.comp (fderiv ℝ (u j) 0) from
      centeredFrame_fderiv S p ((hu j).differentiable (by simp)) 0]
    apply ContinuousLinearMap.ext
    intro z
    change (fderiv ℝ (u j) 0) z=S.symm (S ((fderiv ℝ (u j) 0) z))
    simp
  rw [he]
  exact S.symm.toContinuousLinearMap.opNorm_comp_le _

theorem field_CR_no_gradient_loss (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j)) (p : E)
    {L : ℝ} (hL : 0 ≤ L)
    (huD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (u j) z‖ ≤ L)
    (hCR : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (hu0 : TendstoUniformlyOn u (fun _ => p) atTop (Metric.closedBall (0:ℂ) 3)) :
    Tendsto (fun j => ‖fderiv ℝ (u j) 0‖) atTop (𝓝 0) := by
  let B : ℕ → ℂ → (E →L[ℝ] E) := fun j z => H (t j,u j z)
  have hs : s ∈ Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hts (Eventually.of_forall ht)
  have hB (j : ℕ) : ContDiff ℝ ∞ (B j) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact ContDiffAt.comp (g := H) (f := fun z => (t j,u j z)) z
      (hH (t j,u j z) (ht j)) (contDiffAt_const.prodMk (hu j).contDiffAt)
  have hBounded : Bornology.IsBounded
      ((fderiv ℝ H) '' (Icc (0:ℝ) 1 ×ˢ Metric.closedBall p 1)) :=
    ((isCompact_Icc.prod (isCompact_closedBall p 1)).image_of_continuousOn
      (fun y hy => ((hH y hy.1).continuousAt_fderiv (by simp)).continuousWithinAt)).isBounded
  obtain ⟨K,hK,hKb⟩ := hBounded.exists_pos_norm_le
  have hB0 : TendstoUniformlyOn B (fun _ => H (s,p)) atTop (Metric.closedBall (0:ℂ) 3) := by
    convert continuousAt_comp_uniform_constant (hH (s,p) hs).continuousAt
      (uniform_constant_prod hts hu0) using 1
    all_goals try with_reducible_and_instances rfl
  have hBD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      ‖fderiv ℝ (B j) z‖ ≤ K*L := by
    filter_upwards [huD,Metric.tendstoUniformlyOn_iff.mp hu0 1 (by norm_num)] with j hj hju
    intro z hz
    have hmem : (t j,u j z) ∈ Icc (0:ℝ) 1 ×ˢ Metric.closedBall p 1 :=
      ⟨ht j,by simpa [Metric.mem_closedBall,dist_comm] using (hju z hz).le⟩
    have hd : HasFDerivAt (fun z => (t j,u j z))
        ((0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (u j) z)) z :=
      (hasFDerivAt_const (t j) z).prodMk ((hu j).differentiable (by simp) z).hasFDerivAt
    have he : fderiv ℝ (B j) z=(fderiv ℝ H (t j,u j z)).comp
        ((0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (u j) z)) :=
      (HasFDerivAt.comp (g := H) (f := fun z => (t j,u j z)) z
        ((hH (t j,u j z) (ht j)).differentiableAt (by simp)).hasFDerivAt hd).fderiv
    rw [he]
    apply ((fderiv ℝ H (t j,u j z)).opNorm_comp_le _).trans
    have hnorm : ‖(0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (u j) z)‖=‖fderiv ℝ (u j) z‖ := by
      rw [ContinuousLinearMap.opNorm_prod,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
    rw [hnorm]
    exact mul_le_mul (hKb _ ⟨(t j,u j z),hmem,rfl⟩) (hj z hz) (norm_nonneg _) hK.le
  exact frozen_CR_no_gradient_loss u hu B hB p (H (s,p))
    (hHF (s,p) hs) hL (mul_nonneg hK.le hL) huD hBD hCR hu0 hB0

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem rescaleMap_CR_I [FiniteDimensional ℂ E] [CompleteSpace E]
    {J : E → E →L[ℝ] E} {u : ℂ → E}
    (hu : Differentiable ℝ u)
    (hCR : ∀ z, fderiv ℝ u z Complex.I=J (u z) (fderiv ℝ u z 1))
    (x : ℂ) (r : ℝ) (z : ℂ) :
    fderiv ℝ (rescaleMap u x r) z Complex.I=
      J (rescaleMap u x r z) (fderiv ℝ (rescaleMap u x r) z 1) := by
  rw [rescaleMap_fderiv hu]
  simpa only [smul_apply,map_smul,rescaleMap] using
    congrArg (fun v : E => r • v) (hCR (x+r • z))

theorem field_C0_gradient_bound (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (v : ℂ → E) (hv : TendstoLocallyUniformly u v atTop)
    (c : ℂ) {R : ℝ} (_hR : 0 ≤ R) :
    ∃ L ≥ 0, ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall c R, ‖fderiv ℝ (u j) z‖ ≤ L := by
  by_contra hn
  have hbad (j : ℕ) : ∃ i ≥ j, ∃ z ∈ Metric.closedBall c R,
      (j:ℝ)+1 < ‖fderiv ℝ (u i) z‖ := by
    have hnot : ¬ ∀ᶠ i in atTop, ∀ z ∈ Metric.closedBall c R,
        ‖fderiv ℝ (u i) z‖ ≤ (j:ℝ)+1 := by
      intro hh
      exact hn ⟨(j:ℝ)+1,by positivity,hh⟩
    rw [Filter.eventually_atTop] at hnot
    push Not at hnot
    obtain ⟨i,hi,z,hz,hbig⟩ := hnot j
    exact ⟨i,hi,z,hz,hbig⟩
  choose a ha z hz hbig using hbad
  have hat : Tendsto a atTop atTop := tendsto_atTop_mono ha tendsto_id
  have hpos (j : ℕ) : 0 < ‖fderiv ℝ (u (a j)) (z j)‖ := lt_trans (by positivity) (hbig j)
  choose x hx hweight hlarger hlocal using
    (fun j => weighted_gradient_maximum (u (a j)) (hu (a j)) (z j) (by norm_num : (0:ℝ)<1) (hpos j))
  have hxmem (j : ℕ) : x j ∈ Metric.closedBall c (R+1) := by
    have h1 : dist (x j) (z j) < 1 := hx j
    have h2 : dist (z j) c ≤ R := hz j
    rw [Metric.mem_closedBall]
    linarith [dist_triangle (x j) (z j) c]
  obtain ⟨d,hd,φ,hφ,hφx⟩ := (isCompact_closedBall c (R+1)).tendsto_subseq hxmem
  let b : ℕ → ℕ := fun j => a (φ j)
  have hbt : Tendsto b atTop atTop := hat.comp hφ.tendsto_atTop
  let g : ℕ → ℝ := fun j => ‖fderiv ℝ (u (b j)) (x (φ j))‖
  have hgp (j : ℕ) : 0 < g j := (hpos (φ j)).trans_le (hlarger (φ j))
  have hgb (j : ℕ) : (φ j:ℝ)+1 < g j := (hbig (φ j)).trans_le (hlarger (φ j))
  have hgt : Tendsto g atTop atTop := by
    apply tendsto_atTop_mono (fun j => (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)).trans (hgb j).le)
    exact tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  let r : ℕ → ℝ := fun j => (g j)⁻¹
  have hrt : Tendsto r atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hgt
  let U : ℕ → ℂ → E := fun j => rescaleMap (u (b j)) (x (φ j)) (r j)
  have hUs (j : ℕ) : ContDiff ℝ ∞ (U j) := rescaleMap_smooth (hu (b j)) _ _
  have hlim : TendstoUniformlyOn U (fun _ => v d) atTop (Metric.closedBall (0:ℂ) 3) := by
    have hv' := locally_uniform_reindex hv hbt
    have hvc : Continuous v := hv.continuous (Eventually.of_forall (fun j => (hu j).continuous)).frequently
    convert rescaled_maps_uniform_constant hv' hvc.continuousAt hφx hrt
      (Metric.isBounded_closedBall (x := (0:ℂ)) (r := 3)) using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hUb : ∀ᶠ j in atTop, ‖fderiv ℝ (U j) 0‖=1 ∧
      ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (U j) z‖ ≤ 2 := by
    filter_upwards [eventually_ge_atTop (6:ℕ)] with j hj
    apply weighted_rescale_bounds ((hu (b j)).differentiable (by simp)) (hgp j)
    · have hφj : j ≤ φ j := hφ.id_le j
      have h6 : (6:ℝ) ≤ φ j := by exact_mod_cast le_trans hj hφj
      have hw := hweight (φ j)
      dsimp [g,b] at hgb
      nlinarith [hbig (φ j)]
    · exact hlocal (φ j)
  have hUCR : ∀ j z, fderiv ℝ (U j) z Complex.I=
      H (t (b j),U j z) (fderiv ℝ (U j) z 1) := by
    intro j z
    exact rescaleMap_CR_I (J := fun x => H (t (b j),x)) ((hu (b j)).differentiable (by simp)) (hCR (b j)) _ _ _
  have hzero := field_CR_no_gradient_loss H hH hHF (fun j => t (b j))
    (fun j => ht (b j)) (hts.comp hbt) U hUs (v d) (by norm_num : (0:ℝ) ≤ 2)
    (hUb.mono (fun j hj => hj.2)) (Eventually.of_forall (fun j z _ => hUCR j z)) hlim
  have hone : Tendsto (fun j => ‖fderiv ℝ (U j) 0‖) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' (hUb.mono (fun j hj => hj.1.symm))
  have he : (0:ℝ)=1 := tendsto_nhds_unique hzero hone
  norm_num at he

end HigherDimensionalBallPacking.Rigidity.FramedCR
open scoped ContDiff Topology
open Set Filter Function

namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem holder_gradient_limit_C1 (f : ℕ → ℂ → E) (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (v : ℂ → E) (hv : TendstoLocallyUniformly f v atTop)
    {M C α : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (hα : 0 < α)
    (hval : ∀ j z, z ∈ Metric.closedBall (0:ℂ) 1 → ‖f j z‖ ≤ M)
    (hD : ∀ j x y, ‖fderiv ℝ (f j) x-fderiv ℝ (f j) y‖ ≤ C*‖x-y‖^α) :
    ContDiff ℝ 1 v ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun j => fderiv ℝ (f (φ j))) (fderiv ℝ v) atTop := by
  classical
  let D : ℕ → ℂ → (ℂ →L[ℝ] E) := fun j => fderiv ℝ (f j)
  have hD0 (j : ℕ) : ‖D j 0‖ ≤ 2*M+C := by
    have hh := derivative_bound_of_holder_and_values (f j) ((hf j).differentiable (by simp))
      hM hC (by norm_num : (0:ℝ)<1) hα.le (hval j)
      (fun z _ => by simpa using hD j z 0)
    simpa only [div_one,Real.one_rpow,mul_one] using hh
  have hpoint (j : ℕ) (z : ℂ) : ‖D j z‖ ≤ 2*M+C+C*‖z‖^α := by
    have hh := norm_sub_le (D j z-D j 0) (-D j 0)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at hh
    have h := hD j z 0
    simp only [sub_zero] at h
    exact hh.trans (by linarith [hD0 j])
  have heq : UniformEquicontinuous D := by
    apply Metric.uniformEquicontinuous_iff.mpr
    intro ε hε
    have hg : Tendsto (fun r : ℝ => C*r^α) (𝓝 0) (𝓝 0) := by
      simpa [Real.zero_rpow hα.ne'] using
        (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.const_mul C
    have hh := hg.eventually (gt_mem_nhds hε)
    obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp hh
    refine ⟨δ,hδ,?_⟩
    intro z w hzw j
    rw [dist_eq_norm]
    apply (hD j z w).trans_lt
    apply hδb
    simpa [Metric.mem_ball,dist_eq_norm] using hzw
  let F : ℕ → C(ℂ,(ℂ →L[ℝ] E)) := fun j => ⟨D j,(hf j).continuous_fderiv (by simp)⟩
  have heqr : Equicontinuous (fun f : Set.range F => (f.val : ℂ → (ℂ →L[ℝ] E))) := by
    let ψ : Set.range F → ℕ := fun f => f.property.choose
    have hp (f : Set.range F) : F (ψ f) = f.val := f.property.choose_spec
    have he : (fun f : Set.range F => (f.val : ℂ → (ℂ →L[ℝ] E))) = D ∘ ψ := by
      funext f z
      exact congrArg (fun g : C(ℂ,(ℂ →L[ℝ] E)) => g z) (hp f).symm
    rw [he]
    exact heq.equicontinuous.comp ψ
  let : T2Space (UniformOnFun ℂ (ℂ →L[ℝ] E) {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply Set.eq_univ_iff_forall.mpr
      intro z
      exact mem_sUnion_of_mem (mem_singleton z) isCompact_singleton)
  have hcomp : IsCompact (closure (Set.range F)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun f : C(ℂ,(ℂ →L[ℝ] E)) => (f : ℂ → (ℂ →L[ℝ] E)))
      (𝔖 := {K | IsCompact K}) (fun K hK => hK)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K hK
      exact heqr.equicontinuousOn K
    · intro K hK z hz
      refine ⟨Metric.closedBall 0 (2*M+C+C*‖z‖^α),isCompact_closedBall _ _,?_⟩
      rintro f ⟨j,rfl⟩
      rw [Metric.mem_closedBall,dist_zero_right]
      convert hpoint j z using 1
      all_goals try with_reducible_and_instances rfl
  obtain ⟨w,hw,φ,hφ,hφw⟩ := hcomp.tendsto_subseq (x := F)
    (fun j => subset_closure (mem_range_self j))
  have hloc : TendstoLocallyUniformly (fun j => D (φ j)) w atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hφw
  have hvl := locally_uniform_reindex hv hφ.tendsto_atTop
  have hvD (x : ℂ) : HasFDerivAt v (w x) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      hloc.tendstoLocallyUniformlyOn (fun j z _ => ((hf (φ j)).differentiable (by simp) z).hasFDerivAt)
      (fun z _ => hvl.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)) (mem_univ x)
  refine ⟨contDiff_one_iff_hasFDerivAt.mpr ⟨w,w.continuous,hvD⟩,φ,hφ,?_⟩
  convert hloc using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact (hvD z).fderiv

end

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private theorem exists_principal_threshold (B K : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      B*max δ ((2*δ)^((2:ℝ)/3)*K^((1:ℝ)/3)) ≤ 1/2 := by
  let g : ℝ → ℝ := fun r => B*max r ((2*r)^((2:ℝ)/3)*K^((1:ℝ)/3))
  have hg : Continuous g := by
    exact continuous_const.mul (continuous_id.max
      (((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 2/3)).comp
        (continuous_const.mul continuous_id)).mul continuous_const))
  have hg0 : g 0=0 := by simp [g,Real.zero_rpow (show (2:ℝ)/3 ≠ 0 by norm_num)]
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, g r < 1/2 := by
    have ht : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
      hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact ht.eventually (gt_mem_nhds (show g 0 < (1:ℝ)/2 by rw [hg0]; norm_num))
  have hr1 : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 :=
    (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hr0 : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r,h0,h1,hg⟩ := (hr0.and (hr1.and hev)).exists
  exact ⟨r,h0,h1.le,hg.le⟩

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.packageC1Norm
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.packageC1Space
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.packageCompactNorm
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.packageCompactSpace
theorem smallCR_local_modulus (L K : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) :
    ∃ (χ : ℂ → ℝ) (δ C : ℝ), ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      χ =ᶠ[𝓝 0] (fun _ => (1:ℝ)) ∧ (∀ z, |χ z| ≤ 1) ∧
      tsupport χ ⊆ Metric.closedBall (0:ℂ) 3 ∧ 0 < δ ∧ 0 ≤ C ∧
      ∀ (u : ℂ → E) (A : ℂ → E →L[ℝ] E),
        ContDiff ℝ ∞ u → ContDiff ℝ ∞ A →
        (∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖u z‖ ≤ 1) →
        (∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ u z‖ ≤ L) →
        (∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖A z‖ ≤ δ) →
        (∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ A z‖ ≤ K) →
        (∀ z ∈ Metric.closedBall (0:ℂ) 3,
          fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1=A z (fderiv ℝ u z 1)) →
        ∀ x y, ‖fderiv ℝ (fun z => χ z • u z) x-fderiv ℝ (fun z => χ z • u z) y‖ ≤
          C*‖x-y‖^((1:ℝ)/3) := by
  obtain ⟨χ,θ,D,hD,hχ,hχc,hθ,hθc,hχ2,hθ3,hχ1,hθ1,hχθ,hd⟩ := exists_nested_complex_cutoffs
  have hχ3 : tsupport χ ⊆ Metric.closedBall (0:ℂ) 3 :=
    hχ2.trans (Metric.closedBall_subset_closedBall (by norm_num))
  let B := 2*‖compactCRInverse (E := E) 3‖*‖c1HolderDx (E := E)‖
  obtain ⟨δ,hδ,hδ1,hsmall⟩ := exists_principal_threshold B (K+D)
  refine ⟨χ,δ,localSchauderBound E 3 D L (K+D),hχ,hχc,hχ1,
    fun z => (hχθ z).1,hχ3,hδ,?_,?_⟩
  · dsimp [localSchauderBound]
    positivity
  intro u A hu hA huv huD hAv hAD hCR
  let AA : ℂ → E →L[ℝ] E := fun z => θ z • A z
  have hAA : ContDiff ℝ ∞ AA := hθ.smul hA
  have hAAc : HasCompactSupport AA := hθc.smul_right
  have hAAs : tsupport AA ⊆ Metric.closedBall (0:ℂ) 3 :=
    (tsupport_smul_subset_left θ A).trans hθ3
  have hb := cutoff_smul_bounds hθ hA hθ3 (C := 1) (D := D) (M := δ) (L := K)
    (by norm_num) hD hδ.le hK (fun z => (hχθ z).2) (fun z => (hd z).2.2) hAv hAD
  have hAAv : ∀ z, ‖AA z‖ ≤ δ := by simpa only [one_mul] using hb.1
  have hAAD : ∀ z, ‖fderiv ℝ AA z‖ ≤ K+D := by
    intro z
    exact (hb.2 z).trans (by nlinarith)
  apply cutoff_smallCR_schauder 3 χ hχ hχc hχ3 AA hAA hAAc hAAs u hu
    hD hL (add_nonneg hK hD) hδ.le hδ1 (fun z => (hd z).1)
    (fun z => (hd z).2.1) (fun z hz => huv z (hχ3 hz)) (fun z hz => huD z (hχ3 hz))
    hAAv hAAD
  · intro z hz
    rw [show AA z=A z by simp only [AA,hθ1 z hz,one_smul]]
    exact hCR z (hχ3 hz)
  · dsimp [B] at hsmall
    nlinarith only [hsmall]

end

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

theorem smallCR_C1_closure_threshold (L K : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (u : ℕ → ℂ → E) (A : ℕ → ℂ → E →L[ℝ] E)
      (v : ℂ → E), (∀ j, ContDiff ℝ ∞ (u j)) → (∀ j, ContDiff ℝ ∞ (A j)) →
      TendstoLocallyUniformly u v atTop →
      (∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
        ‖u j z‖ ≤ 1 ∧ ‖fderiv ℝ (u j) z‖ ≤ L ∧ ‖A j z‖ ≤ δ ∧
        ‖fderiv ℝ (A j) z‖ ≤ K ∧
        fderiv ℝ (u j) z Complex.I-Complex.I • fderiv ℝ (u j) z 1=
          A j z (fderiv ℝ (u j) z 1)) →
      ContDiffAt ℝ 1 v 0 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun j => fderiv ℝ (u (φ j)) 0) atTop (𝓝 (fderiv ℝ v 0)) := by
  obtain ⟨χ,δ,C,hχ,hχc,hχ1,hχb,hχ3,hδ,hC,hmod⟩ := smallCR_local_modulus (E := E) L K hL hK
  refine ⟨δ,hδ,?_⟩
  intro u A v hu hA hv hb
  obtain ⟨N,hN⟩ := eventually_atTop.mp hb
  let f : ℕ → ℂ → E := fun j z => χ z • u (j+N) z
  let w : ℂ → E := fun z => χ z • v z
  have hvc : Continuous v := hv.continuous (Eventually.of_forall (fun j => (hu j).continuous)).frequently
  have hχlim : TendstoLocallyUniformly (fun _ : ℕ => χ) χ atTop := by
    exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
      (tendsto_const_nhds (x := (⟨χ,hχ.continuous⟩ : C(ℂ,ℝ))))
  have hflim : TendstoLocallyUniformly f w atTop := by
    exact hχlim.smul₀ (locally_uniform_reindex hv (tendsto_add_atTop_nat N)) hχ.continuous hvc
  have hfb (j : ℕ) (z : ℂ) (hz : z ∈ Metric.closedBall (0:ℂ) 1) : ‖f j z‖ ≤ 1 := by
    have hu1 := (hN (j+N) (Nat.le_add_left N j) z
      ((Metric.closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 3)) hz)).1
    calc ‖f j z‖ = |χ z| *‖u (j+N) z‖ := by simp only [f,norm_smul,Real.norm_eq_abs]
         _ ≤ 1*1 := mul_le_mul (hχb z) hu1 (norm_nonneg _) (by norm_num)
         _ = 1 := one_mul 1
  have hfmod (j : ℕ) := hmod (u (j+N)) (A (j+N)) (hu _) (hA _)
    (fun z hz => (hN _ (Nat.le_add_left N j) z hz).1)
    (fun z hz => (hN _ (Nat.le_add_left N j) z hz).2.1)
    (fun z hz => (hN _ (Nat.le_add_left N j) z hz).2.2.1)
    (fun z hz => (hN _ (Nat.le_add_left N j) z hz).2.2.2.1)
    (fun z hz => (hN _ (Nat.le_add_left N j) z hz).2.2.2.2)
  obtain ⟨hw,φ,hφ,hφD⟩ := holder_gradient_limit_C1 f (fun j => hχ.smul (hu (j+N))) w hflim
    (by norm_num : (0:ℝ) ≤ 1) hC (by norm_num : (0:ℝ) < 1/3) hfb hfmod
  have he (g : ℂ → E) : (fun z => χ z • g z) =ᶠ[𝓝 0] g := by
    filter_upwards [hχ1] with z hz
    simp only [hz,one_smul]
  refine ⟨hw.contDiffAt.congr_of_eventuallyEq (he v).symm,fun j => φ j+N,
    fun i j hij => Nat.add_lt_add_right (hφ hij) N,?_⟩
  have hd := hφD.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (0:ℂ))
  convert hd using 1
  · funext j
    exact (he (u (φ j+N))).fderiv_eq.symm
  · exact congrArg nhds (he v).fderiv_eq.symm

end

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem locally_uniform_small_ball {u : ℕ → ℂ → E} {v : ℂ → E}
    (hv : TendstoLocallyUniformly u v atTop) {c : ℂ} (hvc : ContinuousAt v c)
    {t : ℕ → ℝ} {s : ℝ} (ht : Tendsto t atTop (𝓝 s))
    {G : ℝ × E → F} (hG : ContinuousAt G (s,v c)) (hG0 : G (s,v c)=0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ᶠ j in atTop,
      ∀ z ∈ Metric.closedBall c r, ‖G (t j,u j z)‖ ≤ ε := by
  obtain ⟨δ,hδ,hδG⟩ := Metric.continuousAt_iff.mp hG ε hε
  obtain ⟨a,ha,hav⟩ := Metric.continuousAt_iff.mp hvc (δ/2) (by linarith)
  obtain ⟨U,hU,hUf⟩ := hv _ (Metric.dist_mem_uniformity (by linarith : (0:ℝ)<δ/2)) c
  obtain ⟨b,hb,hbU⟩ := Metric.mem_nhds_iff.mp hU
  let r := min 1 (min a b/2)
  have hr : 0 < r := lt_min (by norm_num) (half_pos (lt_min ha hb))
  refine ⟨r,hr,min_le_left _ _,?_⟩
  filter_upwards [hUf,Metric.tendsto_nhds.mp ht δ hδ] with j hj hjt
  intro z hz
  have hza : dist z c < a := by
    have h := (show dist z c ≤ r from hz).trans (min_le_right 1 (min a b/2))
    linarith [min_le_left a b,lt_min ha hb]
  have hzb : dist z c < b := by
    have h := (show dist z c ≤ r from hz).trans (min_le_right 1 (min a b/2))
    linarith [min_le_right a b,lt_min ha hb]
  have h1 : dist (v z) (u j z)<δ/2 := hj z (hbU hzb)
  have h2 : dist (v z) (v c)<δ/2 := hav hza
  have hu : dist (u j z) (v c)<δ := by
    have hh := dist_triangle (u j z) (v z) (v c)
    rw [dist_comm (u j z) (v z)] at hh
    linarith
  have hh := hδG (show dist (t j,u j z) (s,v c)<δ by rw [Prod.dist_eq]; exact max_lt hjt hu)
  simpa only [hG0,dist_zero_right] using hh.le

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_TangentLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
open HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem frame_rescale_inverse [FiniteDimensional ℂ E] [CompleteSpace E]
    (S : E ≃L[ℝ] E)
    (p : E) (u : ℂ → E) (c : ℂ) {r : ℝ} (hr : r ≠ 0)
    (h : ContDiffAt ℝ 1 (centeredFrame S p (rescaleMap u c r)) 0) :
    ContDiffAt ℝ 1 u c ∧ fderiv ℝ u c=r⁻¹ • S.symm.toContinuousLinearMap.comp
      (fderiv ℝ (centeredFrame S p (rescaleMap u c r)) 0) := by
  let U := centeredFrame S p (rescaleMap u c r)
  let a : ℂ → ℂ := fun z => r⁻¹ • (z-c)
  have ha0 : a c=0 := by simp [a]
  have ha : ContDiff ℝ ∞ a := (contDiff_id.sub contDiff_const).const_smul r⁻¹
  have hid : (fun z => S.symm (U (a z))+p)=u := by
    funext z
    simp only [U,centeredFrame,rescaleMap,a,smul_smul,mul_inv_cancel₀ hr,one_smul,
      add_sub_cancel,ContinuousLinearEquiv.symm_apply_apply,sub_add_cancel]
  have hh : ContDiffAt ℝ 1 U (a c) := by simpa only [ha0] using h
  have huc : ContDiffAt ℝ 1 u c := by
    rw [←hid]
    exact (S.symm.contDiff.contDiffAt.comp c (hh.comp c (ha.of_le (by simp)).contDiffAt)).add contDiffAt_const
  refine ⟨huc,?_⟩
  have had : HasFDerivAt a (r⁻¹ • ContinuousLinearMap.id ℝ ℂ) c := by
    convert (((hasFDerivAt_id (𝕜 := ℝ) c).sub_const c).const_smul r⁻¹) using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hud := ((S.symm.hasFDerivAt.comp c
    ((hh.differentiableAt (by simp)).hasFDerivAt.comp c had)).add_const p).fderiv
  simp only [Function.comp_def] at hud
  rw [hid] at hud
  rw [ha0] at hud
  simpa only [ContinuousLinearMap.comp_smul,ContinuousLinearMap.comp_id] using hud

theorem field_C0_C1At (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (v : ℂ → E) (hv : TendstoLocallyUniformly u v atTop) (c : ℂ) :
    ContDiffAt ℝ 1 v c ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => fderiv ℝ (u (φ j)) c) atTop (𝓝 (fderiv ℝ v c)) := by
  have hs : s ∈ Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hts (Eventually.of_forall ht)
  have hvc : Continuous v := hv.continuous (Eventually.of_forall (fun j => (hu j).continuous)).frequently
  obtain ⟨L,hL,hLu⟩ := field_C0_gradient_bound H hH hHF t ht hts u hu hCR v hv c
    (by norm_num : (0:ℝ) ≤ 1)
  have hBounded : Bornology.IsBounded
      ((fderiv ℝ H) '' (Icc (0:ℝ) 1 ×ˢ Metric.closedBall (v c) 1)) :=
    ((isCompact_Icc.prod (isCompact_closedBall (v c) 1)).image_of_continuousOn
      (fun y hy => ((hH y hy.1).continuousAt_fderiv (by simp)).continuousWithinAt)).isBounded
  obtain ⟨K,hK,hKb⟩ := hBounded.exists_pos_norm_le
  obtain ⟨S,hS⟩ := hHF (s,v c) hs
  let LS := ‖S.toContinuousLinearMap‖*L
  let KS := ‖frameConjugation S‖*(K*L)
  obtain ⟨δ,hδ,hth⟩ := smallCR_C1_closure_threshold (E := E) LS KS
    (mul_nonneg (norm_nonneg S.toContinuousLinearMap) hL)
    (mul_nonneg (norm_nonneg (frameConjugation S)) (mul_nonneg hK.le hL))
  obtain ⟨ru,hru,hru1,hruv⟩ := locally_uniform_small_ball (c := c) hv hvc.continuousAt hts
    (G := fun y : ℝ × E => S (y.2-v c))
    (S.continuous.continuousAt.comp (continuousAt_snd.sub continuousAt_const))
    (by simp) (by norm_num : (0:ℝ)<1)
  obtain ⟨ra,hra,hra1,hraA⟩ := locally_uniform_small_ball (c := c) hv hvc.continuousAt hts
    (G := fun y : ℝ × E => frameConjugation S (H y-H (s,v c)))
    ((frameConjugation S).continuous.continuousAt.comp
      ((hH (s,v c) hs).continuousAt.sub continuousAt_const)) (by simp) hδ
  obtain ⟨rp,hrp,hrp1,hrpv⟩ := locally_uniform_small_ball (c := c) hv hvc.continuousAt hts
    (G := fun y : ℝ × E => y.2-v c)
    (continuousAt_snd.sub continuousAt_const) (by simp) (by norm_num : (0:ℝ)<1)
  let r := min ru (min ra rp)/3
  have hr : 0 < r := div_pos (lt_min hru (lt_min hra hrp)) (by norm_num)
  have hr3u : 3*r ≤ ru := by dsimp [r]; linarith [min_le_left ru (min ra rp)]
  have hr3a : 3*r ≤ ra := by dsimp [r]; linarith [min_le_right ru (min ra rp),min_le_left ra rp]
  have hr3p : 3*r ≤ rp := by dsimp [r]; linarith [min_le_right ru (min ra rp),min_le_right ra rp]
  have hr1 : r ≤ 1 := by linarith
  let w : ℕ → ℂ → E := fun j => rescaleMap (u j) c r
  let U : ℕ → ℂ → E := fun j => centeredFrame S (v c) (w j)
  let B : ℕ → ℂ → (E →L[ℝ] E) := fun j z => H (t j,w j z)
  let A : ℕ → ℂ → (E →L[ℝ] E) := fun j => frozenCoefficient S (H (s,v c)) (B j)
  let V := centeredFrame S (v c) (rescaleMap v c r)
  have hw (j : ℕ) : ContDiff ℝ ∞ (w j) := rescaleMap_smooth (hu j) c r
  have hU (j : ℕ) : ContDiff ℝ ∞ (U j) := centeredFrame_smooth S (v c) (hw j)
  have hB (j : ℕ) : ContDiff ℝ ∞ (B j) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact ContDiffAt.comp (g := H) (f := fun z => (t j,w j z)) z
      (hH (t j,w j z) (ht j)) (contDiffAt_const.prodMk (hw j).contDiffAt)
  have hA (j : ℕ) : ContDiff ℝ ∞ (A j) := frozenCoefficient_smooth S _ (hB j)
  have hmap (z : ℂ) (hz : z ∈ Metric.closedBall (0:ℂ) 3) : dist (c+r • z) c ≤ 3*r := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    nlinarith [show ‖z‖ ≤ 3 by simpa using hz]
  have hb : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      ‖U j z‖ ≤ 1 ∧ ‖fderiv ℝ (U j) z‖ ≤ LS ∧ ‖A j z‖ ≤ δ ∧
      ‖fderiv ℝ (A j) z‖ ≤ KS ∧
      fderiv ℝ (U j) z Complex.I-Complex.I • fderiv ℝ (U j) z 1=
        A j z (fderiv ℝ (U j) z 1) := by
    filter_upwards [hLu,hruv,hraA,hrpv] with j hjD hju hjA hjp
    intro z hz
    have hmem : c+r • z ∈ Metric.closedBall c 1 := (hmap z hz).trans (hr3u.trans hru1)
    have hwD : ‖fderiv ℝ (w j) z‖ ≤ L := by
      rw [show ‖fderiv ℝ (w j) z‖=|r| * ‖fderiv ℝ (u j) (c+r • z)‖ from
        rescaleMap_norm_fderiv ((hu j).differentiable (by simp)) c r z,abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_left (hjD _ hmem) hr.le).trans
        (by simpa using mul_le_mul_of_nonneg_right hr1 hL)
    have hp : w j z ∈ Metric.closedBall (v c) 1 := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,w,rescaleMap] using
        (hjp (c+r • z) ((hmap z hz).trans hr3p))
    have hBD : ‖fderiv ℝ (B j) z‖ ≤ K*L := by
      have hd : HasFDerivAt (fun z => (t j,w j z))
          ((0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (w j) z)) z :=
        (hasFDerivAt_const (t j) z).prodMk ((hw j).differentiable (by simp) z).hasFDerivAt
      have he : fderiv ℝ (B j) z=(fderiv ℝ H (t j,w j z)).comp
          ((0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (w j) z)) :=
        (HasFDerivAt.comp (g := H) (f := fun z => (t j,w j z)) z
          ((hH (t j,w j z) (ht j)).differentiableAt (by simp)).hasFDerivAt hd).fderiv
      rw [he]
      apply ((fderiv ℝ H (t j,w j z)).opNorm_comp_le _).trans
      have hnorm : ‖(0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (w j) z)‖=‖fderiv ℝ (w j) z‖ := by
        rw [ContinuousLinearMap.opNorm_prod,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
      rw [hnorm]
      exact mul_le_mul (hKb _ ⟨(t j,w j z),⟨ht j,hp⟩,rfl⟩) hwD (norm_nonneg _) hK.le
    refine ⟨hju _ ((hmap z hz).trans hr3u),?_,hjA _ ((hmap z hz).trans hr3a),?_,?_⟩
    · rw [show fderiv ℝ (U j) z=S.toContinuousLinearMap.comp (fderiv ℝ (w j) z) from
        centeredFrame_fderiv S (v c) ((hw j).differentiable (by simp)) z]
      exact (S.toContinuousLinearMap.opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left hwD (norm_nonneg _))
    · rw [show fderiv ℝ (A j) z=(frameConjugation S).comp (fderiv ℝ (B j) z) from
        frozenCoefficient_fderiv S _ ((hB j).differentiable (by simp)) z]
      exact ((frameConjugation S).opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left hBD (norm_nonneg _))
    · exact frozen_CR_equation S _ hS (v c) ((hw j).differentiable (by simp)) (B j)
        (rescaleMap_CR_I (J := fun x => H (t j,x)) ((hu j).differentiable (by simp)) (hCR j) c r z)
  have hUV : TendstoLocallyUniformly U V atTop := by
    have hf : UniformContinuous (fun x : E => S (x-v c)) :=
      S.toContinuousLinearMap.uniformContinuous.comp (uniformContinuous_id.sub uniformContinuous_const)
    exact hf.comp_tendstoLocallyUniformly
      (hv.comp (fun z : ℂ => c+r • z) (continuous_const.add (continuous_id.const_smul r)))
  obtain ⟨hV,φ,hφ,hφD⟩ := hth U A V hU hA hUV hb
  obtain ⟨hcv,hdv⟩ := frame_rescale_inverse S (v c) v c hr.ne' hV
  refine ⟨hcv,φ,hφ,?_⟩
  have hcont : Continuous (fun T : ℂ →L[ℝ] E => r⁻¹ • S.symm.toContinuousLinearMap.comp T) :=
    (continuous_const.clm_comp continuous_id).const_smul r⁻¹
  have hlim := hcont.continuousAt.tendsto.comp hφD
  convert hlim using 1
  · funext j
    exact (frame_rescale_inverse S (v c) (u (φ j)) c hr.ne' ((hU (φ j)).of_le (by simp)).contDiffAt).2
  · exact congrArg nhds hdv

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
open HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem fderiv_translate [FiniteDimensional ℂ E] [CompleteSpace E]
    (f : ℂ → E) (hf : Differentiable ℝ f) (x z : ℂ) :
    fderiv ℝ (fun w => f (x+w)) z=fderiv ℝ f (x+z) := by
  have hh := ((hf (x+z)).hasFDerivAt.comp z
    ((hasFDerivAt_id (𝕜 := ℝ) z).const_add x)).fderiv
  simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using hh

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem locally_uniform_translate [NormedSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    {u : ℕ → ℂ → E} {v : ℂ → E}
    (hu : ∀ j, Continuous (u j)) (hv : Continuous v)
    (h : TendstoLocallyUniformly u v atTop) {x : ℕ → ℂ} {c : ℂ}
    (hx : Tendsto x atTop (𝓝 c)) :
    TendstoLocallyUniformly (fun j z => u j (x j+z)) (fun z => v (c+z)) atTop := by
  let U : ℕ → C(ℂ,E) := fun j => ⟨u j,hu j⟩
  let V : C(ℂ,E) := ⟨v,hv⟩
  have hU : Tendsto U atTop (𝓝 V) := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr h
  have hc : Tendsto (fun j => ContinuousMap.const ℂ (x j)) atTop
      (𝓝 (ContinuousMap.const ℂ c)) := ContinuousMap.continuous_const'.continuousAt.tendsto.comp hx
  have ha := hc.add (tendsto_const_nhds (x := ContinuousMap.id ℂ))
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hU.compCM ha)

theorem field_C0_C1_closure (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (v : ℂ → E) (hv : TendstoLocallyUniformly u v atTop) :
    ContDiff ℝ 1 v ∧ TendstoLocallyUniformly (fun j => fderiv ℝ (u j)) (fderiv ℝ v) atTop := by
  have hv1 : ContDiff ℝ 1 v := contDiff_iff_contDiffAt.mpr
    (fun c => (field_C0_C1At H hH hHF t ht hts u hu hCR v hv c).1)
  refine ⟨hv1,?_⟩
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hn
  have hfreq : ∃ᶠ j in atTop, ∃ x ∈ K,
      ε ≤ dist (fderiv ℝ v x) (fderiv ℝ (u j) x) := by
    simpa only [Filter.Frequently,not_exists,not_and,not_le] using hn
  obtain ⟨a,hat,ha⟩ := exists_seq_forall_of_frequently hfreq
  choose x hx hbad using ha
  obtain ⟨c,hc,φ,hφ,hφx⟩ := hK.tendsto_subseq hx
  let b : ℕ → ℕ := fun j => a (φ j)
  have hbt : Tendsto b atTop atTop := hat.comp hφ.tendsto_atTop
  let U : ℕ → ℂ → E := fun j z => u (b j) (x (φ j)+z)
  let V : ℂ → E := fun z => v (c+z)
  have hUs (j : ℕ) : ContDiff ℝ ∞ (U j) := (hu (b j)).comp (contDiff_const.add contDiff_id)
  have hUD (j : ℕ) (z : ℂ) : fderiv ℝ (U j) z=fderiv ℝ (u (b j)) (x (φ j)+z) :=
    fderiv_translate _ ((hu (b j)).differentiable (by simp)) _ _
  have hVD (z : ℂ) : fderiv ℝ V z=fderiv ℝ v (c+z) :=
    fderiv_translate _ (hv1.differentiable (by simp)) _ _
  have hUCR (j : ℕ) (z : ℂ) : fderiv ℝ (U j) z Complex.I=
      H (t (b j),U j z) (fderiv ℝ (U j) z 1) := by
    rw [hUD]
    exact hCR (b j) _
  have hlim : TendstoLocallyUniformly U V atTop :=
    locally_uniform_translate (fun j => (hu (b j)).continuous) hv1.continuous
      (locally_uniform_reindex hv hbt) hφx
  obtain ⟨_,ψ,hψ,hψD⟩ := field_C0_C1At H hH hHF (fun j => t (b j))
    (fun j => ht (b j)) (hts.comp hbt) U hUs hUCR V hlim 0
  have hlimD : Tendsto (fun j => fderiv ℝ (u (b (ψ j))) (x (φ (ψ j))))
      atTop (𝓝 (fderiv ℝ v c)) := by
    simpa only [hUD,hVD,add_zero] using hψD
  have hvD := ((hv1.continuous_fderiv (by simp)).continuousAt.tendsto.comp
    (hφx.comp hψ.tendsto_atTop))
  have hdist : Tendsto (fun j => dist (fderiv ℝ v (x (φ (ψ j))))
      (fderiv ℝ (u (b (ψ j))) (x (φ (ψ j))))) atTop (𝓝 0) := by
    convert hvD.dist hlimD using 1 <;> simp only [Function.comp_def,dist_self]
  obtain ⟨j,hj⟩ := (hdist.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (hbad (φ (ψ j)))) hj

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem HasFrame.square [FiniteDimensional ℂ E] [CompleteSpace E]
    {J : E →L[ℝ] E} (hJ : HasFrame J) (v : E) : J (J v)=-v := by
  obtain ⟨S,hS⟩ := hJ
  apply S.injective
  simp only [hS,smul_smul,Complex.I_mul_I,neg_one_smul,map_neg]

theorem tangentMap_hasFrame {J K : E →L[ℝ] E} (hJ : HasFrame J)
    (hK : ∀ v, K (J v)+J (K v)=0) : HasFrame (tangentMap J K) := by
  obtain ⟨S,hS⟩ := hJ
  have hJJ : ∀ v, J (J v)=-v := HasFrame.square ⟨S,hS⟩
  let C : E →L[ℝ] E := -(1/2:ℝ) • J.comp K
  have hCJ (a : E) : C (J a)=-(1/2:ℝ) • K a := by
    have hKJ : K (J a)=-J (K a) := eq_neg_of_add_eq_zero_left (hK a)
    simp only [C,smul_apply,ContinuousLinearMap.comp_apply,hKJ,map_neg,hJJ,neg_neg]
  have hJC (a : E) : J (C a)=(1/2:ℝ) • K a := by
    simp only [C,smul_apply,neg_apply,ContinuousLinearMap.comp_apply,map_neg,map_smul,hJJ,smul_neg,neg_smul,neg_neg]
  refine ⟨(shearEquiv C).trans (S.prodCongr S),?_⟩
  rintro ⟨a,b⟩
  change (S (J a),S (K a+J b+C (J a)))=(Complex.I • S a,Complex.I • S (b+C a))
  rw [hS a,←hS (b+C a),map_add J,hCJ a,hJC a]
  congr 2
  module

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem tangentField_smooth [FiniteDimensional ℂ E] [CompleteSpace E]
    (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (y : ℝ × (E × E)) (hy : y.1 ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ (tangentField H) y := by
  have hbase : ContDiffAt ℝ ∞ (fun y : ℝ × (E × E) => (y.1,y.2.1)) y :=
    contDiffAt_fst.prodMk (contDiffAt_fst.comp y contDiffAt_snd)
  have hvec : ContDiffAt ℝ ∞ (fun y : ℝ × (E × E) => ((0:ℝ),y.2.2)) y :=
    contDiffAt_const.prodMk (contDiffAt_snd.comp y contDiffAt_snd)
  have hJ := (hH (y.1,y.2.1) hy).comp y hbase
  have hK := (((hH (y.1,y.2.1) hy).fderiv_right (by simp)).comp y hbase).clm_apply hvec
  exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := E × E) (F := E) (G := E) ℝ).toContinuousLinearEquiv.contDiff.contDiffAt.comp y
    ((hJ.clm_comp contDiffAt_const).prodMk
      ((hK.clm_comp contDiffAt_const).add (hJ.clm_comp contDiffAt_const)))

theorem field_derivative_anticommute (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x Y a : E) :
    fderiv ℝ H (t,x) (0,Y) (H (t,x) a)+H (t,x) (fderiv ℝ H (t,x) (0,Y) a)=0 := by
  let B : E → E →L[ℝ] E := fun x => H (t,x)
  let D : E →L[ℝ] (E →L[ℝ] E) := (fderiv ℝ H (t,x)).comp
    ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E))
  have hB : HasFDerivAt B D x :=
    ((hH (t,x) ht).differentiableAt (by simp)).hasFDerivAt.comp x
      ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  have hBB := (hB.clm_apply (hB.clm_apply (hasFDerivAt_const a x))).fderiv
  have he : (fun z => B z (B z a))=fun _ : E => -a := by
    funext z
    exact (hHF (t,z) ht).square a
  rw [he,fderiv_const_apply] at hBB
  have hh := congrArg (fun T : E →L[ℝ] E => T Y) hBB
  simpa [B,D,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,add_comm] using hh.symm

theorem tangentField_hasFrame (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (y : ℝ × (E × E)) (hy : y.1 ∈ Icc (0:ℝ) 1) : HasFrame (tangentField H y) :=
  tangentMap_hasFrame (hHF (y.1,y.2.1) hy)
    (field_derivative_anticommute H hH hHF hy y.2.1 y.2.2)

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem tangentCurve_smooth [FiniteDimensional ℂ E] [CompleteSpace E]
    {u : ℂ → E} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (tangentCurve u) := hu.prodMk ((hu.fderiv_right (by simp)).clm_apply contDiff_const)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem fderiv_directional [FiniteDimensional ℂ E] [CompleteSpace E]
    {u : ℂ → E} (hu : ContDiff ℝ ∞ u) (z a b : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ u w a) z b=fderiv ℝ (fderiv ℝ u) z b a := by
  rw [fderiv_clm_apply ((hu.fderiv_right (by simp : (∞:WithTop ℕ∞)+1 ≤ ∞)).differentiable (by simp) z)
    (differentiableAt_const a)]
  simp

theorem tangentCurve_fderiv {u : ℂ → E} (hu : ContDiff ℝ ∞ u) (z a : ℂ) :
    fderiv ℝ (tangentCurve u) z a=(fderiv ℝ u z a,fderiv ℝ (fderiv ℝ u) z a 1) := by
  have hDu : Differentiable ℝ (fun w => fderiv ℝ u w 1) :=
    ((hu.fderiv_right (by simp : (∞:WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).differentiable (by simp)
  have hh := (((hu.differentiable (by simp)) z).hasFDerivAt.prodMk (hDu z).hasFDerivAt).fderiv
  change fderiv ℝ (fun z => (u z,fderiv ℝ u z 1)) z a=_
  rw [hh]
  simp only [ContinuousLinearMap.prod_apply,fderiv_directional hu]

theorem tangentCurve_CR (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) {u : ℂ → E} (hu : ContDiff ℝ ∞ u)
    (hCR : ∀ z, fderiv ℝ u z Complex.I=H (t,u z) (fderiv ℝ u z 1)) :
    ∀ z, fderiv ℝ (tangentCurve u) z Complex.I=
      tangentField H (t,tangentCurve u z) (fderiv ℝ (tangentCurve u) z 1) := by
  intro z
  let B : ℂ → E →L[ℝ] E := fun w => H (t,u w)
  let DB : ℂ →L[ℝ] (E →L[ℝ] E) := (fderiv ℝ H (t,u z)).comp
    ((0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ u z))
  have hB : HasFDerivAt B DB z :=
    ((hH (t,u z) ht).differentiableAt (by simp)).hasFDerivAt.comp z
      ((hasFDerivAt_const t z).prodMk ((hu.differentiable (by simp)) z).hasFDerivAt)
  have hDu : Differentiable ℝ (fun w => fderiv ℝ u w 1) :=
    ((hu.fderiv_right (by simp : (∞:WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).differentiable (by simp)
  have hR := (hB.clm_apply (hDu z).hasFDerivAt).fderiv
  have he : (fun w => fderiv ℝ u w Complex.I)=(fun w => B w (fderiv ℝ u w 1)) := funext hCR
  have hd := congrArg (fun f : ℂ → E => fderiv ℝ f z 1) he
  rw [fderiv_directional hu,hR] at hd
  have hs := (hu.contDiffAt (x := z)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [tangentCurve_fderiv hu,tangentCurve_fderiv hu]
  change (fderiv ℝ u z Complex.I,fderiv ℝ (fderiv ℝ u) z Complex.I 1)=
    (H (t,u z) (fderiv ℝ u z 1),
      fderiv ℝ H (t,u z) (0,fderiv ℝ u z 1) (fderiv ℝ u z 1)+
        H (t,u z) (fderiv ℝ (fderiv ℝ u) z 1 1))
  rw [hCR z,hs Complex.I 1]
  congr 1
  simpa [B,DB,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    fderiv_directional hu,add_comm] using hd

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem field_C1_CR_limit [FiniteDimensional ℂ E] [CompleteSpace E]
    (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E)
    (hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (v : ℂ → E) (hv : TendstoLocallyUniformly u v atTop)
    (hDv : TendstoLocallyUniformly (fun j => fderiv ℝ (u j)) (fderiv ℝ v) atTop) :
    ∀ z, fderiv ℝ v z Complex.I=H (s,v z) (fderiv ℝ v z 1) := by
  intro z
  have hs : s ∈ Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hts (Eventually.of_forall ht)
  have hvz := hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  have hDz := hDv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  have hp : Tendsto (fun j => (t j,u j z)) atTop (𝓝 (s,v z)) := hts.prodMk_nhds hvz
  have hJ : Tendsto (fun j => H (t j,u j z)) atTop (𝓝 (H (s,v z))) :=
    (hH (s,v z) hs).continuousAt.tendsto.comp hp
  have happ (a : ℂ) : Continuous (fun T : ℂ →L[ℝ] E => T a) :=
    continuous_id.clm_apply continuous_const
  have hleft : Tendsto (fun j => fderiv ℝ (u j) z Complex.I) atTop
      (𝓝 (fderiv ℝ v z Complex.I)) := (happ Complex.I).continuousAt.tendsto.comp hDz
  have heval : Continuous (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hright : Tendsto (fun j => H (t j,u j z) (fderiv ℝ (u j) z 1)) atTop
      (𝓝 (H (s,v z) (fderiv ℝ v z 1))) := by
    have hp' : Tendsto (fun j => (H (t j,u j z),fderiv ℝ (u j) z 1)) atTop
        (𝓝 (H (s,v z),fderiv ℝ v z 1)) :=
      hJ.prodMk_nhds ((happ 1).continuousAt.tendsto.comp hDz)
    convert (heval.tendsto (H (s,v z),fderiv ℝ v z 1)).comp hp' using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  exact tendsto_nhds_unique hleft (hright.congr (fun j => (hCR j z).symm))

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem realLinear_complex_apply [FiniteDimensional ℂ E] [CompleteSpace E]
    (D : ℂ →L[ℝ] E) (z : ℂ) :
    D z=z.re • D 1+z.im • D Complex.I := by
  have hz : z=z.re • (1:ℂ)+z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  simp only [map_add,map_smul]

theorem CR_contDiff_succ {m : ℕ} (H : E → E →L[ℝ] E) (hH : ContDiff ℝ ∞ H)
    (v : ℂ → E) (hv1 : ContDiff ℝ 1 v) (hvm : ContDiff ℝ m v)
    (hDx : ContDiff ℝ m (fun z => fderiv ℝ v z 1))
    (hCR : ∀ z, fderiv ℝ v z Complex.I=H (v z) (fderiv ℝ v z 1)) :
    ContDiff ℝ (m+1 : ℕ) v := by
  rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv]
  refine ⟨hv1.differentiable (by simp),by simp,?_⟩
  apply contDiff_clm_apply_iff.mpr
  intro a
  have he : (fun z => fderiv ℝ v z a)=fun z =>
      a.re • fderiv ℝ v z 1+a.im • H (v z) (fderiv ℝ v z 1) := by
    funext z
    rw [realLinear_complex_apply,hCR]
  rw [he]
  have hHm : ContDiff ℝ m H := hH.of_le (by
    change ((m : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  exact (hDx.const_smul a.re).add (((hHm.comp hvm).clm_apply hDx).const_smul a.im)

end HigherDimensionalBallPacking.Rigidity.FramedCR

namespace HigherDimensionalBallPacking.Rigidity.FramedCR

theorem field_C0_contDiff_nat (m : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
      [FiniteDimensional ℂ E] [CompleteSpace E]
      (H : ℝ × E → E →L[ℝ] E)
      (_hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
      (_hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
      (t : ℕ → ℝ) (_ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
      (_hts : Tendsto t atTop (𝓝 s))
      (u : ℕ → ℂ → E) (_hu : ∀ j, ContDiff ℝ ∞ (u j))
      (_hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
      (v : ℂ → E) (_hv : TendstoLocallyUniformly u v atTop), ContDiff ℝ m v := by
  induction m with
  | zero =>
    intro E _ _ _ _ H hH hHF t ht s hts u hu hCR v hv
    exact contDiff_zero.mpr
      (hv.continuous (Eventually.of_forall (fun j => (hu j).continuous)).frequently)
  | succ m ih =>
    intro E _ _ _ _ H hH hHF t ht s hts u hu hCR v hv
    have hs : s ∈ Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hts (Eventually.of_forall ht)
    obtain ⟨hv1,hDv⟩ := field_C0_C1_closure H hH hHF t ht hts u hu hCR v hv
    have hCRv := field_C1_CR_limit H hH t ht hts u hCR v hv hDv
    have happ : UniformContinuous (fun D : ℂ →L[ℝ] E => D 1) :=
      (ContinuousLinearMap.apply ℝ E (1:ℂ)).uniformContinuous
    have hlim : TendstoLocallyUniformly (fun j => tangentCurve (u j)) (tangentCurve v) atTop :=
      hv.prodMk (happ.comp_tendstoLocallyUniformly hDv)
    have hW := ih (E × E) (tangentField H) (tangentField_smooth H hH)
      (tangentField_hasFrame H hH hHF) t ht hts (fun j => tangentCurve (u j))
      (fun j => tangentCurve_smooth (hu j)) (fun j => tangentCurve_CR H hH (ht j) (hu j) (hCR j))
      (tangentCurve v) hlim
    have hHs : ContDiff ℝ ∞ (fun x : E => H (s,x)) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      exact (hH (s,x) hs).comp x (contDiffAt_const.prodMk contDiffAt_id)
    exact CR_contDiff_succ (fun x => H (s,x)) hHs v hv1 hW.fst hW.snd hCRv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

theorem field_C0_smooth_closure (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (v : ℂ → E) (hv : TendstoLocallyUniformly u v atTop) :
    ContDiff ℝ ∞ v ∧ (∀ z, fderiv ℝ v z Complex.I=H (s,v z) (fderiv ℝ v z 1)) ∧
      TendstoLocallyUniformly (fun j => fderiv ℝ (u j)) (fderiv ℝ v) atTop := by
  obtain ⟨_,hDv⟩ := field_C0_C1_closure H hH hHF t ht hts u hu hCR v hv
  refine ⟨?_,field_C1_CR_limit H hH t ht hts u hCR v hv hDv,hDv⟩
  rw [contDiff_infty]
  intro m
  exact field_C0_contDiff_nat m E H hH hHF t ht hts u hu hCR v hv

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

open scoped ContDiff Topology
open Set Filter Function

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem tangentCurveDir_smooth [FiniteDimensional ℂ E] [CompleteSpace E]
    (a : ℂ) {u : ℂ → E} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (tangentCurveDir a u) :=
  hu.prodMk ((hu.fderiv_right (by simp)).clm_apply contDiff_const)

theorem tangentCurveDir_fderiv {u : ℂ → E} (hu : ContDiff ℝ ∞ u) (a z b : ℂ) :
    fderiv ℝ (tangentCurveDir a u) z b=(fderiv ℝ u z b,fderiv ℝ (fderiv ℝ u) z b a) := by
  have hDu : Differentiable ℝ (fun w => fderiv ℝ u w a) :=
    ((hu.fderiv_right (by simp : (∞:WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).differentiable (by simp)
  have hh := (((hu.differentiable (by simp)) z).hasFDerivAt.prodMk (hDu z).hasFDerivAt).fderiv
  change fderiv ℝ (fun z => (u z,fderiv ℝ u z a)) z b=_
  rw [hh]
  simp only [ContinuousLinearMap.prod_apply,fderiv_directional hu]

theorem tangentCurveDir_CR (a : ℂ) (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) {u : ℂ → E} (hu : ContDiff ℝ ∞ u)
    (hCR : ∀ z, fderiv ℝ u z Complex.I=H (t,u z) (fderiv ℝ u z 1)) :
    ∀ z, fderiv ℝ (tangentCurveDir a u) z Complex.I=
      tangentField H (t,tangentCurveDir a u z) (fderiv ℝ (tangentCurveDir a u) z 1) := by
  intro z
  let B : ℂ → E →L[ℝ] E := fun w => H (t,u w)
  let DB : ℂ →L[ℝ] (E →L[ℝ] E) := (fderiv ℝ H (t,u z)).comp
    ((0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ u z))
  have hB : HasFDerivAt B DB z :=
    ((hH (t,u z) ht).differentiableAt (by simp)).hasFDerivAt.comp z
      ((hasFDerivAt_const t z).prodMk ((hu.differentiable (by simp)) z).hasFDerivAt)
  have hDu : Differentiable ℝ (fun w => fderiv ℝ u w 1) :=
    ((hu.fderiv_right (by simp : (∞:WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).differentiable (by simp)
  have hR := (hB.clm_apply (hDu z).hasFDerivAt).fderiv
  have he : (fun w => fderiv ℝ u w Complex.I)=(fun w => B w (fderiv ℝ u w 1)) := funext hCR
  have hd := congrArg (fun f : ℂ → E => fderiv ℝ f z a) he
  rw [fderiv_directional hu,hR] at hd
  have hs := (hu.contDiffAt (x := z)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [tangentCurveDir_fderiv hu,tangentCurveDir_fderiv hu]
  change (fderiv ℝ u z Complex.I,fderiv ℝ (fderiv ℝ u) z Complex.I a)=
    (H (t,u z) (fderiv ℝ u z 1),
      fderiv ℝ H (t,u z) (0,fderiv ℝ u z a) (fderiv ℝ u z 1)+
        H (t,u z) (fderiv ℝ (fderiv ℝ u) z 1 a))
  rw [hCR z,hs Complex.I a,hs 1 a]
  congr 1
  simpa [B,DB,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    fderiv_directional hu,add_comm] using hd

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity.FramedCR
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

theorem directional_second_convergence (a : ℂ) (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (v : ℂ → E) (hv : TendstoLocallyUniformly u v atTop) :
    TendstoLocallyUniformly (fun j => fderiv ℝ (fun z => fderiv ℝ (u j) z a))
      (fderiv ℝ (fun z => fderiv ℝ v z a)) atTop := by
  obtain ⟨hvs,_,hDv⟩ := field_C0_smooth_closure H hH hHF t ht hts u hu hCR v hv
  have hlim : TendstoLocallyUniformly (fun j => tangentCurveDir a (u j))
      (tangentCurveDir a v) atTop :=
    hv.prodMk ((ContinuousLinearMap.apply ℝ E a).uniformContinuous.comp_tendstoLocallyUniformly hDv)
  obtain ⟨_,_,hDW⟩ := field_C0_smooth_closure (tangentField H)
    (tangentField_smooth H hH) (tangentField_hasFrame H hH hHF) t ht hts
    (fun j => tangentCurveDir a (u j)) (fun j => tangentCurveDir_smooth a (hu j))
    (fun j => tangentCurveDir_CR a H hH (ht j) (hu j) (hCR j)) (tangentCurveDir a v) hlim
  let P : (ℂ →L[ℝ] E × E) →L[ℝ] (ℂ →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ ℂ (E × E) E) (ContinuousLinearMap.snd ℝ E E)
  have he (w : ℂ → E) (hw : ContDiff ℝ ∞ w) (z : ℂ) :
      P (fderiv ℝ (tangentCurveDir a w) z)=fderiv ℝ (fun z => fderiv ℝ w z a) z := by
    ext b
    simp only [P,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_apply,
      tangentCurveDir_fderiv hw,fderiv_directional hw]
    rfl
  simpa only [Function.comp_def,he _ hvs,he _ (hu _)] using
    P.uniformContinuous.comp_tendstoLocallyUniformly hDW

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem standardCurl_smooth [FiniteDimensional ℂ E] [CompleteSpace E]
    {u : ℂ → E} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (standardCurl u) :=
  ((hu.fderiv_right (by simp)).clm_apply contDiff_const).sub
    (((hu.fderiv_right (by simp)).clm_apply contDiff_const).const_smul Complex.I)

theorem standardCurl_convergence (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (v : ℂ → E) (hv : TendstoLocallyUniformly u v atTop) :
    TendstoLocallyUniformly (fun j => standardCurl (u j)) (standardCurl v) atTop ∧
    TendstoLocallyUniformly (fun j => fderiv ℝ (standardCurl (u j)))
      (fderiv ℝ (standardCurl v)) atTop := by
  obtain ⟨hvs,_,hDv⟩ := field_C0_smooth_closure H hH hHF t ht hts u hu hCR v hv
  refine ⟨(curlLinear (E := E)).uniformContinuous.comp_tendstoLocallyUniformly hDv,?_⟩
  have hI := directional_second_convergence Complex.I H hH hHF t ht hts u hu hCR v hv
  have h1 := directional_second_convergence 1 H hH hHF t ht hts u hu hCR v hv
  let M : E →L[ℝ] E := (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  let L : ((ℂ →L[ℝ] E) × (ℂ →L[ℝ] E)) →L[ℝ] (ℂ →L[ℝ] E) :=
    ContinuousLinearMap.fst ℝ _ _-
      ((ContinuousLinearMap.compL ℝ ℂ E E) M).comp (ContinuousLinearMap.snd ℝ _ _)
  have he (w : ℂ → E) (hw : ContDiff ℝ ∞ w) (z : ℂ) :
      L (fderiv ℝ (fun z => fderiv ℝ w z Complex.I) z,
        fderiv ℝ (fun z => fderiv ℝ w z 1) z)=fderiv ℝ (standardCurl w) z := by
    have hi := (((hw.fderiv_right (by simp : (∞:WithTop ℕ∞)+1 ≤ ∞)).clm_apply
      (contDiff_const (c := Complex.I))).differentiable (by simp) z).hasFDerivAt
    have h1 := (((hw.fderiv_right (by simp : (∞:WithTop ℕ∞)+1 ≤ ∞)).clm_apply
      (contDiff_const (c := (1:ℂ)))).differentiable (by simp) z).hasFDerivAt
    exact (hi.sub (M.hasFDerivAt.comp z h1)).fderiv.symm
  simpa only [Function.comp_def,he _ hvs,he _ (hu _)] using
    L.uniformContinuous.comp_tendstoLocallyUniformly (hI.prodMk h1)

end HigherDimensionalBallPacking.Rigidity.FramedCR

 

 

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem density_fderiv_zero_exterior (R : ℝ) (f : ℂ → E)
    (hf : ∀ z, R < ‖z‖ → f z=0) (z : ℂ) (hz : R < ‖z‖) :
    fderiv ℝ f z=0 := by
  apply fderiv_of_notMem_tsupport
  intro hh
  have h := density_tsupport_subset R f hf hh
  exact (not_le_of_gt hz) (by simpa only [Metric.mem_closedBall,dist_zero_right] using h)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem density_locally_uniform_to_uniform [NormedSpace ℝ E] [CompleteSpace E]
    (R : ℝ) (f : ℕ → ℂ → E) (g : ℂ → E)
    (hfs : ∀ j z, R < ‖z‖ → f j z=0) (hgs : ∀ z, R < ‖z‖ → g z=0)
    (h : TendstoLocallyUniformly f g atTop) : TendstoUniformly f g atTop := by
  have hc := tendstoLocallyUniformly_iff_forall_isCompact.mp h
    (Metric.closedBall (0:ℂ) R) (isCompact_closedBall _ _)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hc ε hε] with j hj z
  by_cases hz : ‖z‖ ≤ R
  · exact hj z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
  · rw [hfs j z (lt_of_not_ge hz),hgs z (lt_of_not_ge hz),dist_self]
    exact hε

theorem smoothCompactDensity_tendsto (R : ℝ) (f : ℕ → ℂ → E)
    (hfs : ∀ j, ContDiff ℝ ∞ (f j)) (hfc : ∀ j z, R < ‖z‖ → f j z=0)
    (g : ℂ → E) (hgs : ContDiff ℝ ∞ g) (hgc : ∀ z, R < ‖z‖ → g z=0)
    (h : TendstoLocallyUniformly f g atTop)
    (hD : TendstoLocallyUniformly (fun j => fderiv ℝ (f j)) (fderiv ℝ g) atTop) :
    Tendsto (fun j => smoothCompactDensity R (f j) (hfs j) (hfc j)) atTop
      (𝓝 (smoothCompactDensity R g hgs hgc)) := by
  have h0 := density_locally_uniform_to_uniform R f g hfc hgc h
  have h1 := density_locally_uniform_to_uniform R (fun j => fderiv ℝ (f j)) (fderiv ℝ g)
    (fun j => density_fderiv_zero_exterior R (f j) (hfc j))
    (density_fderiv_zero_exterior R g hgc) hD
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδs⟩ := holder_third_small_sup (K := ℂ) (E := E) 1 ε (by norm_num) hε
  filter_upwards [Metric.tendstoUniformly_iff.mp h0 δ hδ,
    Metric.tendstoUniformly_iff.mp h1 1 (by norm_num)] with j hj hjD
  let d : HolderSpace ℂ E ((1:ℝ)/3) := (smoothCompactDensity R (f j) (hfs j) (hfc j)).val-
    (smoothCompactDensity R g hgs hgc).val
  have hd (z : ℂ) : holderValue ((1:ℝ)/3) d z=f j z-g z := rfl
  have hdb (z : ℂ) : ‖fderiv ℝ (fun x => f j x-g x) z‖ ≤ 1 := by
    change ‖fderiv ℝ (f j-g) z‖ ≤ 1
    rw [fderiv_sub ((hfs j).differentiable (by simp) z) (hgs.differentiable (by simp) z)]
    have hb : ‖fderiv ℝ (f j) z-fderiv ℝ g z‖ < 1 := by
      simpa only [dist_eq_norm,norm_sub_rev] using hjD z
    exact hb.le
  have hl : LipschitzWith 1 (fun x => f j x-g x) :=
    lipschitzWith_of_nnnorm_fderiv_le ((hfs j).differentiable (by simp) |>.sub
      (hgs.differentiable (by simp))) (fun z => hdb z)
  have hdn : ‖d‖ < ε := hδs d
    (fun z => by simpa only [hd,dist_eq_norm,norm_sub_rev] using (hj z).le)
    (fun x y => by simpa only [hd,dist_eq_norm,NNReal.coe_one,one_mul] using hl.dist_le_mul x y)
  rw [Subtype.dist_eq,dist_eq_norm]
  exact hdn

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function
section
open HigherDimensionalBallPacking.Rigidity
open FramedCR

theorem affineHolderModuli_isCompact_oai (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) (R : ℝ)
    (hR : ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u →
      ∀ z, R < ‖z‖ → standardCurl u z=0) :
    IsCompact (affineHolderModuli J p q R) := by
  apply IsSeqCompact.isCompact
  intro U hU
  choose u hu he using fun j => (hU j).2
  obtain ⟨φ,hφ,τ,hτ,hφt,v,hφv,hv⟩ := homotopy_affine_curve_compactness
    n hn J hJs hJ hc hs p q hpq (fun j => (U j).1) (fun j => (hU j).1) u hu
  have hCR (j : ℕ) (z : ℂ) : fderiv ℝ (u (φ j)) z Complex.I=
      lineHomotopy J (U (φ j)).1 (u (φ j) z) (fderiv ℝ (u (φ j)) z 1) := by
    simpa only [mul_one] using (hu (φ j)).2.1 z |>.2 (1:ℂ)
  have hlim := standardCurl_convergence
    (fun y : ℝ × Phase n => lineHomotopy J y.1 y.2)
    (fun y hy => lineHomotopy_contDiffAt hJs hJ hy)
    (fun y hy => compatible_standard_frame (lineHomotopy_compatible hJ hy y.2))
    (fun j => (U (φ j)).1) (fun j => (hU (φ j)).1) hφt
    (fun j => u (φ j)) (fun j => (hu (φ j)).1) hCR v hφv
  let G : CompactHolderSpace (Phase n) R :=
    smoothCompactDensity R (standardCurl v) (standardCurl_smooth hv.1) (hR τ hτ v hv)
  have hG : Tendsto (fun j => smoothCompactDensity R (standardCurl (u (φ j)))
      (standardCurl_smooth (hu (φ j)).1) (hR _ (hU (φ j)).1 _ (hu (φ j)))) atTop (𝓝 G) :=
    smoothCompactDensity_tendsto R (fun j => standardCurl (u (φ j)))
      (fun j => standardCurl_smooth (hu (φ j)).1)
      (fun j => hR _ (hU (φ j)).1 _ (hu (φ j)))
      (standardCurl v) (standardCurl_smooth hv.1) (hR τ hτ v hv) hlim.1 hlim.2
  have heG (j : ℕ) : smoothCompactDensity R (standardCurl (u (φ j)))
      (standardCurl_smooth (hu (φ j)).1) (hR _ (hU (φ j)).1 _ (hu (φ j)))=(U (φ j)).2 := by
    apply Subtype.ext
    apply holderValue_injective ((1:ℝ)/3)
    apply DFunLike.ext
    intro z
    exact (he (φ j) z).symm
  simp only [heG] at hG
  refine ⟨(τ,G),⟨hτ,v,hv,fun _ => rfl⟩,φ,hφ,?_⟩
  exact hφt.prodMk_nhds hG

end

 

 

 

open scoped ContDiff Topology
open Set Filter Function








open scoped ContDiff Topology
open Set Filter Function

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.affineHolderModuli_isCompact_oai := @OAI.HigherDimensionalBallPacking.Rigidity.affineHolderModuli_isCompact_oai
