-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.densityResidual_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:02:02.899442+00:00
-- url     : https://prove2.me/submissions/0df969e0-f7f3-48d4-b459-f1a76aa303c1

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp005

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

lemma markedCRInverse_rightInverse (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    fderiv ℝ (markedCRInverse R u) x Complex.I -
      Complex.I • fderiv ℝ (markedCRInverse R u) x 1 = compactHolderValue R u x := by
  have hd := c1Holder_hasFDerivAt ((1:ℝ)/3) (compactCRInverse R u) x
  have ha := (hasFDerivAt_id (𝕜 := ℝ) x).smul_const
    (compactCRInverseValue R u 1-compactCRInverseValue R u 0)
  have ht := (hd.sub_const (compactCRInverseValue R u 0)).sub ha
  change HasFDerivAt (markedCRInverse R u) _ x at ht
  rw [ht.fderiv]
  simp only [sub_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,one_smul,smul_sub]
  have hh := compactCRInverse_rightInverse R u x
  simp only [compactCRInverseValue,c1Holder_fderiv] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  abel

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_HolderCalculus
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

open scoped ContDiff Topology
open Set Function Filter

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma markedCRInverse_differentiable (R : ℝ) (g : CompactHolderSpace E R) :
    Differentiable ℝ (markedCRInverse R g) := by
  exact (((compactCRInverse_contDiff R g).differentiable (by norm_num)).sub_const _).sub
    (differentiable_id.smul_const _)

end HigherDimensionalBallPacking.Rigidity

 

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_NonlinearCR
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



namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [CompleteSpace E]

theorem c1HolderAffineCurve_hasFDerivAt (α : ℝ) (c : E) (A : ℂ →L[ℝ] E)
    (u : C1HolderSpace E α) (z : ℂ) :
    HasFDerivAt (c1HolderAffineCurve α c A u) (A+holderValue α (c1HolderDeriv α u) z) z :=
  (A.hasFDerivAt.const_add c).add (c1Holder_hasFDerivAt α u z)

@[simp] theorem c1HolderAffineCurve_fderiv (α : ℝ) (c : E) (A : ℂ →L[ℝ] E)
    (u : C1HolderSpace E α) (z : ℂ) :
    fderiv ℝ (c1HolderAffineCurve α c A u) z = A+holderValue α (c1HolderDeriv α u) z :=
  (c1HolderAffineCurve_hasFDerivAt α c A u z).fderiv

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityBounds
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
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
open FramedCR


theorem densityCurve_contDiff {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) : ContDiff ℝ 1 (densityCurve p q R g) := by
  unfold densityCurve markedCRInverse
  exact (contDiff_const.add (contDiff_id.smul contDiff_const)).add
    (((compactCRInverse_contDiff R g).sub contDiff_const).sub
      (contDiff_id.smul contDiff_const))

theorem densityCurve_curl {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    standardCurl (densityCurve p q R g) z=compactHolderValue R g z := by
  have hd := (hasFDerivAt_const (𝕜 := ℝ) p z).add
    ((hasFDerivAt_id (𝕜 := ℝ) z).smul_const (q-p))
  have hg := (markedCRInverse_differentiable R g z).hasFDerivAt
  have h := hd.add hg
  change HasFDerivAt (densityCurve p q R g) _ z at h
  unfold standardCurl
  rw [h.fderiv]
  simp only [add_apply,zero_add,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,one_smul,smul_add]
  have he := markedCRInverse_rightInverse R g z
  linear_combination he

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityResidual
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
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity








open scoped ContDiff Topology
open Set Filter Function
open HigherDimensionalBallPacking.Rigidity

 theorem timeDensityProfile_value {n : ℕ} (p q : Phase n) (R : ℝ)
    (y : ℝ × CompactHolderSpace (Phase n) R) (z : ℂ) :
    (timeDensityProfile p q R y).1.1+(timeDensityProfile p q R y).1.2 z+
      holderValue ((1:ℝ)/3) (timeDensityProfile p q R y).2 z=(y.1,densityCurve p q R y.2 z) := by
  apply Prod.ext
  · change y.1+0+(holderValue ((1:ℝ)/3) (holderLinearPost ((1:ℝ)/3)
      (ContinuousLinearMap.inr ℝ ℝ (Phase n))
      (c1HolderValue ((1:ℝ)/3) (compactCRInverse R y.2))) z).1=y.1
    rw [holderLinearPost_apply]
    simp
  · change p-compactCRInverseValue R y.2 0+z • densitySlope p q R y.2+
      compactCRInverseValue R y.2 z=p+z • (q-p)+markedCRInverse R y.2 z
    simp only [densitySlope,markedCRInverse,smul_sub]
    abel

 theorem densityCoefficient_value {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) R) (z : ℂ) :
    holderValue ((1:ℝ)/3) (densityCoefficient p q R A hA hc y) z=A (y.1,densityCurve p q R y.2 z) := by
  rw [densityCoefficient,holderAffineFamily_apply,timeDensityProfile_value]

 theorem densityCurve_eq_profile {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) :
    densityCurve p q R g=c1HolderAffineCurve ((1:ℝ)/3)
      (p-compactCRInverseValue R g 0) (densityLinearSlope p q R g) (compactCRInverse R g) := by
  funext z
  change p+z • (q-p)+(compactCRInverseValue R g z-compactCRInverseValue R g 0-
    z • (compactCRInverseValue R g 1-compactCRInverseValue R g 0))=
    p-compactCRInverseValue R g 0+z • densitySlope p q R g+compactCRInverseValue R g z
  simp only [densitySlope,smul_sub]
  abel

 theorem densityJet_value {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    holderValue ((1:ℝ)/3) (densityJet p q R g) z=fderiv ℝ (densityCurve p q R g) z := by
  rw [densityCurve_eq_profile,c1HolderAffineCurve_fderiv]
  change holderValue ((1:ℝ)/3) (holderConst ((1:ℝ)/3) (densityLinearSlope p q R g)) z+
    holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse R g)) z=_
  rw [holderConst_apply]

 theorem densityResidual_value {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) R) (z : ℂ) :
    holderValue ((1:ℝ)/3) (densityResidual p q R A hA hc y) z=
      fderiv ℝ (densityCurve p q R y.2) z Complex.I-
        (standardJ n+A (y.1,densityCurve p q R y.2 z))
          (fderiv ℝ (densityCurve p q R y.2) z 1) := by
  change compactHolderValue R y.2 z-
    holderValue ((1:ℝ)/3) (holderCLM ((1:ℝ)/3) (densityCoefficient p q R A hA hc y)
      (holderJetEval ((1:ℝ)/3) 1 (densityJet p q R y.2))) z=_
  rw [holderCLM_apply,densityCoefficient_value,holderJetEval_apply,densityJet_value,
    ←densityCurve_curl p q R y.2 z]
  change (fderiv ℝ (densityCurve p q R y.2) z Complex.I-standardJ n (fderiv ℝ (densityCurve p q R y.2) z 1))-A _ _=
    fderiv ℝ (densityCurve p q R y.2) z Complex.I-(standardJ n (fderiv ℝ (densityCurve p q R y.2) z 1)+A _ _)
  abel

 theorem pseudoHolomorphicAt_of_scalarCR {n : ℕ} {J : Phase n → End n}
    {u : ℂ → Phase n} {z : ℂ} (hu : DifferentiableAt ℝ u z)
    (hJ : ∀ v, J (u z) (J (u z) v)=-v)
    (hCR : fderiv ℝ u z Complex.I=J (u z) (fderiv ℝ u z 1)) :
    PseudoHolomorphicAt J u z := by
  refine ⟨hu,?_⟩
  intro w
  have hw : w=w.re • (1:ℂ)+w.im • Complex.I := by apply Complex.ext <;> simp
  have hiw : Complex.I*w=(-w.im) • (1:ℂ)+w.re • Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  conv_rhs => rw [hw]
  rw [hiw]
  simp only [map_add,map_smul,hCR,hJ]
  rw [smul_neg,neg_smul]
  abel

 theorem densityResidual_zero_iff_oai {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (J : Phase n → End n) (hJ : ∀ x, Compatible (J x))
    (he : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, A (t,x)=lineHomotopy J t x-standardJ n)
    (y : ℝ × CompactHolderSpace (Phase n) R) (hy : y.1 ∈ Icc (0:ℝ) 1) :
    densityResidual p q R A hA hc y=0 ↔
      ∀ z, PseudoHolomorphicAt (lineHomotopy J y.1) (densityCurve p q R y.2) z := by
  have hv (z : ℂ) : holderValue ((1:ℝ)/3) (densityResidual p q R A hA hc y) z=
      fderiv ℝ (densityCurve p q R y.2) z Complex.I-
        lineHomotopy J y.1 (densityCurve p q R y.2 z) (fderiv ℝ (densityCurve p q R y.2) z 1) := by
    rw [densityResidual_value,he _ hy]
    congr 2
    abel
  constructor
  · intro h z
    apply pseudoHolomorphicAt_of_scalarCR ((densityCurve_contDiff p q R y.2).differentiable (by simp) z)
      (lineHomotopy_compatible hJ hy _).1
    apply sub_eq_zero.mp
    rw [←hv,h]
    rfl
  · intro h
    apply holderValue_injective ((1:ℝ)/3)
    apply DFunLike.ext
    intro z
    rw [hv]
    have hz := (h z).2 (1:ℂ)
    change _-_=(0 : Phase n)
    simpa only [mul_one] using sub_eq_zero.mpr hz

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.densityResidual_zero_iff_oai := @OAI.HigherDimensionalBallPacking.Rigidity.densityResidual_zero_iff_oai
