-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.responseCoefficient_invertible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:18:39.56025+00:00
-- url     : https://prove2.me/submissions/0dca1b57-da81-4d32-a6fb-69ed8db6318c

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp007
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_cutoffFrozen_invertible

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

theorem compatible_standardJ (n : ℕ) : Compatible (standardJ n) :=
  ⟨standardJ_sq n, standardForm_J_J, fun _ hv => standardForm_J_pos hv⟩

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

theorem interpolateJ_standard {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    interpolateJ (standardJ n) t = standardJ n := by
  have ha : 0 < 1+t := by linarith [ht.1]
  have hb : 0 ≤ 1-t := by linarith [ht.2]
  obtain ⟨e,he⟩ := cayleyP_invertible (compatible_standardJ n) ha hb
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator (standardJ n) (1+t) (1-t) ((e : End n) x)) =
    standardJ n ((e : End n) x)
  rw [he,cayleyOperator_on_denominator ⟨e,he⟩]
  congr 1
  simp only [cayleyP_apply,relativeOperator_apply,standardJ_sq,neg_neg]
  module

theorem lineHomotopy_compatible {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x : Phase n) :
    Compatible (lineHomotopy J t x) := compatible_interpolateJ (hJ x) ht

@[simp] theorem lineHomotopy_zero {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) (x : Phase n) : lineHomotopy J 0 x = standardJ n :=
  interpolateJ_zero (hJ x)

@[simp] theorem lineHomotopy_one {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) (x : Phase n) : lineHomotopy J 1 x = J x :=
  interpolateJ_one (hJ x)

theorem lineHomotopy_support {n : ℕ} (J : Phase n → End n)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    tsupport (fun x => lineHomotopy J t x - standardJ n) ⊆
      tsupport (fun x => J x - standardJ n) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have hzero := image_eq_zero_of_notMem_tsupport hn
  have hJx : J x = standardJ n := sub_eq_zero.mp hzero
  apply hx
  change interpolateJ (J x) t - standardJ n = 0
  rw [hJx,interpolateJ_standard ht,sub_self]

theorem lineHomotopy_compact {n : ℕ} {J : Phase n → End n}
    (hJc : HasCompactSupport (fun x => J x - standardJ n))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasCompactSupport (fun x => lineHomotopy J t x - standardJ n) :=
  hJc.of_isClosed_subset (isClosed_tsupport _) (lineHomotopy_support J ht)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



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








open scoped Topology ContDiff
open Set Filter Function







open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function







open scoped Topology
open Set Filter Function







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







open scoped ContDiff Topology
open Set Filter Function







open scoped ContDiff Topology
open Set Filter Function
open HigherDimensionalBallPacking.Rigidity

end HigherDimensionalBallPacking.Rigidity

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

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityMaps
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

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem responseCoefficient_value {n : ℕ} (b B : ContDiffBump (0:ℂ)) (hbB : b.rOut≤B.rIn)
    (p q : Phase n) (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut) (z : ℂ) :
    holderValue ((1:ℝ)/3) (responseCoefficient b B A hA hc (responseCoords B p q b.rOut y)) z=
      b z • A (y.1,densityCurve p q b.rOut y.2 z) := by
  change b z • holderValue ((1:ℝ)/3) (holderPost ((1:ℝ)/3) (by norm_num) A hA hc _) z=_
  rw [holderPost_apply]
  by_cases hz : b z=0
  · rw [hz]
    ext v
    simp
  have hzz : ‖z‖≤b.rOut := by
    by_contra hn
    exact hz (b.zero_of_le_dist (by simpa using (le_of_not_ge hn)))
  have hB : B z=1 := B.one_of_mem_closedBall (by simpa using hzz.trans hbB)
  congr 2
  rw [responseProfile,map_add,BoundedContinuousFunction.add_apply,holderConstantCLM_value,
    holderLinearPost_apply, map_add, BoundedContinuousFunction.add_apply, holderCutoffAffine_apply]
  change (y.1,0)+(ContinuousLinearMap.inr ℝ ℝ (Phase n))
    (B z • ((p-compactCRInverseValue b.rOut y.2 0)+affineSlope (densitySlope p q b.rOut y.2) z)+
      B z • compactCRInverseValue b.rOut y.2 z)=_
  rw [hB,one_smul,one_smul]
  apply Prod.ext
  · simp
  · simp only [Prod.snd_add, ContinuousLinearMap.inr_apply, zero_add]
    rw [densityCurve_eq_profile]
    rfl

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityExistence
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





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem responseCoefficient_uncut {n : ℕ} (b B : ContDiffBump (0:ℂ)) (hbB : b.rOut≤B.rIn)
    (p q : Phase n) (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut)
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → A (y.1,densityCurve p q b.rOut y.2 z)=0) (z : ℂ) :
    holderValue ((1:ℝ)/3) (responseCoefficient b B A hA hc (responseCoords B p q b.rOut y)) z=
      A (y.1,densityCurve p q b.rOut y.2 z) := by
  rw [responseCoefficient_value b B hbB p q A hA hc y z]
  by_cases hz : ‖z‖≤b.rIn
  · rw [b.one_of_mem_closedBall (by simpa using hz),one_smul]
  · rw [hs z (lt_of_not_ge hz)]
    ext v
    simp

 theorem responseCoefficient_invertible_oai {n : ℕ} (b B : ContDiffBump (0:ℂ)) (hbB : b.rOut≤B.rIn)
    (p q : Phase n) (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (he : ∀ t∈Icc (0:ℝ) 1, ∀ x, A (t,x)=lineHomotopy J t x-standardJ n)
    (y : ℝ × CompactHolderSpace (Phase n) b.rOut) (hy : y.1∈Icc (0:ℝ) 1)
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → A (y.1,densityCurve p q b.rOut y.2 z)=0) :
    (cutoffFrozen b (responseCoefficient b B A hA hAc (responseCoords B p q b.rOut y))).IsInvertible := by
  have hts : ContDiff ℝ ∞ (fun x => lineHomotopy J y.1 x-standardJ n) := by
    apply ContDiff.sub _ contDiff_const
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (lineHomotopy_contDiffAt hJs hJ (y := (y.1,x)) hy).comp x (contDiffAt_const.prodMk contDiffAt_id)
  let H := c1HolderAffineCompose ((1:ℝ)/3) (by norm_num) (by norm_num)
    (fun x => lineHomotopy J y.1 x-standardJ n) hts (lineHomotopy_compact hc hy)
    (p-compactCRInverseValue b.rOut y.2 0) (affineSlope (densitySlope p q b.rOut y.2)) (compactCRInverse b.rOut y.2)
  have hH (z : ℂ) : holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) H) z=
      A (y.1,densityCurve p q b.rOut y.2 z) := by
    rw [he _ hy,densityCurve_eq_profile]
    exact c1HolderAffineCompose_value _ _ _ _ _ _ _ _ _ z
  have hHeq : c1HolderValue ((1:ℝ)/3) H=responseCoefficient b B A hA hAc (responseCoords B p q b.rOut y) := by
    apply holderValue_injective
    apply BoundedContinuousFunction.ext
    intro z
    rw [hH,responseCoefficient_uncut b B hbB p q A hA hAc y hs]
  rw [←hHeq]
  apply cutoffFrozen_invertible b H
  · intro z hz
    rw [hH,hs z hz]
  · intro z
    rw [hH,he _ hy,add_comm,sub_add_cancel]
    exact lineHomotopy_compatible hJ hy _

end HigherDimensionalBallPacking.Rigidity

 

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.responseCoefficient_invertible_oai := @OAI.HigherDimensionalBallPacking.Rigidity.responseCoefficient_invertible_oai
