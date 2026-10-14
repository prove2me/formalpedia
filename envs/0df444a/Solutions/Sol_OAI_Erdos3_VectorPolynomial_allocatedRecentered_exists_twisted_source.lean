-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedRecentered_exists_twisted_source
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-11T23:47:11.374951+00:00
-- url     : https://prove2.me/submissions/1f5075bf-e6bc-428a-ad0f-2204d9e04243

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B162
import Definitions.Def_OAIErdos3B164

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
namespace OAI

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

open scoped NNReal BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

end Erdos3

end

section

namespace Erdos3
open scoped Classical BigOperators NNReal

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem siteFactorTensor_identity {D S U : Type*} [Fintype D] [DecidableEq D] [Fintype S]
    {T : D → Type*} [∀ d, Fintype (T d)]
    (c : ∀ d, T d → ℂ) (f : ∀ d, T d → S → U → ℂ) (v : S → D → U) :
    (∏ d, ∑ t, c d t * ∏ s, f d t s (v s d)) =
      ∑ t : ∀ d, T d, (∏ d, c d (t d)) * ∏ s, ∏ d, f d (t d) s (v s d) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_comm]

theorem siteFactorTensor_coefficient_sum {D : Type*} [Fintype D] [DecidableEq D]
    {T : D → Type*} [∀ d, Fintype (T d)] (c : ∀ d, T d → ℂ) :
    (∑ t : ∀ d, T d, ‖∏ d, c d (t d)‖) = ∏ d, ∑ t, ‖c d t‖ := by
  simp_rw [norm_prod]
  exact (Fintype.prod_sum (fun d t => ‖c d t‖)).symm

theorem siteFactorTensor_coefficient_bound {D : Type*} [Fintype D] [DecidableEq D]
    {T : D → Type*} [∀ d, Fintype (T d)] (c : ∀ d, T d → ℂ) (C : D → ℝ)
    (hc : ∀ d, (∑ t, ‖c d t‖) ≤ C d) :
    (∑ t : ∀ d, T d, ‖∏ d, c d (t d)‖) ≤ ∏ d, C d := by
  rw [siteFactorTensor_coefficient_sum]
  exact Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (fun d _ => hc d)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {S T U D : Type*} [Fintype S] [Fintype T]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped Matrix ENNReal

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeImage_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L m).toAddSubgroup.index = L.toAddSubgroup.index := by
  have hk : (integerResidueMap I m).toAddMonoidHom.ker ≤ L.toAddSubgroup := by
    change (LinearMap.ker (integerResidueMap I m)).toAddSubgroup ≤ L.toAddSubgroup
    rw [integerResidueMap_ker]
    exact hperiod
  have h := L.toAddSubgroup.index_map_eq (integerResidueMap_surjective I m) hk
  change (L.toAddSubgroup.map (integerResidueMap I m).toAddMonoidHom).index = _
  exact h

theorem residueLatticeImage_card_mul_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = m ^ Fintype.card I := by
  classical
  have h := (residueLatticeImage L m).toAddSubgroup.card_mul_index
  rw [residueLatticeImage_index L m hperiod] at h
  change Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = Nat.card (I → ZMod m) at h
  have heq : Nat.card (I → ZMod m) = m ^ Fintype.card I := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  exact h.trans heq

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeImage_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    L.toAddSubgroup.index ≤ m ^ Fintype.card I := by
  have h := residueLatticeImage_card_mul_index L m hperiod
  have hpos := Nat.card_pos (α := residueLatticeImage L m)
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitExpansionCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_weighted_pair_nonzero {I : Type*} {J : I → Type*}
    [Fintype I] [∀ i, Fintype (J i)] (c : I → ℂ) (d z : ∀ i, J i → ℂ)
    {delta C D : ℝ} (hdelta : 0 < delta) (hC : 0 < C) (hD : 0 < D)
    (hc : (∑ i, ‖c i‖) ≤ C) (hd : ∀ i, (∑ j, ‖d i j‖) ≤ D)
    (hsum : delta ≤ ‖∑ i, ∑ j, (c i * d i j) * z i j‖) :
    ∃ i j, c i ≠ 0 ∧ d i j ≠ 0 ∧ delta / (C * D) ≤ ‖z i j‖ := by
  classical
  let w := fun i j => if c i * d i j = 0 then 0 else z i j
  have he : ∀ i j, (c i * d i j) * w i j = (c i * d i j) * z i j := by
    intro i j
    dsimp only [w]
    split_ifs with h
    · simp only [h, zero_mul]
    · rfl
  obtain ⟨i, j, hj⟩ := exists_large_weighted_pair c d w hdelta hC hD hc hd
    (by simpa only [he] using hsum)
  have hn : c i * d i j ≠ 0 := by
    intro h
    have hpos := div_pos hdelta (mul_pos hC hD)
    simp only [w, h, ite_true, norm_zero] at hj
    exact (not_le_of_gt hpos) hj
  exact ⟨i, j, (mul_ne_zero_iff.mp hn).1, (mul_ne_zero_iff.mp hn).2,
    by simpa only [w, hn, ite_false] using hj⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.TranslatedMixtureL1
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] in
theorem pivotOutputDensity_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℝ) :
    pivotOutputDensity A B f v = inverseJacobian A * ∫ y, f (y, A.symm (v - B y)) := by
  exact integral_const_mul _ _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotJacobianBound
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotSliceProfile_zero_outside (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ} {R : ℝ}
    (hf : ∀ p, R < ‖p‖ → f p = 0) (v : I → ℝ) (y : J → ℝ) (hy : R < ‖y‖) :
    pivotSliceProfile A B f v y = 0 :=
  hf _ (hy.trans_le (norm_fst_le (y, A.symm (v - B y))))

theorem pivotSliceProfile_integrable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Continuous f) {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (v : I → ℝ) :
    Integrable (pivotSliceProfile A B f v) := by
  have hc : Continuous (pivotSliceProfile A B f v) := by
    unfold pivotSliceProfile
    fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : J → ℝ) R)
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  exact hy (pivotSliceProfile_zero_outside A B hsupport v y h)

omit [Fintype I] in
theorem pivotOutputDensity_slice_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℝ) :
    pivotOutputDensity A B f v = inverseJacobian A * ∫ y, pivotSliceProfile A B f v y :=
  pivotOutputDensity_formula A B f v

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] in
theorem coordinateMatrix_entry_le_norm (f : (J → ℝ) →L[ℝ] (I → ℝ)) (i : I) (j : J) :
    |(LinearMap.toMatrix' f.toLinearMap) i j| ≤ ‖f‖ := by
  rw [LinearMap.toMatrix'_apply]
  calc
    |f (Pi.single j 1) i| ≤ ‖f (Pi.single j 1)‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (f (Pi.single j 1)) i
    _ ≤ ‖f‖ * ‖(Pi.single j 1 : J → ℝ)‖ := f.le_opNorm (Pi.single j 1)
    _ = ‖f‖ := by rw [Pi.norm_single, norm_one, mul_one]

theorem inverseJacobian_le_norm_bound (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) {U : ℝ}
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ U) :
    inverseJacobian A ≤ (Fintype.card I).factorial * U ^ Fintype.card I := by
  have h := matrix_det_abs_le_uniform_bound
    (LinearMap.toMatrix' A.symm.toContinuousLinearMap.toLinearMap)
    (fun i j => (coordinateMatrix_entry_le_norm A.symm.toContinuousLinearMap i j).trans hA)
  rw [LinearMap.det_toMatrix'] at h
  exact h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PivotNormalizedMatrix
namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem normalizedIntegerPivot_entry (A : Matrix I I ℤ) (S P : I → ℝ) (i j : I) :
    normalizedIntegerPivot A S P i j = (A i j : ℝ) * S j / P i := by
  simp only [normalizedIntegerPivot, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.map_apply, Int.coe_castRingHom, div_eq_mul_inv]
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem normalizedPivotEquiv_coe (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedPivotEquiv A hA S P hS hP).toContinuousLinearMap =
      matrixSupCLM (normalizedIntegerPivot A S P) :=
  (matrixSupCLM_inverse_spec (normalizedIntegerPivot A S P)
    (normalizedIntegerPivot_det_ne_zero A hA S P hS hP)).1.choose_spec

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem smoothProductProfile_norm_le (I : Type*) [Fintype I] (x : I → ℝ) :
    ‖smoothProductProfile I x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (smoothProductProfile_range I x).1]
  exact (smoothProductProfile_range I x).2

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialPivotNormalization
namespace OAI

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

theorem normalizedPivotEquiv_inverse_eq {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (S P : I → ℝ)
    (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap =
      (matrixSupCLM (normalizedIntegerPivot A S P)).inverse := by
  rw [← normalizedPivotEquiv_coe A hA S P hS hP, ContinuousLinearMap.inverse_equiv]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PivotDensityCap
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotOutputDensity_abs_le (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ)
    {R H : ℝ} (hR : 0 ≤ R) (hsupport : ∀ p, R < ‖p‖ → f p = 0)
    (hbound : ∀ p, ‖f p‖ ≤ H) (v : I → ℝ) :
    |pivotOutputDensity A B f v| ≤ inverseJacobian A * H * (2 * R) ^ Fintype.card J := by
  have hi := integral_norm_le_box (pivotSliceProfile A B f v) hR
    (pivotSliceProfile_zero_outside A B hsupport v) (fun y _ => hbound _)
  have hb := (norm_integral_le_integral_norm (f := pivotSliceProfile A B f v)).trans hi
  rw [pivotOutputDensity_slice_formula, abs_mul, abs_of_pos (inverseJacobian_pos A)]
  have h := mul_le_mul_of_nonneg_left hb (inverseJacobian_pos A).le
  simpa only [Real.norm_eq_abs, mul_assoc] using h

theorem pivotOutputDensity_abs_le_uniform [DecidableEq I]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (f : (J → ℝ) × (I → ℝ) → ℝ) {R H U : ℝ} (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hbound : ∀ p, ‖f p‖ ≤ H)
    (hinv : ‖A.symm.toContinuousLinearMap‖ ≤ U) (v : I → ℝ) :
    |pivotOutputDensity A B f v| ≤
      ((Fintype.card I).factorial * U ^ Fintype.card I) * H * (2 * R) ^ Fintype.card J :=
  (pivotOutputDensity_abs_le A B f hR hsupport hbound v).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (inverseJacobian_le_norm_bound A hinv) hH) (by positivity))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {I J N : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]

theorem normalizedIntegerColumns_entry (B : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ)
    (i : I) (j : J) : normalizedIntegerColumns B T P i j = (P i)⁻¹ * B i j * T j := by
  simp [normalizedIntegerColumns, Matrix.diagonal_mul, Matrix.mul_diagonal]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

end Erdos3

end

section

namespace Erdos3

theorem normalizedIntegerColumns_entry_div {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) (i : I) (j : J) :
    normalizedIntegerColumns A T P i j = (A i j : ℝ) * T j / P i := by
  rw [normalizedIntegerColumns_entry]
  simp only [div_eq_mul_inv]
  ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem smoothSplitProfile_norm_le (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) : ‖smoothSplitProfile J I p‖ ≤ 1 := by
  rw [smoothSplitProfile_join]
  exact smoothProductProfile_norm_le _ _

theorem smoothSplitProfile_lipschitz (J I : Type*) [Fintype J] [Fintype I] :
    LipschitzWith ((Fintype.card J + Fintype.card I) * probabilityProfileLipschitz)
      (smoothSplitProfile J I) := by
  have hj : LipschitzWith 1 (fun p : (J → ℝ) × (I → ℝ) => Sum.elim p.1 p.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    have he : Sum.elim p.1 p.2 - Sum.elim q.1 q.2 = Sum.elim (p-q).1 (p-q).2 := by
      funext k
      cases k <;> rfl
    rw [he, sumElim_norm]
  have h := (smoothProductProfile_lipschitz (J ⊕ I)).comp hj
  simpa only [mul_one, Fintype.card_sum, Nat.cast_add, Function.comp_def,
    ← smoothSplitProfile_join] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

variable {I J R : Type*} [Fintype I] (s : I ↪ J)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarCubeMinorPolynomial
namespace OAI

section

namespace Erdos3

theorem scalarCubeMinorPolynomial_grid_eval {I J : Type*} [Fintype I] [DecidableEq I]
    {N L : ℕ} (e : J × Option I ≃ Fin N) (s : I → J) (x : J → IntegerScalarCubeBox I L) :
    MvPolynomial.eval (fun i => (scalarCubeGrid e x i : ℝ) / L) (scalarCubeMinorPolynomial e s) =
      normalizedScalarCubeMinor s x := by
  rw [scalarCubeMinorPolynomial, coordinateMatrixPolynomial_eval]
  let A := (scalarCubeDifferenceMatrix x).submatrix id s
  have hm : ((fun i j => (scalarCubeGrid e x (e (s j, some i)) : ℝ) / L) : Matrix I I ℝ) =
      (L : ℝ)⁻¹ • A.map (Int.castRingHom ℝ) := by
    ext i j
    simp [A, scalarCubeGrid, scalarCubeDifferenceMatrix, sampledColumnMatrix,
      Matrix.submatrix_apply, div_eq_mul_inv, mul_comm]
  have hcast : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) :=
    ((Int.castRingHom ℝ).map_det A).symm
  rw [hm, Matrix.det_smul, hcast, inv_pow]
  change ((L : ℝ) ^ Fintype.card I)⁻¹ * (A.det : ℝ) = (A.det : ℝ) / (L : ℝ) ^ Fintype.card I
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI

namespace Erdos3

theorem normalizedScalarCubePivot_det {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {L : ℕ}
    (s : I → J) (x : J → IntegerScalarCubeBox I L) :
    (normalizedScalarCubePivot s x).det = normalizedScalarCubeMinor s x := by
  let e := Fintype.equivFin (J × Option I)
  have h := scalarCubeMinorPolynomial_grid_eval e s x
  rw [scalarCubeMinorPolynomial, coordinateMatrixPolynomial_eval] at h
  change Matrix.det (fun i j => ((x (s j) (some i) : ℤ) : ℝ) / (L : ℝ)) = _
  simpa only [scalarCubeGrid, e.symm_apply_apply] using h

end Erdos3

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotOutputLipschitz
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotSliceProfile_output_bound (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (v w : I → ℝ) (y : J → ℝ) :
    ‖pivotSliceProfile A B f v y - pivotSliceProfile A B f w y‖ ≤
      K * ‖A.symm.toContinuousLinearMap‖ * ‖v - w‖ := by
  have h := hf.norm_sub_le (y, A.symm (v - B y)) (y, A.symm (w - B y))
  have heq : (y, A.symm (v - B y)) - (y, A.symm (w - B y)) =
      ((0 : J → ℝ), A.symm (v - w)) := by
    ext i <;> simp [← map_sub]
  rw [heq, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at h
  exact h.trans (by
    simpa only [ContinuousLinearEquiv.coe_coe, mul_assoc] using mul_le_mul_of_nonneg_left
      (A.symm.toContinuousLinearMap.le_opNorm (v - w)) K.coe_nonneg)

theorem pivotOutputDensity_output_bound (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {R : ℝ} (hR : 0 ≤ R)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (v w : I → ℝ) :
    |pivotOutputDensity A B f v - pivotOutputDensity A B f w| ≤
      (inverseJacobian A * (2 * R) ^ Fintype.card J * K *
        ‖A.symm.toContinuousLinearMap‖) * ‖v - w‖ := by
  have hi (u) := pivotSliceProfile_integrable A B hf.continuous hsupport u
  have hb := integral_norm_le_box
    (fun y => pivotSliceProfile A B f v y - pivotSliceProfile A B f w y) hR
    (fun y hy => by rw [pivotSliceProfile_zero_outside A B hsupport v y hy,
      pivotSliceProfile_zero_outside A B hsupport w y hy, sub_self])
    (fun y _ => pivotSliceProfile_output_bound A B hf v w y)
  rw [pivotOutputDensity_slice_formula, pivotOutputDensity_slice_formula,
    ← mul_sub, ← integral_sub (hi v) (hi w), abs_mul,
    abs_of_pos (inverseJacobian_pos A)]
  have hn := (norm_integral_le_integral_norm
    (f := fun y => pivotSliceProfile A B f v y - pivotSliceProfile A B f w y)).trans hb
  have hm := mul_le_mul_of_nonneg_left hn (inverseJacobian_pos A).le
  simpa only [Real.norm_eq_abs] using hm.trans_eq (by ring)

theorem pivotOutputDensity_output_bound_uniform [DecidableEq I]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {R U : ℝ} (hR : 0 ≤ R) (hsupport : ∀ p, R < ‖p‖ → f p = 0)
    (hinv : ‖A.symm.toContinuousLinearMap‖ ≤ U) (v w : I → ℝ) :
    |pivotOutputDensity A B f v - pivotOutputDensity A B f w| ≤
      ((Fintype.card I).factorial * U ^ Fintype.card I *
        (2 * R) ^ Fintype.card J * K * U) * ‖v - w‖ := by
  have hU : 0 ≤ U := (norm_nonneg _).trans hinv
  apply (pivotOutputDensity_output_bound A B hf hR hsupport v w).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (inverseJacobian_le_norm_bound A hinv) (by positivity))
      K.coe_nonneg)
    hinv (norm_nonneg _) (by positivity)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialStarCoordinates
namespace OAI

section

namespace Erdos3

theorem spatialStar_vertex {I R : Type*} [AddCommMonoid R] (v : (Unit ⊕ I) → R) (i : Unit ⊕ I) :
    spatialStar v i = v (.inl ()) + ∑ j ∈ spatialStarVertex i, v (.inr j) := by
  cases i with
  | inl i => cases i; simp [spatialStar, spatialStarVertex]
  | inr i => simp [spatialStar, spatialStarVertex]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI

namespace Erdos3

open scoped BigOperators Matrix Classical

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open scoped Matrix

theorem integerMatrix_fromCols_range {I J N : Type*} [Fintype J] [Fintype N]
    (B : Matrix I J ℤ) (C : Matrix I N ℤ) :
    (Matrix.fromCols B C).mulVecLin.range = B.mulVecLin.range ⊔ C.mulVecLin.range := by
  ext v
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨B *ᵥ (fun j => x (.inl j)), ⟨_, rfl⟩,
      C *ᵥ (fun n => x (.inr n)), ⟨_, rfl⟩, ?_⟩
    exact (Matrix.fromCols_mulVec B C x).symm.trans hx
  · rintro ⟨b, ⟨x, rfl⟩, c, ⟨y, rfl⟩, h⟩
    refine ⟨Sum.elim x y, ?_⟩
    change Matrix.fromCols B C *ᵥ Sum.elim x y = v
    rw [Matrix.fromCols_mulVec_sumElim]
    exact h

theorem pivotFullImage_split {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C : Matrix I N ℤ) :
    pivotFullImage A (Matrix.fromCols B C) = pivotFullImage A B ⊔ C.mulVecLin.range := by
  unfold pivotFullImage
  rw [integerMatrix_fromCols_range, sup_assoc]

end Erdos3

namespace Erdos3

open scoped Matrix Classical

end Erdos3

namespace Erdos3

open scoped Classical

theorem latticeStarMask_bound {I : Type*} (L : Submodule ℤ ((Unit ⊕ I) → ℤ)) (m : ℕ)
    {G : ℝ} (hindex : (L.toAddSubgroup.index : ℝ) ≤ G) (a : (Unit ⊕ I) → ZMod m) :
    ‖latticeStarMask L m a‖ ≤ G := by
  classical
  unfold latticeStarMask
  split_ifs
  · simpa using hindex
  · simpa using (Nat.cast_nonneg L.toAddSubgroup.index).trans hindex

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

end Erdos3

namespace Erdos3

open scoped NNReal Matrix

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueIntervalFactors
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueSiteIndicator_range {m : ℕ} (r : ZMod m) (u : ℤ) :
    0 ≤ residueSiteIndicator r u ∧ residueSiteIndicator r u ≤ 1 := by
  unfold residueSiteIndicator
  split_ifs <;> norm_num

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MaskedIntervalApproximation
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem maskedIntervalApprox_coefficient_sum {S : Type*} [Fintype S] [DecidableEq S]
    (B r : ℝ) (m : ℕ) [NeZero m] (F : (S → ℝ) → ℂ) (M : (S → ZMod m) → ℂ)
    {G A : ℝ} (hG : 0 ≤ G) (hM : ∀ a, ‖M a‖ ≤ G) (hF : ∀ x, ‖F x‖ ≤ A) :
    (∑ a : S → ZMod m, ∑ k : S → Fin (intervalSiteCount B r),
      ‖M a * F (fun i => intervalSiteCenter B r (k i))‖) ≤
      (m : ℝ)^Fintype.card S * (intervalSiteCount B r : ℝ)^Fintype.card S * (G * A) := by
  calc
    _ ≤ ∑ _a : S → ZMod m, ∑ _k : S → Fin (intervalSiteCount B r), G * A := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (hM a) (hF _) (norm_nonneg _) hG
    _ = _ := by simp [mul_assoc]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialSiteShift
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem spatialStarDensity_bound {I : Type*} (f : ((Unit ⊕ I) → ℝ) → ℝ) {C : ℝ}
    (hf : ∀ y, |f y| ≤ C) (y : (Unit ⊕ I) → ℝ) : ‖spatialStarDensity f y‖ ≤ C := by
  simpa only [spatialStarDensity, Complex.norm_real, Real.norm_eq_abs] using hf (spatialUnstar y)

theorem spatialSiteApprox_coefficient_sum {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : ((Unit ⊕ I) → ℝ) → ℝ) (b r : ℝ) {G C : ℝ}
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G) (hf : ∀ y, |f y| ≤ C) :
    (∑ a : (Unit ⊕ I) → ZMod m, ∑ k : (Unit ⊕ I) → Fin (intervalSiteCount b r),
      ‖latticeStarMask (pivotFullImage A B) m a *
        spatialStarDensity f (fun i => intervalSiteCenter b r (k i))‖) ≤
      (m : ℝ)^Fintype.card (Unit ⊕ I) * (intervalSiteCount b r : ℝ)^Fintype.card (Unit ⊕ I) * (G * C) :=
  maskedIntervalApprox_coefficient_sum b r m (spatialStarDensity f)
    (latticeStarMask (pivotFullImage A B) m) ((Nat.cast_nonneg _).trans hindex)
    (latticeStarMask_bound _ _ hindex) (spatialStarDensity_bound f hf)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem spatialSiteApprox_sum {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : ((Unit ⊕ I) → ℝ) → ℝ) (H b r : ℝ) (v : (Unit ⊕ I) → ℤ) :
    spatialSiteApprox A B m f H b r v =
      ∑ t : SpatialSiteLabel I m b r, spatialSiteCoefficient A B m f b r t *
        ∏ i, (residueIntervalSiteWeight b r H (t.1 i) (t.2 i) (spatialStar v i) : ℂ) := by
  simp only [spatialSiteApprox, maskedIntervalApprox, Fintype.sum_prod_type,
    spatialSiteCoefficient, Complex.ofReal_prod]

theorem spatialSiteCoefficient_sum_bound {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : ((Unit ⊕ I) → ℝ) → ℝ) (b r : ℝ) {G C : ℝ}
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G) (hf : ∀ y, |f y| ≤ C) :
    (∑ t : SpatialSiteLabel I m b r, ‖spatialSiteCoefficient A B m f b r t‖) ≤
      (m : ℝ)^Fintype.card (Unit ⊕ I) * (intervalSiteCount b r : ℝ)^Fintype.card (Unit ⊕ I) * (G*C) := by
  simpa only [Fintype.sum_prod_type, spatialSiteCoefficient] using
    spatialSiteApprox_coefficient_sum A B m f b r hindex hf

theorem vectorSpatialSiteExpansion {D I J : Type*}
    [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : D → Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : D → ((Unit ⊕ I) → ℝ) → ℝ) (H : D → ℝ)
    (b r : ℝ) (v : D → (Unit ⊕ I) → ℤ) :
    (∏ d, spatialSiteApprox A (B d) m (f d) (H d) b r (v d)) =
      ∑ t : D → SpatialSiteLabel I m b r,
        (∏ d, spatialSiteCoefficient A (B d) m (f d) b r (t d)) *
          ∏ i, vectorResidueSiteWeight b r H (fun d => (t d).1 i) (fun d => (t d).2 i)
            (fun d => spatialStar (v d) i) := by
  simp_rw [spatialSiteApprox_sum]
  exact siteFactorTensor_identity _ _ _

theorem vectorSpatialSiteCoefficient_sum_bound {D I J : Type*}
    [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : D → Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : D → ((Unit ⊕ I) → ℝ) → ℝ) (b r : ℝ) {G C : ℝ}
    (hindex : ∀ d, ((pivotFullImage A (B d)).toAddSubgroup.index : ℝ) ≤ G)
    (hf : ∀ d y, |f d y| ≤ C) :
    (∑ t : D → SpatialSiteLabel I m b r,
      ‖∏ d, spatialSiteCoefficient A (B d) m (f d) b r (t d)‖) ≤
      ((m : ℝ)^Fintype.card (Unit ⊕ I) * (intervalSiteCount b r : ℝ)^Fintype.card (Unit ⊕ I) *
        (G*C))^Fintype.card D := by
  have h := siteFactorTensor_coefficient_bound
    (fun d => spatialSiteCoefficient A (B d) m (f d) b r) _
    (fun d => spatialSiteCoefficient_sum_bound A (B d) m (f d) b r (hindex d) (hf d))
  simpa only [Finset.prod_const, Finset.card_univ] using h

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem starVertexSiteFactor_prod {α V : Type*} [Fintype α]
    (factor : Unit ⊕ α → V → ℂ) (v : Finset α → V) :
    (∏ s, starVertexSiteFactor factor s (v s)) =
      ∏ i, factor i (v (spatialStarVertex i)) := by
  unfold starVertexSiteFactor
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  simp

theorem physicalCubeVertexValue_star {X α : Type*}
    (v : X → (Unit ⊕ α) → ℤ) (i : Unit ⊕ α) :
    physicalCubeVertexValue v (spatialStarVertex i) = fun x => spatialStar (v x) i := by
  funext x
  exact (spatialStar_vertex (v x) i).symm

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Matrix

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [CompactSpace (CoefficientTorus (K := Fin q) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
variable [BorelSpace (CoefficientTorus (K := Fin q) U)]
variable (μ : Measure (CoefficientTorus (K := Fin q) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

variable {X : Type*} {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

variable {X : Type*} {m dim : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialScales
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

theorem physicalCubePivotIndex_inl {α K : Type*} (s : α ↪ K) (i : Unit) :
    physicalCubePivotIndex s (.inl i) = none := rfl

theorem physicalCubePivotIndex_inr {α K : Type*} (s : α ↪ K) (i : α) :
    physicalCubePivotIndex s (.inr i) = some (s i) := rfl

theorem physicalCubeCoefficient_pivot {α K : Type*}
    (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K) :
    (physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s) =
      selectedSpatialPivot root D s := by
  ext i j
  cases i <;> cases j <;> rfl

theorem physicalSpatialInputScale_pos (K : Type*) {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    ∀ k, 0 < physicalSpatialInputScale K A R k := by
  intro k
  cases k
  · exact hA
  · exact hR

theorem physicalCube_normalized_columns {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    (root : K → ℤ) (D : Matrix α K ℤ) {A R L : ℝ}
    (hA : A ≠ 0) (hR : R ≠ 0) (hL : L ≠ 0) :
    normalizedIntegerColumns (physicalCubeCoefficient root D)
        (physicalSpatialInputScale K A R) (physicalSpatialOutputScale α A R L) =
      fun i k => match i, k with
      | .inl _, none => 1
      | .inl _, some k => (root k : ℝ) * R / A
      | .inr _, none => 0
      | .inr i, some k => (D i k : ℝ) / L := by
  ext i k
  rw [normalizedIntegerColumns_entry_div]
  cases i <;> cases k <;>
    simp [physicalCubeCoefficient, physicalSpatialInputScale, physicalSpatialOutputScale, hA]
  field_simp

theorem physicalCube_normalized_pivot {α K : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K) {A R L : ℝ}
    (hA : A ≠ 0) (hR : R ≠ 0) (hL : L ≠ 0) :
    normalizedIntegerPivot ((physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s))
        (fun i => physicalSpatialInputScale K A R (physicalCubePivotIndex s i))
        (physicalSpatialOutputScale α A R L) =
      rootDifferenceMatrix (fun i => (root (s i) : ℝ) * R / A)
        (Matrix.of (fun i j => (D i (s j) : ℝ) / L)) := by
  ext i j
  rw [normalizedIntegerPivot_entry]
  cases i <;> cases j <;>
    simp [physicalCubePivotIndex_inl, physicalCubePivotIndex_inr,
      physicalCubeCoefficient, physicalSpatialInputScale,
      physicalSpatialOutputScale, rootDifferenceMatrix, Matrix.fromBlocks, hA]
  field_simp

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

theorem physicalCube_normalized_entry_bound {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    (root : K → ℤ) (D : Matrix α K ℤ) {A R L : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L)
    (hr : ∀ k, |(root k : ℝ)| * R ≤ A) (hD : ∀ i k, |(D i k : ℝ)| ≤ L) :
    ∀ i k, |normalizedIntegerColumns (physicalCubeCoefficient root D)
      (physicalSpatialInputScale K A R) (physicalSpatialOutputScale α A R L) i k| ≤ 1 := by
  rw [physicalCube_normalized_columns root D hA.ne' hR.ne' hL.ne']
  rintro (i | i) (k | k)
  · norm_num
  · dsimp
    rw [abs_div, abs_mul, abs_of_pos hA, abs_of_pos hR]
    exact (div_le_one hA).mpr (hr k)
  · norm_num
  · dsimp
    rw [abs_div, abs_of_pos hL]
    exact (div_le_one hL).mpr (hD i k)

theorem physicalCube_pivot_control {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K) {A R L κ : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ)
    (hr : ∀ k, |(root k : ℝ)| * R ≤ A) (hD : ∀ i k, |(D i k : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    ((physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s)).det ≠ 0 ∧
      ‖(matrixSupCLM (normalizedIntegerPivot
        ((physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s))
        (fun i => physicalSpatialInputScale K A R (physicalCubePivotIndex s i))
        (physicalSpatialOutputScale α A R L))).inverse‖ ≤
        (Fintype.card (Unit ⊕ α) : ℝ) * (Fintype.card (Unit ⊕ α)).factorial / κ := by
  let M := (physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s)
  let S := fun i => physicalSpatialInputScale K A R (physicalCubePivotIndex s i)
  let P := physicalSpatialOutputScale α A R L
  have hS : ∀ i, 0 < S i := fun i => physicalSpatialInputScale_pos K hA hR _
  have hP : ∀ i, 0 < P i := physicalSpatialOutputScale_pos α hA hR hL
  have he : normalizedIntegerPivot M S P =
      rootDifferenceMatrix (fun i => (root (s i) : ℝ) * R / A)
        (Matrix.of (fun i j => (D i (s j) : ℝ) / L)) :=
    physicalCube_normalized_pivot root D s hA.ne' hR.ne' hL.ne'
  have hd : κ ≤ |(normalizedIntegerPivot M S P).det| := by
    rw [he, rootDifferenceMatrix_det (fun i => (root (s i) : ℝ) * R / A)
      (Matrix.of (fun i j => (D i (s j) : ℝ) / L))]
    exact hminor
  have hb : ∀ i j, |normalizedIntegerPivot M S P i j| ≤ 1 := by
    intro i j
    have h := physicalCube_normalized_entry_bound root D hA hR hL hr hD i (physicalCubePivotIndex s j)
    simpa only [M, S, P, normalizedIntegerPivot_entry, normalizedIntegerColumns_entry_div,
      Matrix.submatrix_apply, id_eq] using h
  have hn : M.det ≠ 0 := by
    intro hz
    have hdet := normalizedIntegerPivot_abs_det M S P hS hP
    rw [hz, Int.natAbs_zero, Nat.cast_zero, zero_mul, zero_div] at hdet
    rw [hdet] at hd
    exact (not_le_of_gt hκ) hd
  refine ⟨hn, ?_⟩
  have h := (matrixSupCLM_inverse_norm_le (normalizedIntegerPivot M S P) zero_le_one hb hκ hd).2
  simpa only [one_pow, mul_one, mul_div_assoc] using h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSpatialLaw
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

theorem anisotropicSpatialScale_physicalPivot {I J : Type*} (s : I ↪ J) (A R : ℝ) :
    (fun i => physicalSpatialInputScale J A R (physicalCubePivotIndex s i)) =
      anisotropicSpatialScale I A R := by
  funext i
  cases i <;> rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AnisotropicSpatialCapBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

theorem anisotropicSpatialPivot_control {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) {A R L κ : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ)
    (hr : ∀ j, |(root j : ℝ)| * R ≤ A) (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    (selectedSpatialPivot root D s).det ≠ 0 ∧
      ‖(matrixSupCLM (normalizedIntegerPivot (selectedSpatialPivot root D s)
        (anisotropicSpatialScale I A R) (physicalSpatialOutputScale I A R L))).inverse‖ ≤
          physicalSpatialInverseBound I κ := by
  have h := physicalCube_pivot_control root D s hA hR hL hκ hr hD hminor
  simpa only [physicalCubeCoefficient_pivot, anisotropicSpatialScale_physicalPivot,
    physicalSpatialInverseBound] using h

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem anisotropicSpatialKernelDensity_bounds {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) {A R L κ : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ)
    (hr : ∀ j, |(root j : ℝ)| * R ≤ A) (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    let hp := (anisotropicSpatialPivot_control root D s hA hR hL hκ hr hD hminor).1
    let f := anisotropicSpatialKernelDensity s root D hp A R L hA hR hL
    (∀ y, |f y| ≤ anisotropicSpatialDensityCap s κ) ∧
      LipschitzWith (Real.toNNReal (anisotropicSpatialDensityLip s κ)) f := by
  intro hp f
  let M := selectedSpatialPivot root D s
  let E := normalizedPivotEquiv M hp (anisotropicSpatialScale I A R) (physicalSpatialOutputScale I A R L)
    (anisotropicSpatialScale_pos I hA hR) (physicalSpatialOutputScale_pos I hA hR hL)
  have hi : ‖E.symm.toContinuousLinearMap‖ ≤ physicalSpatialInverseBound I κ := by
    rw [show E = normalizedPivotEquiv M hp (anisotropicSpatialScale I A R)
      (physicalSpatialOutputScale I A R L) (anisotropicSpatialScale_pos I hA hR)
      (physicalSpatialOutputScale_pos I hA hR hL) from rfl, normalizedPivotEquiv_inverse_eq]
    exact (anisotropicSpatialPivot_control root D s hA hR hL hκ hr hD hminor).2
  constructor
  · intro y
    have h := pivotOutputDensity_abs_le_uniform E
      (matrixSupCLM (normalizedIntegerColumns (selectedSpatialFreeColumns root D s)
        (fun _ => R) (physicalSpatialOutputScale I A R L)))
      (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) zero_le_one zero_le_one
      (smoothSplitProfile_zero_outside _ _) (smoothSplitProfile_norm_le _ _) hi y
    simpa only [f, anisotropicSpatialKernelDensity, normalizedFiberDensity,
      anisotropicSpatialDensityCap, E, M, mul_one] using h
  · apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [Real.dist_eq, Real.coe_toNNReal _ (anisotropicSpatialDensityLip_nonneg s hκ.le)]
    have h := pivotOutputDensity_output_bound_uniform E
      (matrixSupCLM (normalizedIntegerColumns (selectedSpatialFreeColumns root D s)
        (fun _ => R) (physicalSpatialOutputScale I A R L)))
      (smoothSplitProfile_lipschitz (UnselectedColumn s) (Unit ⊕ I)) zero_le_one
      (smoothSplitProfile_zero_outside _ _) hi v w
    simpa only [f, anisotropicSpatialKernelDensity, normalizedFiberDensity,
      anisotropicSpatialDensityLip, anisotropicSpatialDensityCap, E, M, mul_one,
      NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, dist_eq_norm, mul_assoc] using h

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicCanonicalDensity
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem coordinateRescaledDensity_bound {I : Type*} (a : I → ℝ)
    (f : (I → ℝ) → ℝ) {C : ℝ} (hf : ∀ x, |f x| ≤ C) :
    ∀ x, |coordinateRescaledDensity a f x| ≤ C := fun x => hf (fun i => a i * x i)

theorem coordinateScale_lipschitz {I : Type*} [Fintype I]
    (a : I → ℝ) {C : ℝ≥0} (ha : ∀ i, |a i| ≤ C) :
    LipschitzWith C (fun x : I → ℝ => fun i => a i * x i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg C.coe_nonneg (norm_nonneg _))).2
  intro i
  change ‖a i * x i - a i * y i‖ ≤ _
  rw [← mul_sub, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul (ha i) (norm_le_pi_norm (x - y) i) (norm_nonneg _) C.coe_nonneg

theorem coordinateRescaledDensity_lipschitz {I : Type*} [Fintype I]
    (a : I → ℝ) (f : (I → ℝ) → ℝ) {K C : ℝ≥0}
    (hf : LipschitzWith K f) (ha : ∀ i, |a i| ≤ C) :
    LipschitzWith (K * C) (coordinateRescaledDensity a f) :=
  hf.comp (coordinateScale_lipschitz a ha)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {I : Type*} [Fintype I]

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel

theorem canonicalSpatialSiteDensity_bounds {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L κ : ℝ} (hW : 0 ≤ W) (hL : 0 < L) (hL1 : 1 ≤ L) (hκ : 0 < κ)
    (hr : ∀ j, |(root j : ℝ)| ≤ 1 + W) (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    (∀ z, |canonicalSpatialSiteDensity s root D hp W L hW hL z| ≤ anisotropicSpatialDensityCap s κ) ∧
      LipschitzWith (Real.toNNReal (anisotropicSpatialDensityLip s κ) * Real.toNNReal (1 + W))
        (canonicalSpatialSiteDensity s root D hp W L hW hL) := by
  have ha : 0 < 1 + W := by linarith
  have h := anisotropicSpatialKernelDensity_bounds root D s ha zero_lt_one hL hκ
    (fun j => by simpa only [mul_one] using hr j) hD hminor
  have hcap : ∀ z, |canonicalSpatialKernelDensity s root D hp W L hW hL z| ≤
      anisotropicSpatialDensityCap s κ := h.1
  have hlip : LipschitzWith (Real.toNNReal (anisotropicSpatialDensityLip s κ))
      (canonicalSpatialKernelDensity s root D hp W L hW hL) := h.2
  constructor
  · exact coordinateRescaledDensity_bound _ _ hcap
  · apply coordinateRescaledDensity_lipschitz _ _ hlip
    intro i
    rw [Real.coe_toNNReal _ ha.le]
    cases i with
    | inl i =>
      change |(1 + W) / (1 + W)| ≤ 1 + W
      rw [div_self ha.ne', abs_one]
      linarith
    | inr i =>
      change |(1 + W) / (L * 1)| ≤ 1 + W
      rw [mul_one, abs_div, abs_of_pos ha, abs_of_pos hL]
      exact div_le_self ha.le hL1

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSpatialResidueSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residueSiteIndicator_affine {m : ℕ} [NeZero m] (q : ℕ) (hq : 0 < q)
    (offset : ℤ) (a : ZMod m) (z : ℤ) :
    residueSiteIndicator (m := q * m)
        ((offset + (q : ℤ) * (a.val : ℤ) : ℤ) : ZMod (q * m))
        (offset + (q : ℤ) * z) = residueSiteIndicator a z := by
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hval : ((a.val : ℤ) : ZMod m) = a := by simp
  have heq :
      ((offset + (q : ℤ) * z : ℤ) : ZMod (q * m)) =
        ((offset + (q : ℤ) * (a.val : ℤ) : ℤ) : ZMod (q * m)) ↔
      (z : ZMod m) = a := by
    calc
      _ ↔ ((q * m : ℕ) : ℤ) ∣
          (offset + (q : ℤ) * (a.val : ℤ)) - (offset + (q : ℤ) * z) :=
        ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _
      _ ↔ (m : ℤ) ∣ (a.val : ℤ) - z := by
        rw [Nat.cast_mul, show
          (offset + (q : ℤ) * (a.val : ℤ)) - (offset + (q : ℤ) * z) =
            (q : ℤ) * ((a.val : ℤ) - z) by ring, mul_dvd_mul_iff_left hqz]
      _ ↔ (z : ZMod m) = ((a.val : ℤ) : ZMod m) :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).symm
      _ ↔ (z : ZMod m) = a := by rw [hval]
  unfold residueSiteIndicator
  simp only [heq]

theorem affineResidueIntervalSiteWeight_range (b H : ℝ) {r : ℝ} (hr : 0 < r)
    (q : ℕ) (offset : ℤ) {m : ℕ} (a : ZMod m)
    (k : Fin (intervalSiteCount b r)) (u : ℤ) :
    0 ≤ affineResidueIntervalSiteWeight b r H q offset a k u ∧
      affineResidueIntervalSiteWeight b r H q offset a k u ≤ 1 := by
  have ha := residueSiteIndicator_range
    (m := q * m) ((offset + (q : ℤ) * (a.val : ℤ) : ℤ) : ZMod (q * m)) u
  have hk := intervalSiteWeight_range b hr k (((u : ℝ) - offset) / ((q : ℝ) * H))
  exact ⟨mul_nonneg ha.1 hk.1,
    (mul_le_mul ha.2 hk.2 hk.1 zero_le_one).trans_eq (one_mul 1)⟩

theorem affineResidueIntervalSiteWeight_pullback (b r H : ℝ) (q : ℕ) (hq : 0 < q)
    (offset : ℤ) {m : ℕ} [NeZero m] (a : ZMod m)
    (k : Fin (intervalSiteCount b r)) (z : ℤ) :
    affineResidueIntervalSiteWeight b r H q offset a k (offset + (q : ℤ) * z) =
      residueIntervalSiteWeight b r H a k z := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold affineResidueIntervalSiteWeight residueIntervalSiteWeight
  rw [residueSiteIndicator_affine q hq]
  congr 2
  push_cast
  rw [add_sub_cancel_left, mul_div_mul_left _ _ hqR]

theorem affineVectorResidueSiteWeight_bound {X : Type*} [Fintype X]
    (b : ℝ) {r : ℝ} (hr : 0 < r) (H : X → ℝ) (q : X → ℕ) (offset : X → ℤ)
    {m : ℕ} (a : X → ZMod m) (k : X → Fin (intervalSiteCount b r)) (u : X → ℤ) :
    ‖affineVectorResidueSiteWeight b r H q offset a k u‖ ≤ 1 := by
  rw [affineVectorResidueSiteWeight, norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro x _
  have h := affineResidueIntervalSiteWeight_range b (H x) hr (q x) (offset x) (a x) (k x) (u x)
  simpa only [Complex.norm_real, Real.norm_of_nonneg h.1] using h.2

theorem affineVectorResidueSiteWeight_pullback {X : Type*} [Fintype X]
    (b r : ℝ) (H : X → ℝ) (q : X → ℕ) (hq : ∀ x, 0 < q x) (offset : X → ℤ)
    {m : ℕ} [NeZero m] (a : X → ZMod m) (k : X → Fin (intervalSiteCount b r))
    (z : X → ℤ) :
    affineVectorResidueSiteWeight b r H q offset a k (fun x => offset x + (q x : ℤ) * z x) =
      vectorResidueSiteWeight b r H a k z := by
  unfold affineVectorResidueSiteWeight vectorResidueSiteWeight
  apply Finset.prod_congr rfl
  intro x _
  rw [affineResidueIntervalSiteWeight_pullback b r (H x) (q x) (hq x)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalCubeVertexValue_residueReconstruction {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ)
    (v : X → (Unit ⊕ α) → ℤ) (s : Finset α) (x : X) :
    physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s x =
      physicalCubeVertexValue (physicalCubeRootDifferences root D base residue) s x +
        (q x : ℤ) * physicalCubeVertexValue v s x := by
  simp only [physicalCubeVertexValue, physicalResidueReconstruction,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem physicalResidueSpatialSiteFactor_bound {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (b : ℝ) {r : ℝ} (hr : 0 < r)
    (H : X → ℝ) {m : ℕ} (t : X → SpatialSiteLabel α m b r)
    (s : Finset α) (u : X → ℤ) :
    ‖physicalResidueSpatialSiteFactor root D base residue q b r H t s u‖ ≤ 1 := by
  apply starVertexSiteFactor_bound
  intro i y
  exact affineVectorResidueSiteWeight_bound b hr H q _ _ _ y

theorem physicalResidueStarFactor_pullback {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (b r : ℝ) (H : X → ℝ) {m : ℕ} [NeZero m]
    (t : X → SpatialSiteLabel α m b r) (i : Unit ⊕ α)
    (v : X → (Unit ⊕ α) → ℤ) :
    physicalResidueStarFactor root D base residue q b r H t i
        (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v)
          (spatialStarVertex i)) =
      vectorResidueSiteWeight b r H (fun x => (t x).1 i) (fun x => (t x).2 i)
        (fun x => spatialStar (v x) i) := by
  unfold physicalResidueStarFactor
  have hvertex :
      physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v)
          (spatialStarVertex i) =
        fun x => physicalCubeVertexValue (physicalCubeRootDifferences root D base residue)
          (spatialStarVertex i) x + (q x : ℤ) * spatialStar (v x) i := by
    funext x
    rw [physicalCubeVertexValue_residueReconstruction, physicalCubeVertexValue_star v i]
  rw [hvertex]
  exact affineVectorResidueSiteWeight_pullback b r H q hq _ _ _ _

theorem physicalResidueSpatialSiteFactor_prod {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (b r : ℝ) (H : X → ℝ) {m : ℕ} [NeZero m]
    (t : X → SpatialSiteLabel α m b r) (v : X → (Unit ⊕ α) → ℤ) :
    (∏ s, physicalResidueSpatialSiteFactor root D base residue q b r H t s
      (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s)) =
      ∏ i, vectorResidueSiteWeight b r H (fun x => (t x).1 i) (fun x => (t x).2 i)
        (fun x => spatialStar (v x) i) := by
  unfold physicalResidueSpatialSiteFactor
  rw [starVertexSiteFactor_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact physicalResidueStarFactor_pullback root D base residue q hq b r H t i v

theorem physicalResidue_spatialSiteExpansion {K X J : Type*} {dim : ℕ}
    [Fintype K] [Fintype X] [DecidableEq X] [Fintype J]
    (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (A : Matrix (Unit ⊕ Fin dim) (Unit ⊕ Fin dim) ℤ)
    (B : X → Matrix (Unit ⊕ Fin dim) J ℤ) (m : ℕ) [NeZero m]
    (f : X → ((Unit ⊕ Fin dim) → ℝ) → ℝ) (H : X → ℝ) (b r : ℝ)
    (v : X → (Unit ⊕ Fin dim) → ℤ)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) :
    (∏ x, spatialSiteApprox A (B x) m (f x) (H x) b r (v x)) *
        physicalCubeSiteTest test (physicalResidueReconstruction root D base residue q v) =
      ∑ t : X → SpatialSiteLabel (Fin dim) m b r,
        (∏ x, spatialSiteCoefficient A (B x) m (f x) b r (t x)) *
          ∏ s, test s (fun x =>
            (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s x : ℝ)) *
              physicalResidueSpatialSiteFactor root D base residue q b r H t s
                (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s) := by
  rw [vectorSpatialSiteExpansion, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [mul_assoc, Finset.prod_mul_distrib,
    physicalResidueSpatialSiteFactor_prod root D base residue q hq]
  congr 1
  exact mul_comm _ _

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedLocalResidueReconstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (H : X → ℝ)
variable {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)


variable (q : X → ℕ) {τ : ℝ}
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)

local notation "labels" => PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus
local notation "terms" => X → SpatialSiteLabel (Fin dim) modulus 4 mesh

theorem allocatedSpatialExpansionCoefficient_sum_le
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection)) (r : labels) :
    (∑ t : terms, ‖allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh r t‖) ≤
      allocatedSpatialCoefficientCap X selection M modulus mesh := by
  let ker := fun g => (0 : ℤ) + (x g none : ℤ)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker
    (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
  let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hp W S.value
    hW (Nat.cast_pos.mpr S.positive)
  obtain ⟨y, _hy⟩ := (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).exists_weight_pos
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hroot (g : G) : |(ker g : ℝ)| ≤ 1 + W := by
    have h := (allocatedPhysicalCube_root_budget B U b S (fun _ => 0) x y (.inl g)).trans hbudget
    change |(ker g : ℝ)| ≤ W at h
    linarith
  have hD (i : Fin dim) (g : G) : |(scalarCubeDifferenceMatrix x i g : ℝ)| ≤ S.value :=
    allocatedPhysicalCube_directions_bound B U b S x y i (.inl g)
  have hminor : 1 / (M : ℝ) ≤
      |(Matrix.of (fun i j => (scalarCubeDifferenceMatrix x i (selection j) : ℝ) / (S.value : ℝ))).det| := by
    change 1 / (M : ℝ) ≤ |(normalizedScalarCubePivot selection x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  have hf := (canonicalSpatialSiteDensity_bounds selection ker (scalarCubeDifferenceMatrix x) hp
    hW (Nat.cast_pos.mpr S.positive) (by exact_mod_cast S.positive) hκ hroot hD hminor).1
  let extra := Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
    (liftResidueMatrix (principalSpatialResidueColumns modulus (fun _ => (0 : ℤ)) id r))
  have hfull : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection) extra := by
    dsimp only [extra]
    rw [pivotFullImage_split]
    exact hperiod.trans le_sup_left
  have hindex : ((pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
      extra).toAddSubgroup.index : ℝ) ≤ (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) := by
    exact_mod_cast residueLatticeImage_index_le _ modulus hfull
  exact vectorSpatialSiteCoefficient_sum_bound _ (fun _ : X => extra) modulus (fun _ => f)
    4 mesh (fun _ => hindex) (fun _ => hf)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (H : X → ℝ)

variable {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S

variable (X : Type*) [Fintype X]


variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (C₀ ρ δ mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cg Z : ℝ)

local notation "label" => (PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedAmbientBoxTests
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ) (base : X → ℤ)

local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)

omit [DecidableEq G] [NeZero modulus] in
theorem allocatedRecenteredSpatialTwist_bound (hmesh : 0 < mesh)
    (r : labels) (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q)
    (t : terms) (s : Finset (Fin dim)) (u : X → ℤ) :
    ‖allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base r a t s u‖ ≤ 1 := by
  exact physicalResidueSpatialSiteFactor_bound _ _ base _ q 4 hmesh _ t s u

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W : ℝ} (hW : 0 ≤ W)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))

local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

theorem allocatedRecenteredResidueWeight_expansion (hq : ∀ z, 0 < q z)
    (r : labels) (a : cells) (v : X → (Unit ⊕ Fin dim) → ℤ)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) :
    allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
        N hW mesh base cells (physicalCubeSiteTest test) r a v =
      ∑ t : terms, (coeff (principalResidueLabel modulus (wholeReference r)) t / ((volume : ℝ) : ℂ)) *
        ∏ s, test s (fun z => (physicalCubeVertexValue (reconstruct r a.val v) s z : ℝ)) *
          twist r a.val t s (physicalCubeVertexValue (reconstruct r a.val v) s) := by
  have hexp :
      allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW mesh (principalResidueLabel modulus (wholeReference r)) v *
        physicalCubeSiteTest test (reconstruct r a.val v) =
      ∑ t : terms, coeff (principalResidueLabel modulus (wholeReference r)) t *
        ∏ s, test s (fun z => (physicalCubeVertexValue (reconstruct r a.val v) s z : ℝ)) *
          twist r a.val t s (physicalCubeVertexValue (reconstruct r a.val v) s) := by
    exact physicalResidue_spatialSiteExpansion _ _ base _ q hq _ _ modulus _ _ 4 mesh v test
  unfold allocatedRecenteredResidueWeight
  rw [div_mul_eq_mul_div, hexp, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem allocatedRecenteredSpatial_sum_expansion (hq : ∀ z, 0 < q z)
    (r : labels) (a : cells) (vset : Finset (X → (Unit ⊕ Fin dim) → ℤ))
    (test : Finset (Fin dim) → (X → ℝ) → ℂ)
    (F : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) :
    (∑ v ∈ vset, allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x
        hM selection hx N hW mesh base cells (physicalCubeSiteTest test) r a v * F v) =
      ∑ t : terms, (coeff (principalResidueLabel modulus (wholeReference r)) t / ((volume : ℝ) : ℂ)) *
        ∑ v ∈ vset, (∏ s, test s (fun z => (physicalCubeVertexValue (reconstruct r a.val v) s z : ℝ)) *
          twist r a.val t s (physicalCubeVertexValue (reconstruct r a.val v) s)) * F v := by
  simp_rw [allocatedRecenteredResidueWeight_expansion B U b S X modulus q wholeReference x N mesh base
    hM selection hx hW cells hq, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (a : cells)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (a : cells)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ) (base : X → ℤ)

local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W ξ : ℝ} (hW : 0 ≤ W)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))

local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4
local notation "V" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

theorem allocatedRecentered_exists_twisted_source
    (hq : ∀ z, 0 < q z) (hmesh : 0 < mesh)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hV : ∀ z, 0 < V z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight q cells V z)
    (r : labels) (test : Finset (Fin dim) → (X → ℝ) → ℂ)
    (F : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C)
    (hcoeff : allocatedSpatialCoefficientCap X selection M modulus mesh ≤ C)
    (hsource : δ ≤ ‖∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
      ∑ v ∈ window, allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x
        hM selection hx N hW mesh base cells (physicalCubeSiteTest test) r a v * F (reconstruct r a.val v)‖) :
    ∃ (a : cells) (t : terms),
      coeff (principalResidueLabel modulus (wholeReference r)) t ≠ 0 ∧
      (∀ s u, ‖twist r a.val t s u‖ ≤ 1) ∧
      δ / C ≤ ‖(∑ v ∈ window,
        (∏ s, test s (fun z => (physicalCubeVertexValue (reconstruct r a.val v) s z : ℝ)) *
          twist r a.val t s (physicalCubeVertexValue (reconstruct r a.val v) s)) *
            F (reconstruct r a.val v)) / ((volume : ℝ) : ℂ)‖ := by
  let c : cells → ℂ := fun a => (selectedResidueCellWeight q cells V a : ℂ)
  let d : terms → ℂ := coeff (principalResidueLabel modulus (wholeReference r))
  let z : cells → terms → ℂ := fun a t => (∑ v ∈ window,
    (∏ s, test s (fun u => (physicalCubeVertexValue (reconstruct r a.val v) s u : ℝ)) *
      twist r a.val t s (physicalCubeVertexValue (reconstruct r a.val v) s)) *
        F (reconstruct r a.val v)) / ((volume : ℝ) : ℂ)
  have hc : (∑ a, ‖c a‖) ≤ 1 := by
    simp only [c, Complex.norm_real, Real.norm_of_nonneg (selectedResidueCellWeight_nonneg q cells V _)]
    exact (selectedResidueCellWeight_sum q cells V hV hZ).le
  have hd : (∑ t, ‖d t‖) ≤ C :=
    (allocatedSpatialExpansionCoefficient_sum_le B U b S x X hM selection hx modulus hW mesh
      hbudget hperiod _).trans hcoeff
  have heq (a : cells) :
      (∑ v ∈ window, allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x
        hM selection hx N hW mesh base cells (physicalCubeSiteTest test) r a v * F (reconstruct r a.val v)) =
        ∑ t, d t * z a t := by
    rw [allocatedRecenteredSpatial_sum_expansion B U b S X modulus q wholeReference x N mesh base
      hM selection hx hW cells hq r a window test (fun v => F (reconstruct r a.val v))]
    apply Finset.sum_congr rfl
    intro t _
    dsimp only [d, z]
    ring
  simp_rw [heq, Finset.mul_sum, ← mul_assoc] at hsource
  obtain ⟨a, t, _, hdt, ht⟩ := exists_large_weighted_pair_nonzero c (fun _ => d) z hδ zero_lt_one hC hc
    (fun _ => hd) hsource
  refine ⟨a, t, hdt, ?_, ?_⟩
  · exact allocatedRecenteredSpatialTwist_bound B U b S X modulus q wholeReference x N mesh base hmesh r a.val t
  · simpa only [one_mul] using ht

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (a : cells)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable (period : ℕ) [NeZero period]
variable {K : Type*} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (a : cells)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable (period : ℕ) [NeZero period]
variable {K : Type*} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (a : cells)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable (period : ℕ) [NeZero period]
variable {K : Type*} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ≥0) (base : X → ℤ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q)
variable (period : ℕ)


variable (spatial : X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
variable (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))
variable (fi : (LayerSamplerAxis I n → ℝ) → ℂ) (s : Finset (Fin dim))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ≥0) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (a : cells)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable (period : ℕ) [NeZero period]
variable {K : Type*} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ≥0) (base : X → ℤ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q)
variable (period : ℕ)


variable (spatial : X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
variable (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))
variable (fi : (LayerSamplerAxis I n → ℝ) → ℂ) (s : Finset (Fin dim))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ≥0) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (a : cells)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable (period : ℕ) [NeZero period]
variable {K : Type*} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ≥0) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (a : cells)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable (period : ℕ) [NeZero period]
variable {K : Type*} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

variable [DecidableEq X]

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedRecentered_exists_twisted_source.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedRecentered_exists_twisted_source.{u_1, u_2, u_3, u_4, u_5}
