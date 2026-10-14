-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedRecenteredSelectedMean_l1_source
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-11T23:08:20.527436+00:00
-- url     : https://prove2.me/submissions/1fcb47b3-1229-4c30-a0d7-c62d3fdd877c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B162
import Definitions.Def_OAIErdos3B200
import Theorems.Thm_OAI_Erdos3_FiniteProbabilityWeights_complexMean_congr_support

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

theorem integerResidueMatrix_eq_iff_dvd_sub {I J : Type*}
    (C D : Matrix I J ℤ) (m : ℕ) :
    integerResidueMatrix C m = integerResidueMatrix D m ↔
      ∀ i j, (m : ℤ) ∣ C i j - D i j := by
  constructor
  · intro h i j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (C i j - D i j) m).mp
    rw [Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun (congrFun h i) j)
  · intro h
    ext i j
    change (C i j : ZMod m) = (D i j : ZMod m)
    apply sub_eq_zero.mp
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (C i j - D i j) m).mpr (h i j)
    simpa only [Int.cast_sub] using hz

theorem integerResidueMatrix_reduce {I J : Type*} (C D : Matrix I J ℤ)
    {m n : ℕ} (hmn : m ∣ n) (h : integerResidueMatrix C n = integerResidueMatrix D n) :
    integerResidueMatrix C m = integerResidueMatrix D m := by
  apply (integerResidueMatrix_eq_iff_dvd_sub C D m).mpr
  have hd : (m : ℤ) ∣ (n : ℤ) := by exact_mod_cast hmn
  exact fun i j => hd.trans ((integerResidueMatrix_eq_iff_dvd_sub C D n).mp h i j)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem intervalSiteWeight_sum {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : ℝ) (hx : |x| ≤ B) :
    ∑ i, intervalSiteWeight B r i x = 1 := by
  apply regularizedTentPartition_sum _ hr
  obtain ⟨i, hi⟩ := exists_uniformIntervalGrid_approx hB (boxCoverMeshCount_pos B 1 r) x hx
  refine ⟨i, ?_⟩
  have he := boxCoverMeshCount_error (1 : ℝ≥0) hr (B := B)
  simp only [NNReal.coe_one, one_mul] at he
  exact (show dist x (intervalSiteCenter B r i) ≤ 2 * B / boxCoverMeshCount B 1 r from hi).trans he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped NNReal

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace RepresentativeWindow

end RepresentativeWindow
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {α : Type*} [Fintype α] {κ X : α → Type*}
  (ψ : ∀ a, κ a → X a → ℝ)

variable [DecidableEq α] [∀ a, Fintype (κ a)]

variable [∀ a, PseudoMetricSpace (X a)]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

theorem intervalTensorWeight_nonneg {S : Type*} [Fintype S] (B : ℝ) {r : ℝ} (hr : 0 < r)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) : 0 ≤ intervalTensorWeight B r k x :=
  Finset.prod_nonneg (fun i _ => (intervalSiteWeight_range B hr (k i) (x i)).1)

theorem intervalTensorWeight_sum {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ∑ k : S → Fin (intervalSiteCount B r), intervalTensorWeight B r k x = 1 := by
  unfold intervalTensorWeight
  rw [← Fintype.prod_sum (fun i k => intervalSiteWeight B r k (x i))]
  simp only [intervalSiteWeight_sum hB hr _ (hx _), Finset.prod_const_one]

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueIntervalFactors
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem prod_residueSiteIndicator {S : Type*} [Fintype S] (m : ℕ)
    (r : S → ZMod m) (u : S → ℤ) :
    (∏ i, residueSiteIndicator (r i) (u i)) = if (fun i => (u i : ZMod m)) = r then 1 else 0 := by
  classical
  by_cases h : (fun i => (u i : ZMod m)) = r
  · simp only [h, ite_true]
    apply Finset.prod_eq_one
    intro i _
    simp only [residueSiteIndicator, congrFun h i, ite_true]
  · rw [if_neg h]
    have hn : ∃ i, (u i : ZMod m) ≠ r i := not_forall.mp (fun hi => h (funext hi))
    obtain ⟨i, hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [residueSiteIndicator, hi])

theorem prod_residueIntervalSiteWeight {S : Type*} [Fintype S] (B r H : ℝ) (m : ℕ)
    (a : S → ZMod m) (k : S → Fin (intervalSiteCount B r)) (u : S → ℤ) :
    (∏ i, residueIntervalSiteWeight B r H (a i) (k i) (u i)) =
      (if (fun i => (u i : ZMod m)) = a then 1 else 0) *
        intervalTensorWeight B r k (fun i => (u i : ℝ) / H) := by
  classical
  simp only [residueIntervalSiteWeight, Finset.prod_mul_distrib, prod_residueSiteIndicator,
    intervalTensorWeight]

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

theorem maskedIntervalApprox_eq {S : Type*} [Fintype S] [DecidableEq S]
    (B r H : ℝ) (m : ℕ) [NeZero m]
    (F : (S → ℝ) → ℂ) (M : (S → ZMod m) → ℂ) (u : S → ℤ) :
    maskedIntervalApprox B r H m F M u =
      M (fun i => (u i : ZMod m)) * intervalTensorApprox B r F (fun i => (u i : ℝ) / H) := by
  classical
  unfold maskedIntervalApprox
  simp_rw [prod_residueIntervalSiteWeight]
  rw [Finset.sum_eq_single (fun i => (u i : ZMod m))]
  · simp only [ite_true, one_mul]
    rw [intervalTensorApprox, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · intro a _ ha
    simp only [Ne.symm ha, ite_false, zero_mul, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero]
  · simp

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

theorem intervalTensorApprox_norm_le {S : Type*} [Fintype S] [DecidableEq S]
    {B r C : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → ℝ) → ℂ)
    (hF : ∀ y, ‖F y‖ ≤ C) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ‖intervalTensorApprox B r F x‖ ≤ C := by
  unfold intervalTensorApprox
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k : S → Fin (intervalSiteCount B r), intervalTensorWeight B r k x * C := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (intervalTensorWeight_nonneg B hr k x)]
      exact mul_le_mul_of_nonneg_left (hF _) (intervalTensorWeight_nonneg B hr k x)
    _ = C := by rw [← Finset.sum_mul, intervalTensorWeight_sum hB hr x hx, one_mul]

theorem spatialSiteApprox_norm_le {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : ((Unit ⊕ I) → ℝ) → ℝ) (H : ℝ)
    {b r G C : ℝ} (hb : 0 < b) (hr : 0 < r)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hf : ∀ y, |f y| ≤ C) (v : (Unit ⊕ I) → ℤ)
    (hv : ∀ i, |((spatialStar v i : ℤ) : ℝ) / H| ≤ b) :
    ‖spatialSiteApprox A B m f H b r v‖ ≤ G * C := by
  rw [spatialSiteApprox, maskedIntervalApprox_eq, norm_mul]
  exact mul_le_mul (latticeStarMask_bound _ _ hindex _)
    (intervalTensorApprox_norm_le hb hr _ (spatialStarDensity_bound f hf) _ hv)
    (norm_nonneg _) ((Nat.cast_nonneg _).trans hindex)

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

theorem trimmedSpatial_scales_pos {X : Type*} {B τ : ℝ} (hB : 0 ≤ B) (hτ : 0 < τ)
    (N modulus : X → ℕ) (x : X) (hN : 0 < N x) (hq : 0 < modulus x) :
    0 < trimmedSpatialRootScale τ N modulus x ∧ 0 < trimmedSpatialSlopeScale B τ N modulus x := by
  have hn : (0 : ℝ) < N x := by exact_mod_cast hN
  have hq' : (0 : ℝ) < modulus x := by exact_mod_cast hq
  unfold trimmedSpatialRootScale trimmedSpatialSlopeScale
  constructor <;> positivity

theorem trimmedSpatial_scale_ratio {X : Type*} {B τ : ℝ} (hB : 0 ≤ B)
    (N modulus : X → ℕ) (x : X) :
    trimmedSpatialRootScale τ N modulus x =
      (1 + B) * trimmedSpatialSlopeScale B τ N modulus x := by
  have hb : 1 + B ≠ 0 := ne_of_gt (by linarith)
  unfold trimmedSpatialRootScale trimmedSpatialSlopeScale
  field_simp

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalAmbientVolumeRatio
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalSpatial_uniform_volume {X α : Type*} [Fintype X] [Fintype α]
    (H T : X → ℝ) {W L : ℝ} (hL : L ≠ 0) (hscale : ∀ d, H d = (1 + W) * T d) :
    (∏ d, ∏ _i : Unit ⊕ α, H d) =
      (((1 + W) / L) ^ Fintype.card α) ^ Fintype.card X *
        ∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) L i := by
  have hrow (d) : (∏ _i : Unit ⊕ α, H d) =
      ((1 + W) / L) ^ Fintype.card α * ∏ i, physicalSpatialOutputScale α (H d) (T d) L i := by
    simp only [Fintype.prod_sum_type, physicalSpatialOutputScale, Sum.elim_inl, Sum.elim_inr,
      Finset.prod_const, Finset.card_univ, Fintype.card_unique, pow_one]
    have he : (1 + W) / L * (L * T d) = H d := by rw [hscale d]; field_simp
    rw [mul_left_comm _ (H d), ← mul_pow, he]
    simp only [Fintype.card_sum, Fintype.card_unique, pow_add, pow_one]
  simp_rw [hrow]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialShiftedWindowError
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

namespace BooleanCubeKernel

open scoped BigOperators

theorem mem_spatialWindow_scaled_iff {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (hH : ∀ d, 0 < H d) (b : ℝ) (v : X → (Unit ⊕ α) → ℤ) :
    v ∈ spatialWindow H b ↔ ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ b := by
  rw [mem_spatialWindow_iff]
  simp only [abs_div, abs_of_pos (hH _), div_le_iff₀ (hH _), mul_comm]

theorem spatialWindow_card {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (hH : ∀ d, 1 ≤ H d) {b : ℝ} (hb : 0 ≤ b) :
    ((spatialWindow (α := α) H b).card : ℝ) ≤
      (2*b+1) ^ Fintype.card (X × (Unit ⊕ α)) * (∏ d, ∏ _i : Unit ⊕ α, H d) := by
  classical
  let F : (X → (Unit ⊕ α) → ℤ) → (X × (Unit ⊕ α) → ℤ) :=
    fun v z => spatialStar (v z.1) z.2
  have hinj : Function.Injective F := by
    intro v w h
    funext d
    have he : spatialStar (v d) = spatialStar (w d) := funext (fun i => congrFun h (d, i))
    have hu := congrArg spatialUnstar he
    simpa only [spatialUnstar_star] using hu
  have hinto : (spatialWindow H b).image F ⊆
      rectangularWeightIndices 0 (fun z : X × (Unit ⊕ α) => H z.1) b := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    apply (mem_rectangular_zero_radius_iff _ b _).mpr
    intro z
    exact (mem_spatialWindow_iff H b v).mp hv z.1 z.2
  have hc : (spatialWindow (α := α) H b).card ≤
      (rectangularWeightIndices 0 (fun z : X × (Unit ⊕ α) => H z.1) b).card := by
    rw [← Finset.card_image_of_injective _ hinj]
    exact Finset.card_le_card hinto
  apply (Nat.cast_le.mpr hc).trans
  simpa only [Fintype.prod_prod_type] using
    rectangularWeightIndices_card_le (0 : X × (Unit ⊕ α) → ℝ)
      (fun z => H z.1) (fun z => hH z.1) hb

theorem spatialWindow_card_anisotropic {X α : Type*} [Fintype X] [Fintype α]
    (H T : X → ℝ) {W L b : ℝ} (hH : ∀ d, 1 ≤ H d) (hb : 0 ≤ b)
    (hL : L ≠ 0) (hscale : ∀ d, H d = (1 + W) * T d) :
    ((spatialWindow (α := α) H b).card : ℝ) ≤
      ((2*b+1) ^ Fintype.card (X × (Unit ⊕ α)) *
        (((1+W)/L) ^ Fintype.card α) ^ Fintype.card X) *
      ∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) L i := by
  have h := spatialWindow_card (α := α) H hH hb
  rw [physicalSpatial_uniform_volume H T hL hscale, ← mul_assoc] at h
  exact h

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

namespace BooleanCubeKernel

variable {X I : Type*} [Fintype X] [Fintype I]

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

variable {X I : Type*} [Fintype X] [Fintype I]

end BooleanCubeKernel
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SpatialResidueMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residueSpatialSite_norm_le {D I J N : Type*}
    [Fintype D] [Fintype I] [DecidableEq I] [Fintype J] [Fintype N]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (f : D → ((Unit ⊕ I) → ℝ) → ℝ) (H : D → ℝ)
    {b r C : ℝ} (hb : 0 < b) (hr : 0 < r) (_hC : 0 ≤ C) (hf : ∀ d y, |f d y| ≤ C)
    (residue : D → Matrix (Unit ⊕ I) N (ZMod m)) (v : D → (Unit ⊕ I) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ)/H d| ≤ b) :
    ‖∏ d, spatialSiteApprox A (Matrix.fromCols B (liftResidueMatrix (residue d))) m (f d) (H d) b r (v d)‖ ≤
      ((m : ℝ)^Fintype.card (Unit ⊕ I)*C)^Fintype.card D := by
  have hfull (d : D) : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage A (Matrix.fromCols B (liftResidueMatrix (residue d))) := by
    rw [pivotFullImage_split]
    exact hp.trans le_sup_left
  have hi (d : D) :
      ((pivotFullImage A (Matrix.fromCols B (liftResidueMatrix (residue d)))).toAddSubgroup.index : ℝ) ≤
        (m : ℝ)^Fintype.card (Unit ⊕ I) := by
    exact_mod_cast residueLatticeImage_index_le _ m (hfull d)
  calc
    _ ≤ ∏ d, ‖spatialSiteApprox A (Matrix.fromCols B (liftResidueMatrix (residue d))) m (f d) (H d) b r (v d)‖ :=
      (norm_prod _ _).le
    _ ≤ ∏ _d : D, (m : ℝ)^Fintype.card (Unit ⊕ I)*C :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun d _ =>
        spatialSiteApprox_norm_le A _ m (f d) (H d) hb hr (hi d) (hf d) (v d) (hv d))
    _ = _ := by simp

end Erdos3

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedTrimmedResidueTest
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem selectedResidue_site_mass_bound {K X Y : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (T : Finset (ColumnResiduePattern K X q)) (V : K × X → ℝ)
    (hV : ∀ z, 0 < V z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (S : Finset Y) (φ : T → Y → ℂ) {A E B C : ℝ}
    (hA : 0 < A) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hφ : ∀ a v, v ∈ S → ‖φ a v‖ ≤ B) (hcard : (S.card : ℝ) ≤ C * A) :
    (∑ a : T, selectedResidueCellWeight q T V a * ((E / A) * ∑ v ∈ S, ‖φ a v‖)) ≤
      B * E * C := by
  have hpart (a : T) : (E / A) * (∑ v ∈ S, ‖φ a v‖) ≤ B * E * C := by
    have hs : (∑ v ∈ S, ‖φ a v‖) ≤ B * S.card := by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using
        Finset.sum_le_sum (fun v hv => hφ a v hv)
    calc
      _ ≤ (E / A) * (B * S.card) := mul_le_mul_of_nonneg_left hs (div_nonneg hE hA.le)
      _ ≤ (E / A) * (B * (C * A)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcard hB) (div_nonneg hE hA.le)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ a : T, selectedResidueCellWeight q T V a * (B * E * C) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hpart a)
        (selectedResidueCellWeight_nonneg q T V a))
    _ = (∑ a : T, selectedResidueCellWeight q T V a) * (B * E * C) := (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [selectedResidueCellWeight_sum q T V hV hmass, one_mul]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedResidue_coefficient_tail {K X Y : Type*} [Fintype K] [Fintype X]
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern K X stride))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (window : Finset Y) (ψ : Y → ℂ) (test : cells → Y → ℂ)
    (error : cells → Y → ℝ) {A C E Cwin : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hψ : ∀ v ∈ window, ‖ψ v‖ ≤ C) (htest : ∀ a v, ‖test a v‖ ≤ 1)
    (herror : ∀ a v, error a v ≤ E) (hcard : (window.card : ℝ) ≤ Cwin * A) :
    (∑ t : cells × window,
      ‖(selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (A : ℂ)) *
        test t.1 t.2.val‖ * error t.1 t.2.val) ≤ C * E * Cwin := by
  have hφ (a : cells) (v : Y) (hv : v ∈ window) : ‖ψ v * test a v‖ ≤ C := by
    rw [norm_mul]
    exact (mul_le_mul (hψ v hv) (htest a v) (norm_nonneg _) hC).trans_eq (mul_one _)
  calc
    _ ≤ ∑ t : cells × window,
        ‖(selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (A : ℂ)) *
          test t.1 t.2.val‖ * E :=
      Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (herror t.1 t.2.val) (norm_nonneg _))
    _ = ∑ a : cells, selectedResidueCellWeight stride cells V a *
        ((E / A) * ∑ v ∈ window, ‖ψ v * test a v‖) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_coe_sort window (fun v => ‖ψ v * test a v‖),
        Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      simp only [norm_mul, norm_div, Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg (selectedResidueCellWeight_nonneg stride cells V a), abs_of_pos hA]
      ring
    _ ≤ _ := selectedResidue_site_mass_bound stride cells V hV hmass window
      (fun a v => ψ v * test a v) hA hE hC hφ hcard

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedResidue_coefficient_tail_of_window_mass {K X Y : Type*} [Fintype K] [Fintype X]
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern K X stride))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (window : Finset Y) (ψ : Y → ℂ) (test : cells → Y → ℂ)
    (error : cells → Y → ℝ) {A C E : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (hψ : ∀ w ∈ window, ‖ψ w‖ ≤ C) (htest : ∀ a w, ‖test a w‖ ≤ 1)
    (herror : ∀ a w, 0 ≤ error a w)
    (hmass : ∀ a, (∑ w ∈ window, error a w) ≤ E * A) :
    (∑ t : cells × window,
      ‖(selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (A : ℂ)) *
        test t.1 t.2.val‖ * error t.1 t.2.val) ≤ C * E := by
  have hcell (a : cells) :
      (∑ w : window, ‖(selectedResidueCellWeight stride cells V a : ℂ) *
        (ψ w.val / (A : ℂ)) * test a w.val‖ * error a w.val) ≤
      selectedResidueCellWeight stride cells V a * (C * E) := by
    let w := selectedResidueCellWeight stride cells V a
    have hw : 0 ≤ w := selectedResidueCellWeight_nonneg stride cells V a
    have hn (v : window) :
        ‖(w : ℂ) * (ψ v.val / (A : ℂ)) * test a v.val‖ ≤ w / A * C := by
      have ht : ‖ψ v.val‖ * ‖test a v.val‖ ≤ C :=
        (mul_le_mul (hψ v.val v.property) (htest a v.val) (norm_nonneg _) hC).trans_eq (mul_one C)
      calc
        _ = w / A * (‖ψ v.val‖ * ‖test a v.val‖) := by
          simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hw, abs_of_pos hA]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left ht (div_nonneg hw hA.le)
    calc
      _ ≤ ∑ v : window, (w / A * C) * error a v.val :=
        Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_right (hn v) (herror a v.val))
      _ = (w / A * C) * ∑ v ∈ window, error a v := by
        rw [← Finset.mul_sum, Finset.sum_coe_sort]
      _ ≤ (w / A * C) * (E * A) :=
        mul_le_mul_of_nonneg_left (hmass a) (mul_nonneg (div_nonneg hw hA.le) hC)
      _ = w * (C * E) := by field_simp [hA.ne']
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ a : cells, selectedResidueCellWeight stride cells V a * (C * E) :=
      Finset.sum_le_sum (fun a _ => hcell a)
    _ = _ := by rw [← Finset.sum_mul, selectedResidueCellWeight_sum stride cells V hV hZ, one_mul]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedReferenceJetMass
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem referenceJetEnvelope_anisotropic_volume {X : Type*} [Fintype X] {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x) (H T : X → ℝ)
    {W L : ℝ} (hL : L ≠ 0) (hscale : ∀ x, H x = (1 + W) * T x) :
    ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
      (∏ i, residueProfileWidth stride (referenceJetEnvelopeWidths (q := q) stride H) i) /
      (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) =
    ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
      (((1 + W) / L) ^ q) ^ Fintype.card X) *
      (∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i) := by
  rw [referenceJetEnvelope_volume stride hs H, physicalSpatial_uniform_volume H T hL hscale]
  simp only [Fintype.card_fin, mul_assoc]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedLongResidueProfile
namespace OAI

section

namespace Erdos3

theorem principalResidueLabel_eq_of_dvd {D α : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ}
    (y y₀ : PrincipalIntegerTuples B h α L) {q refined : ℕ}
    (hdiv : q ∣ refined)
    (hlabel : principalResidueLabel refined y = principalResidueLabel refined y₀) :
    principalResidueLabel q y = principalResidueLabel q y₀ := by
  exact integerResidueMatrix_reduce (fun j i => (y j i : ℤ))
    (fun j i => (y₀ j i : ℤ)) hdiv hlabel

namespace VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]


variable (u : PrincipalAxisTuples (B := B) (h := layerSamplerDegree I n) (α := α)
  (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v v₀ : PrincipalAxisTuples (B := B) (h := layerSamplerDegree I n) (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))

end VectorPolynomial
end Erdos3

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

local notation "sides" => allocatedPrincipalSides B U b S
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)

theorem allocatedResidueSpatialKernel_norm_le
    (hH : ∀ t, 0 < H t) (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (r : labels) (v : X → (Unit ⊕ Fin dim) → ℤ) (hv : v ∈ spatialWindow H 4) :
    ‖allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh r v‖ ≤
      ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
        anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X := by
  let ker := fun g => (0 : ℤ) + (x g none : ℤ)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker
    (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
  let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hp W S.value
    hW (Nat.cast_pos.mpr S.positive)
  obtain ⟨y, _hy⟩ := (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
    sides (allocatedPrincipalSides_pos B U b S)).exists_weight_pos
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hC := anisotropicSpatialDensityCap_nonneg selection hκ.le
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
  exact residueSpatialSite_norm_le _ _ modulus hperiod (fun _ : X => f) H (by norm_num) hmesh hC
    (fun _ => hf) (fun _ => principalSpatialResidueColumns modulus (fun _ => (0 : ℤ)) id r) v
    ((mem_spatialWindow_scaled_iff H hH 4 v).mp hv)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalExponentialCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable (q : ℕ) [NeZero q]

variable (δ : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable (q : ℕ) [NeZero q]

variable (δ : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
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

local notation "refined" => residueRefinedPeriod modulus q

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)


variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)
variable (href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
variable (Q : ℝ≥0) (hQ : 1 ≤ Q) (hratio : (1 + W) / (S.value : ℝ) ≤ Q)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
  pivotFullImage
    (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
    (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
variable (hmesh : 0 < mesh) {ε : ℝ} (hε : 0 ≤ ε) (hmargin : (3 + 2 * mesh) + 2 * ε ≤ 4)
variable (hsize : ∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ ε * trimmedSpatialRootScale τ N q t)
variable (htest : ∀ v, ‖test v‖ ≤ 1)



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedRecenteredProfileTerm_residue_weight
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple)
    (hwhole : principalResidueLabel refined
      (wholeReference (principalResidueLabel refined y)) = principalResidueLabel refined y) :
    allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile y =
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let r := principalResidueLabel refined y
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r
    ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
      ∑ v ∈ window,
        allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells test r a v *
          profile y (point (reconstruct a.val v)) := by
  have hcoarse := principalResidueLabel_eq_of_dvd _ _
    (show modulus ∣ residueRefinedPeriod modulus q from ⟨∏ t, q t, rfl⟩) hwhole
  simp only [allocatedRecenteredProfileTerm, allocatedRecenteredResidueWeight, hcoarse]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (modulus : ℕ) [NeZero modulus]
variable [NeZero (residueRefinedPeriod modulus stride)]

variable (δ : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

theorem allocatedRecenteredProfileTerm_selected_mean
    (law : FiniteProbabilityWeights fullTuple) (r : labels)
    (hlabel : ∀ y, law.weight y ≠ 0 → principalResidueLabel refined y = r)
    (hwhole : principalResidueLabel refined (wholeReference r) = r)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) :
    law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile) =
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r
    ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
      ∑ v ∈ window,
        allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
          N hW mesh base cells test r a v * law.complexMean (fun y => profile y (point (reconstruct a.val v))) := by
  dsimp only
  have hp (y) (hy : law.weight y ≠ 0) :=
    allocatedRecenteredProfileTerm_residue_weight (τ := τ) (ξ := ξ) B U b S X modulus q wholeReference x hM selection hx
      N hW mesh base cells point test profile y (by rw [hlabel y hy]; exact hwhole)
  have he := law.complexMean_congr_support (fun y hy => by
    simpa only [hlabel y hy] using hp y hy)
  refine he.trans ?_
  rw [FiniteProbabilityWeights.complexMean_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [FiniteProbabilityWeights.complexMean_mul_left]
  congr 1
  simp only [FiniteProbabilityWeights.complexMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro y _
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (modulus : ℕ) [NeZero modulus]
variable [NeZero (residueRefinedPeriod modulus stride)]

variable (δ : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (modulus : ℕ) [NeZero modulus]
variable [NeZero (residueRefinedPeriod modulus stride)]

variable (δ : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (modulus : ℕ) [NeZero modulus]
variable [NeZero (residueRefinedPeriod modulus stride)]

variable (δ : ℝ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRecenteredL1Source
namespace OAI

section

namespace Erdos3
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

variable {X K : Type*} [Fintype X] [Fintype K] {dim : ℕ}
variable (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
variable (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option K) X stride))
variable (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
variable (H T : X → ℝ) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
variable {Wsp Lsp : ℝ} (hLsp : 0 < Lsp) (hsc : ∀ x, H x = (1 + Wsp) * T x)
variable (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
variable (hprofile : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
local notation "Cube" => (X → (Unit ⊕ Fin dim) → ℤ)
local notation "window" => spatialWindow (α := Fin dim) H 4
local notation "scale" => ((∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (H x) (T x) Lsp i) : ℝ)
local notation "factor" => (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X
local notation "reconstruct" => (fun a : cells => physicalResidueReconstruction root D base
  (boundedColumnResidueRepresentative stride (Subtype.val a)) stride)
local notation "target" a => columnResiduePattern stride
  (standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative stride a)))
local notation "V₁" => referenceJetEnvelopeWidths (q := dim) stride H

include hs hV hZ hH hT hLsp hsc hrows hprofile in
theorem physicalReconstruction_weighted_sampled_error
    (ψ test : Cube → ℂ) {Cψ : ℝ} (hCψ : 0 ≤ Cψ)
    (hψ : ∀ w ∈ window, ‖ψ w‖ ≤ Cψ) (htest : ∀ w, ‖test w‖ ≤ 1)
    (error : Cube → ℝ) (he0 : ∀ w, 0 ≤ error w) {E : ℝ}
    (he : ∀ a : cells,
      (0 < ∑' z, selectedResidueSmoothWeight stride {target a.val} V₁ z) ∧
      selectedResidueDensityMass stride {target a.val} V₁
        (fun z => error (translatePhysicalCube base (standardPhysicalCubeOutput z))) ≤ E) :
    (∑ t : cells × window,
      ‖(selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val)‖ * error (reconstruct t.1 t.2.val)) ≤ Cψ * (factor * E) := by
  have hscale : 0 < scale := Finset.prod_pos (fun x _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hH x) (hT x) hLsp i))
  have hmass (a : cells) : (∑ w ∈ window, error (reconstruct a w)) ≤ (factor * E) * scale := by
    have hv := referenceJetEnvelopeWidths_pos (q := dim) stride hs H hH
    have hraw := physicalReconstruction_sum_le_sampled_mass stride hs root D a.val H hH hrows hprofile
      (fun w => error (translatePhysicalCube base w)) (fun w => he0 _) (he a).1
    have hvol := referenceJetEnvelope_anisotropic_volume (q := dim) stride hs H T hLsp.ne' hsc
    have hvol0 : 0 ≤ (3 / 2 : ℝ) ^ Fintype.card (Option (Fin dim) × X) *
        (∏ i, residueProfileWidth stride V₁ i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) :=
      div_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
        (Finset.prod_nonneg (fun i _ => (residueProfileWidth_pos stride V₁ hs hv i).le)))
        (pow_pos smoothProbabilityProfile_pos_zero _).le
    have hh := hraw.trans (mul_le_mul_of_nonneg_left (he a).2 hvol0)
    rw [hvol] at hh
    simp_rw [← physicalResidueReconstruction_translate root D base] at hh
    exact hh.trans_eq (by ring)
  exact selectedResidue_coefficient_tail_of_window_mass stride cells V hV hZ window ψ
    (fun a w => test (reconstruct a w)) (fun a w => error (reconstruct a w))
    hscale hCψ hψ (fun _ w => htest _) (fun _ w => he0 _) hmass

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

variable {X K : Type*} [Fintype X] [Fintype K] {dim : ℕ}
variable (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
variable (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option K) X stride))
variable (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
variable (H T : X → ℝ) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
variable {Wsp Lsp : ℝ} (hLsp : 0 < Lsp) (hsc : ∀ x, H x = (1 + Wsp) * T x)
variable (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
variable (hprofile : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
local notation "Cube" => (X → (Unit ⊕ Fin dim) → ℤ)
local notation "window" => spatialWindow (α := Fin dim) H 4
local notation "scale" => ((∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (H x) (T x) Lsp i) : ℝ)
local notation "factor" => (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X
local notation "reconstruct" => (fun a : cells => physicalResidueReconstruction root D base
  (boundedColumnResidueRepresentative stride (Subtype.val a)) stride)
local notation "target" a => columnResiduePattern stride
  (standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative stride a)))
local notation "V₁" => referenceJetEnvelopeWidths (q := dim) stride H

include hs hV hZ hH hT hLsp hsc hrows hprofile in
theorem physicalReconstruction_source_of_sampled_l1_and_uniform
    (ψ test f ideal model : Cube → ℂ) {Cψ : ℝ} (hCψ : 0 ≤ Cψ)
    (hψ : ∀ w ∈ window, ‖ψ w‖ ≤ Cψ) (htest : ∀ w, ‖test w‖ ≤ 1)
    {E κ ε : ℝ} (hε : 0 ≤ ε) (hH1 : ∀ x, 1 ≤ H x)
    (he : ∀ a : cells,
      (0 < ∑' z, selectedResidueSmoothWeight stride {target a.val} V₁ z) ∧
      selectedResidueDensityMass stride {target a.val} V₁
        (fun z => ‖f (translatePhysicalCube base (standardPhysicalCubeOutput z)) -
          ideal (translatePhysicalCube base (standardPhysicalCubeOutput z))‖) ≤ E)
    (happrox : ∀ w, ‖ideal w - model w‖ ≤ ε)
    (hsource : κ ≤ (∑ t : cells × window,
      (selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val) * f (reconstruct t.1 t.2.val)).re) :
    κ - Cψ * (factor * E + ((9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X) * ε) ≤
      (∑ t : cells × window,
        (selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
          test (reconstruct t.1 t.2.val) * model (reconstruct t.1 t.2.val)).re := by
  let c := fun t : cells × window =>
    (selectedResidueCellWeight stride cells V t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
      test (reconstruct t.1 t.2.val)
  let W := (9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
    (((1 + Wsp) / Lsp) ^ dim) ^ Fintype.card X
  have herr := physicalReconstruction_weighted_sampled_error stride hs root D base cells V hV hZ
    H T hH hT hLsp hsc hrows hprofile ψ test hCψ hψ htest
    (fun w => ‖f w - ideal w‖) (fun _ => norm_nonneg _) he
  have hscale : 0 < scale := Finset.prod_pos (fun x _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hH x) (hT x) hLsp i))
  have hmass := selectedResidue_coefficient_tail stride cells V hV hZ window ψ
    (fun a w => test (reconstruct a w)) (fun _ _ => (1 : ℝ)) hscale hCψ zero_le_one
    hψ (fun _ w => htest _) (fun _ _ => le_rfl)
    (show (Finset.card window : ℝ) ≤ W * scale by
      simpa only [W, Fintype.card_fin, show (2 * (4 : ℝ) + 1) = 9 by norm_num] using
        spatialWindow_card_anisotropic (α := Fin dim) H T hH1 (by norm_num : (0 : ℝ) ≤ 4) hLsp.ne' hsc)
  simp only [mul_one] at hmass
  have herror : (∑ t : cells × window, ‖c t‖ *
      ‖f (reconstruct t.1 t.2.val) - model (reconstruct t.1 t.2.val)‖) ≤
      Cψ * (factor * E + W * ε) := by
    calc
      _ ≤ ∑ t : cells × window, ‖c t‖ *
          (‖f (reconstruct t.1 t.2.val) - ideal (reconstruct t.1 t.2.val)‖ + ε) := by
        apply Finset.sum_le_sum
        intro t _
        exact mul_le_mul_of_nonneg_left
          ((norm_sub_le_norm_sub_add_norm_sub _ (ideal (reconstruct t.1 t.2.val)) _).trans
            (add_le_add le_rfl (happrox _))) (norm_nonneg _)
      _ = (∑ t : cells × window, ‖c t‖ *
          ‖f (reconstruct t.1 t.2.val) - ideal (reconstruct t.1 t.2.val)‖) +
          (∑ t : cells × window, ‖c t‖) * ε := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      _ ≤ Cψ * (factor * E) + (Cψ * W) * ε :=
        add_le_add herr (mul_le_mul_of_nonneg_right hmass hε)
      _ = _ := by ring
  have hn : ‖∑ t : cells × window, c t *
      (f (reconstruct t.1 t.2.val) - model (reconstruct t.1 t.2.val))‖ ≤
      Cψ * (factor * E + W * ε) := by
    exact (norm_sum_le _ _).trans (by simpa only [norm_mul] using herror)
  simp only [mul_sub, Finset.sum_sub_distrib] at hn
  have hr := (Complex.re_le_norm _).trans hn
  rw [Complex.sub_re] at hr
  change κ ≤ (∑ t : cells × window, c t * f (reconstruct t.1 t.2.val)).re at hsource
  change κ - Cψ * (factor * E + W * ε) ≤ _
  linarith only [hr, hsource]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory
open scoped BigOperators Classical

variable {X K : Type*} [Fintype X] [Fintype K] {dim : ℕ}
variable (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
variable (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option K) X stride))
variable (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
variable (H T : X → ℝ) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
variable {Wsp Lsp : ℝ} (hLsp : 0 < Lsp) (hsc : ∀ x, H x = (1 + Wsp) * T x)
variable (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
variable (hprofile : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
local notation "target" a => columnResiduePattern stride
  (standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative stride a)))
local notation "V₁" => referenceJetEnvelopeWidths (q := dim) stride H

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

theorem allocatedRecenteredSelectedMean_l1_source
    (law : FiniteProbabilityWeights fullTuple) (r : labels)
    (hlabel : ∀ y, law.weight y ≠ 0 → principalResidueLabel refined y = r)
    (hwhole : principalResidueLabel refined (wholeReference r) = r)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    (ideal model : EuclideanJetLayers U O → ℂ)
    (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (htest : ∀ w, ‖test w‖ ≤ 1) {κ δ Eerror ε : ℝ}
    (hsource : κ ≤ (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile)).re)
    (hε : 0 ≤ ε) (htrunc : ∀ z, ‖ideal z - model z‖ ≤ ε) :
    let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r)
    let D := allocatedPhysicalCubeDirections B U b S x (wholeReference r)
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let V₁ := referenceJetEnvelopeWidths (q := dim) q H
    let _A := (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i : ℝ)
    let C := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    (∀ z, 0 < V z) → (0 < ∑' z, selectedResidueSmoothWeight q cells V z) →
    (∀ t i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) →
    (∀ t, 1 ≤ H t) →
    (∀ a : cells,
      let target := columnResiduePattern q (standardPhysicalCubeFrame
        (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative q a.val)))
      (0 < ∑' z, selectedResidueSmoothWeight q {target} V₁ z) ∧
      selectedResidueDensityMass q {target} V₁ (fun z =>
        ‖law.complexMean (fun y => profile y (point (translatePhysicalCube base (standardPhysicalCubeOutput z)))) -
          ideal (point (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤ Eerror) →
    C * (volumeFactor * Eerror + ((9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X) * ε) ≤ δ →
    κ - δ ≤
      (∑ t : cells × window, (selectedResidueCellWeight q cells V t.1 : ℂ) *
        allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
          N hW mesh base cells test r t.1 t.2.val *
        model (point (allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r
          t.1.val t.2.val))).re := by
  intro root D H T V V₁ A C volumeFactor hV hZ hrows hprofile hH1 he hcost
  have hH (t) : 0 < H t := (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).1
  have hT (t) : 0 < T t := (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).2
  let ψ := allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh
    (principalResidueLabel modulus (wholeReference r))
  have hC : 0 ≤ C := pow_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (anisotropicSpatialDensityCap_nonneg selection (one_div_nonneg.mpr (Nat.cast_nonneg _)))) _
  have hψ : ∀ v ∈ window, ‖ψ v‖ ≤ C :=
    allocatedResidueSpatialKernel_norm_le B U b S x X hM selection hx modulus H hW mesh
      hH hbudget hmesh hperiod (principalResidueLabel modulus (wholeReference r))
  have hid := allocatedRecenteredProfileTerm_selected_mean (τ := τ) (ξ := ξ)
    B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test
    law r hlabel hwhole profile
  have hsource' : κ ≤ (∑ t : cells × window,
      (selectedResidueCellWeight q cells V t.1 : ℂ) * (ψ t.2.val / (A : ℂ)) *
        test (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative q t.1.val) q t.2.val) *
        law.complexMean (fun y => profile y (point
          (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative q t.1.val) q t.2.val)))).re := by
    rw [hid] at hsource
    rw [Fintype.sum_prod_type]
    convert hsource using 1
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum, ← Finset.sum_coe_sort window]
    apply Finset.sum_congr rfl
    intro v _
    dsimp only [allocatedRecenteredResidueWeight, allocatedWholeResidueReconstruction, ψ, A, root, D, H, T]
    ring
  have ht := physicalReconstruction_source_of_sampled_l1_and_uniform q hq root D base cells V hV hZ H T hH hT
    (Nat.cast_pos.mpr S.positive) (trimmedSpatial_scale_ratio hW N q) hrows hprofile
    ψ test (fun w => law.complexMean (fun y => profile y (point w)))
    (fun w => ideal (point w)) (fun w => model (point w))
    hC hψ htest hε hH1 he (fun w => htrunc _) hsource'
  have ht' := (sub_le_sub_left hcost κ).trans ht
  refine le_of_le_of_eq ht' ?_
  refine congrArg Complex.re ?_
  apply Finset.sum_congr rfl
  intro t _
  dsimp only [allocatedRecenteredResidueWeight, allocatedWholeResidueReconstruction, ψ, A, root, D, H, T]
  ring

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedRecenteredSelectedMean_l1_source.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedRecenteredSelectedMean_l1_source.{u_1, u_2, u_3, u_4, u_5, u_6}
