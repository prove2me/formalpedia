-- Prove2me | solution 1 for OAI.Erdos3.physicalBox_pair_kernel_grid_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:36:18.517493+00:00
-- url     : https://prove2.me/submissions/e6e31a1e-fbd0-4a11-b49c-550cc9f333bc

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B111
import Theorems.Thm_OAI_Erdos3_smooth_affinePairRowDensity_cap

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BinaryDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem binaryDensity_lipschitz {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → ℝ) (g : Y → ℝ) (C D L M : ℝ≥0)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (hg : ∀ y, g y ∈ Set.Icc (0 : ℝ) D)
    (hL : LipschitzWith L f) (hM : LipschitzWith M g) :
    LipschitzWith (D * L + C * M) (binaryDensity f g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hdx : dist x.1 y.1 ≤ dist x y := le_max_left _ _
  have hdy : dist x.2 y.2 ≤ dist x y := le_max_right _ _
  have hleft : |f x.1 - f y.1| ≤ (L : ℝ) * dist x y := by
    have h := hL.dist_le_mul x.1 y.1
    rw [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdx L.coe_nonneg)
  have hright : |g x.2 - g y.2| ≤ (M : ℝ) * dist x y := by
    have h := hM.dist_le_mul x.2 y.2
    rw [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdy M.coe_nonneg)
  rw [Real.dist_eq]
  change |f x.1 * g x.2 - f y.1 * g y.2| ≤ _
  calc
    |f x.1 * g x.2 - f y.1 * g y.2| =
        |(f x.1 - f y.1) * g x.2 + f y.1 * (g x.2 - g y.2)| := by congr 1; ring
    _ ≤ |(f x.1 - f y.1) * g x.2| + |f y.1 * (g x.2 - g y.2)| := abs_add_le _ _
    _ = |f x.1 - f y.1| * g x.2 + f y.1 * |g x.2 - g y.2| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hg _).1, abs_of_nonneg (hf _).1]
    _ ≤ ((L : ℝ) * dist x y) * D + C * ((M : ℝ) * dist x y) :=
      add_le_add (mul_le_mul hleft (hg _).2 (hg _).1 (mul_nonneg L.coe_nonneg dist_nonneg))
        (mul_le_mul (hf _).2 hright (abs_nonneg _) C.coe_nonneg)
    _ = (D * L + C * M : ℝ≥0) * dist x y := by push_cast; ring

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

theorem splitSmoothProductProfile_lipschitz (J I : Type*) [Fintype J] [Fintype I] :
    LipschitzWith (((Fintype.card J + Fintype.card I : ℕ) : ℝ≥0) * probabilityProfileLipschitz)
      (splitSmoothProductProfile J I) := by
  have h := binaryDensity_lipschitz (smoothProductProfile J) (smoothProductProfile I) 1 1
    (Fintype.card J * probabilityProfileLipschitz) (Fintype.card I * probabilityProfileLipschitz)
    (smoothProductProfile_range J) (smoothProductProfile_range I)
    (smoothProductProfile_lipschitz J) (smoothProductProfile_lipschitz I)
  have he : binaryDensity (smoothProductProfile J) (smoothProductProfile I) =
      splitSmoothProductProfile J I := by funext p; rfl
  rw [← he]
  simpa only [one_mul, Nat.cast_add, add_mul] using h

theorem splitSmoothProductProfile_zero_outside (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) (hp : 1 < ‖p‖) : splitSmoothProductProfile J I p = 0 := by
  change 1 < max ‖p.1‖ ‖p.2‖ at hp
  rcases lt_max_iff.mp hp with h | h
  · exact mul_eq_zero_of_left (smoothProductProfile_zero_outside J p.1 h) _
  · exact mul_eq_zero_of_right _ (smoothProductProfile_zero_outside I p.2 h)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem physicalBoxCell_eq_iff (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (x : translatedIntegerBox lo N) (c : ∀ i, (P i).Label) :
    physicalBoxCell lo N P x = c ↔ ∀ i,
      intervalCellLower (lo i) (P i) (c i) ≤ x.val i ∧ x.val i < intervalCellUpper (lo i) (P i) (c i) := by
  change (fun i => intervalResidueCell (lo i) (P i) 1 0 ((physicalBoxUnitResidueEquiv lo N x) i)) = c ↔ _
  rw [funext_iff]
  exact forall_congr' (fun i => intervalResidueCell_eq_iff (lo i) (P i) (hstep i) 1 0 _ (c i))

theorem physicalBoxCell_distance_lower (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (x : translatedIntegerBox lo N) (i : I) :
    |(x.val i : ℝ) - (intervalCellLower (lo i) (P i) (physicalBoxCell lo N P x i) : ℝ)| ≤
      ((P i).length (physicalBoxCell lo N P x i) : ℝ) := by
  have hi := (physicalBoxCell_eq_iff lo N P hstep x _).mp rfl i
  have hlo : (intervalCellLower (lo i) (P i) (physicalBoxCell lo N P x i) : ℝ) ≤ x.val i := by
    exact_mod_cast hi.1
  have hhi : (x.val i : ℝ) < (intervalCellLower (lo i) (P i) (physicalBoxCell lo N P x i) : ℝ) +
      ((P i).length (physicalBoxCell lo N P x i) : ℝ) := by exact_mod_cast hi.2
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PivotKernelAllowances
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem pivotOutputDensity_lipschitz {I J : Type*} [Fintype I] [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} (R K : ℝ≥0) (hf : LipschitzWith K f)
    (hs : ∀ p, (R : ℝ) < ‖p‖ → f p = 0) :
    LipschitzWith (pivotKernelLip J A R K) (pivotOutputDensity A B f) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.dist_eq, dist_eq_norm]
  apply (pivotOutputDensity_output_bound A B hf R.coe_nonneg hs v w).trans_eq
  change _ = (inverseJacobian A * (K : ℝ) * (2*(R : ℝ))^Fintype.card J *
    ‖A.symm.toContinuousLinearMap‖) * ‖v-w‖
  ring

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

end Erdos3

namespace Erdos3

open scoped Matrix Classical

end Erdos3

namespace Erdos3

open scoped Classical

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped Matrix

theorem normalized_affinePairPivot {J : Type*} (t u : J → ℤ) (k : J)
    {H L : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) :
    normalizedIntegerPivot (affinePairPivot t u k) (affinePairScale H L) (fun _ => H) =
      !![1, (t k : ℝ) / L; 1, (u k : ℝ) / L] := by
  ext i j
  rw [normalizedIntegerPivot_entry]
  fin_cases i <;> fin_cases j <;> simp [affinePairPivot, affinePairScale, hH] <;> field_simp

theorem normalized_affinePairPivot_det {J : Type*} (t u : J → ℤ) (k : J)
    {H L : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) :
    (normalizedIntegerPivot (affinePairPivot t u k) (affinePairScale H L) (fun _ => H)).det =
      ((u k - t k : ℤ) : ℝ) / L := by
  rw [normalized_affinePairPivot t u k hH hL]
  simp [Matrix.det_fin_two, sub_div]

theorem normalized_affinePairPivot_inverse {J : Type*} (t u : J → ℤ) (k : J)
    {H L C κ : ℝ} (hH : H ≠ 0) (hL : L ≠ 0) (hC : 1 ≤ C) (hκ : 0 < κ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) :
    ‖(matrixSupCLM (normalizedIntegerPivot (affinePairPivot t u k)
      (affinePairScale H L) (fun _ => H))).inverse‖ ≤ 4 * C / κ := by
  have hentry : ∀ i j, |normalizedIntegerPivot (affinePairPivot t u k)
      (affinePairScale H L) (fun _ => H) i j| ≤ C := by
    rw [normalized_affinePairPivot t u k hH hL]
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using hC
    · exact ht
    · simpa using hC
    · exact hu
  have hd : κ ≤ |(normalizedIntegerPivot (affinePairPivot t u k)
      (affinePairScale H L) (fun _ => H)).det| := by
    rwa [normalized_affinePairPivot_det t u k hH hL]
  have h := (matrixSupCLM_inverse_norm_le _ (zero_le_one.trans hC) hentry hκ hd).2
  norm_num [mul_div_assoc, ← mul_assoc] at h
  simpa only [mul_div_assoc] using h

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSmoothPairLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem smooth_affinePairRowDensity_lipschitz {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    {H L C κ : ℝ} (hH : 0 < H) (hL : 0 < L) (hC : 1 ≤ C) (hκ : 0 < κ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) :
    LipschitzWith (Real.toNNReal (2 * (4 * C / κ) ^ 3 * (smoothPairRowLipschitz k : ℝ) *
      (2 : ℝ) ^ Fintype.card {j : J // j ≠ k}))
      (affinePairRowDensity t u k hne H L hH hL
        (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2))) := by
  have hA : (affinePairPivot t u k).det ≠ 0 := by rwa [affinePairPivot_det]
  let e := normalizedPivotEquiv (affinePairPivot t u k) hA (affinePairScale H L)
    (fun _ => H) (affinePairScale_pos hH hL) (fun _ => hH)
  let b := matrixSupCLM (normalizedIntegerColumns (affinePairFree t u k) (fun _ => H / L) (fun _ => H))
  have hU : 0 ≤ 4 * C / κ := div_nonneg (by linarith) hκ.le
  have hinv : ‖e.symm.toContinuousLinearMap‖ ≤ 4 * C / κ := by
    dsimp only [e]
    rw [normalizedPivotEquiv_inverse_eq]
    exact normalized_affinePairPivot_inverse t u k hH.ne' hL.ne' hC hκ ht hu hgap
  have hLip : LipschitzWith (smoothPairRowLipschitz k)
      (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) := by
    simpa only [smoothPairRowLipschitz, Fintype.card_fin] using
      splitSmoothProductProfile_lipschitz {j : J // j ≠ k} (Fin 2)
  have h := pivotOutputDensity_lipschitz e b 1 (smoothPairRowLipschitz k) hLip
    (splitSmoothProductProfile_zero_outside _ _)
  apply h.weaken
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ (by positivity)]
  change inverseJacobian e * (smoothPairRowLipschitz k : ℝ) * (2 * 1) ^ Fintype.card {j : J // j ≠ k} *
    ‖e.symm.toContinuousLinearMap‖ ≤ _
  rw [mul_one]
  have hj := inverseJacobian_le_norm_bound e hinv
  norm_num at hj
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hj (smoothPairRowLipschitz k).coe_nonneg)
    (by positivity : 0 ≤ (2 : ℝ) ^ Fintype.card {j : J // j ≠ k})
  apply (mul_le_mul hm hinv (norm_nonneg _) (by positivity)).trans_eq
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SmoothPairKernel
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem smoothPairProductDensity_regularity {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) (L : ℝ) (hH : ∀ i, 0 < H i) (hL : 0 < L)
    {C κ : ℝ} (hC : 1 ≤ C) (hκ : 0 < κ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) :
    let B : ℝ≥0 := Real.toNNReal (1 + 2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k})
    let K : ℝ≥0 := Real.toNNReal (2 * (4 * C / κ) ^ 3 * (smoothPairRowLipschitz k : ℝ) *
      2 ^ Fintype.card {j : J // j ≠ k})
    (∀ y, |smoothPairProductDensity t u k hne H L hH hL y| ≤ (B : ℝ) ^ Fintype.card I) ∧
      LipschitzWith (Fintype.card I * K * B ^ Fintype.card I)
        (smoothPairProductDensity t u k hne H L hH hL) := by
  dsimp only
  let B : ℝ≥0 := Real.toNNReal (1 + 2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k})
  let K : ℝ≥0 := Real.toNNReal (2 * (4 * C / κ) ^ 3 * (smoothPairRowLipschitz k : ℝ) *
    2 ^ Fintype.card {j : J // j ≠ k})
  have hB : 1 ≤ B := by
    apply NNReal.coe_le_coe.mp
    dsimp only [B]
    rw [Real.coe_toNNReal _ (by positivity)]
    simp only [NNReal.coe_one]
    exact le_add_of_nonneg_right (by positivity)
  have hlip (i : I) : LipschitzWith K (fun y : I → Fin 2 → ℝ =>
      affinePairRowDensity t u k hne (H i) L (hH i) hL
        (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) (y i)) := by
    have h := smooth_affinePairRowDensity_lipschitz t u k hne (hH i) hL hC hκ ht hu hgap
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (h.dist_le_mul (x i) (y i)).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) K.coe_nonneg)
  have hcap (i : I) (y : I → Fin 2 → ℝ) :
      |affinePairRowDensity t u k hne (H i) L (hH i) hL
        (splitSmoothProductProfile {j : J // j ≠ k} (Fin 2)) (y i)| ≤ B := by
    have h := smooth_affinePairRowDensity_cap t u k hne (hH i) hL hC hκ ht hu hgap (y i)
    dsimp only [B]
    rw [Real.coe_toNNReal _ (by positivity)]
    linarith
  exact bounded_lipschitz_real_prod _ hB hlip hcap

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SmoothPairPhysicalGrid
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem normalized_integer_pair_dist {I : Type*} [Fintype I]
    (H : I → ℝ) (hH : ∀ i, 0 < H i) (v w c : I → Fin 2 → ℤ)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ i j, |(v i j : ℝ) - (w i j : ℝ)| ≤ ρ * H i) :
    dist (fun i j => ((v i j - c i j : ℤ) : ℝ) / H i)
      (fun i j => ((w i j - c i j : ℤ) : ℝ) / H i) ≤ ρ := by
  apply (dist_pi_le_iff hρ).mpr
  intro i
  apply (dist_pi_le_iff hρ).mpr
  intro j
  rw [Real.dist_eq]
  have heq : ((v i j - c i j : ℤ) : ℝ) / H i -
      ((w i j - c i j : ℤ) : ℝ) / H i = ((v i j : ℝ) - (w i j : ℝ)) / H i := by
    push_cast
    ring
  rw [heq, abs_div, abs_of_pos (hH i)]
  exact (div_le_iff₀ (hH i)).mpr (h i j)

theorem shiftedPairLocationKernel_grid_error {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) (L : ℝ) (hH : ∀ i, 0 < H i) (hL : 0 < L)
    {C κ ρ : ℝ} (hC : 1 ≤ C) (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (b : Option J × I → ℤ) (x y x' y' : I → ℤ)
    (hx : ∀ i, |(x i : ℝ) - (x' i : ℝ)| ≤ ρ * H i)
    (hy : ∀ i, |(y i : ℝ) - (y' i : ℝ)| ≤ ρ * H i) :
    |shiftedPairLocationKernel t u k hne H L hH hL b x y -
      shiftedPairLocationKernel t u k hne H L hH hL b x' y'| ≤
      (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ := by
  have hd := normalized_integer_pair_dist H hH (affinePairRowsOfLocations (x, y))
    (affinePairRowsOfLocations (x', y')) (smoothAffinePairRows t u b) hρ (fun i j => by
      fin_cases j
      · exact hx i
      · exact hy i)
  have hlip : LipschitzWith (smoothPairKernelLip (Fintype.card I) k C κ)
      (smoothPairProductDensity t u k hne H L hH hL) :=
    (smoothPairProductDensity_regularity t u k hne H L hH hL hC hκ ht hu hgap).2
  exact (hlip.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left hd (NNReal.coe_nonneg _))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PhysicalBoxKernel
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem physicalBox_pair_kernel_grid_error {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) (L : ℝ) (hH : ∀ i, 0 < H i) (hL : 0 < L)
    {C κ ρ : ℝ} (hC : 1 ≤ C) (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) (b : Option J × I → ℤ)
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1)
    (hlength : ∀ i c, ((P i).length c : ℝ) ≤ ρ * H i)
    (x y : translatedIntegerBox lo N) :
    |shiftedPairLocationKernel t u k hne H L hH hL b x.val y.val -
      shiftedPairLocationKernel t u k hne H L hH hL b
        (fun i => intervalCellLower (lo i) (P i) (physicalBoxCell lo N P x i))
        (fun i => intervalCellLower (lo i) (P i) (physicalBoxCell lo N P y i))| ≤
      (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ := by
  exact shiftedPairLocationKernel_grid_error t u k hne H L hH hL hC hκ hρ ht hu hgap b _ _ _ _
    (fun i => (physicalBoxCell_distance_lower lo N P hstep x i).trans (hlength i _))
    (fun i => (physicalBoxCell_distance_lower lo N P hstep y i).trans (hlength i _))

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.physicalBox_pair_kernel_grid_error.{u_1, u_2} := @OAI.Erdos3.physicalBox_pair_kernel_grid_error.{u_1, u_2}
