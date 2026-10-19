-- Prove2me | solution 1 for OAI.Erdos3.goodScalarKernelTuple_anisotropic_error_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:12:48.517435+00:00
-- url     : https://prove2.me/submissions/4ed91bc8-3016-4ac3-9519-73f454b040f7

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B113
import Definitions.Def_OAIE3v2B162
import Theorems.Thm_OAI_Erdos3_normalizedIntegerImage_polynomial_error_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

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

theorem residueLatticeImage_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    L.toAddSubgroup.index ≤ m ^ Fintype.card I := by
  have h := residueLatticeImage_card_mul_index L m hperiod
  have hpos := Nat.card_pos (α := residueLatticeImage L m)
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixSupInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem matrixSupCLM_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (x : κ → ℝ) : matrixSupCLM A x = A.mulVec x := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PivotDeterminantBudget
namespace OAI

section

namespace Erdos3

theorem integerPivot_det_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) {H : ℝ} (hA : ∀ i j, |(A i j : ℝ)| ≤ H) :
    (A.det.natAbs : ℝ) ≤ (Fintype.card I).factorial * H ^ Fintype.card I := by
  have hd : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) A).symm
  have h := matrix_det_abs_le_uniform_bound (A.map (Int.castRingHom ℝ)) hA
  rw [hd] at h
  simpa only [Nat.cast_natAbs, Int.cast_abs] using h

theorem integerPivot_polynomial_period_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) {C L : ℝ} (h : ℕ)
    (hA : ∀ i j, |(A i j : ℝ)| ≤ C * L ^ h) :
    (A.det.natAbs : ℝ) ≤
      ((Fintype.card I).factorial * C ^ Fintype.card I) * L ^ (h * Fintype.card I) := by
  have hb := integerPivot_det_bound A hA
  simpa only [mul_pow, ← pow_mul, mul_assoc] using hb

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

theorem splitInputProfile_integral (f : (J → ℝ) × (I → ℝ) → ℝ) :
    (∫ x, splitInputProfile f x) = ∫ p, f p :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)).integral_comp
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)).measurableEmbedding f

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem smoothProductProfile_contDiff (I : Type*) [Fintype I] :
    ContDiff ℝ ∞ (smoothProductProfile I) := by
  rw [smoothProductProfile_eq_cutoff]
  exact contDiff_coordinateBoxCutoff _ smoothProbabilityProfile_contDiff 1

theorem smoothProductProfile_norm_le (I : Type*) [Fintype I] (x : I → ℝ) :
    ‖smoothProductProfile I x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (smoothProductProfile_range I x).1]
  exact (smoothProductProfile_range I x).2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RootDifferenceMatrix
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem rootDifferenceMatrix_mulVec {I J R : Type*} [Fintype J] [CommRing R]
    (root : J → R) (D : Matrix I J R) (x : R) (v : J → R) :
    rootDifferenceMatrix root D *ᵥ Sum.elim (fun _ : Unit => x) v =
      Sum.elim (fun _ : Unit => x + ∑ j, root j * v j) (D *ᵥ v) := by
  funext i
  cases i with
  | inl i =>
    cases i
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, rootDifferenceMatrix, Matrix.fromBlocks]
  | inr i => simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, rootDifferenceMatrix, Matrix.fromBlocks]

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

theorem selectedSpatial_fromCols {I J R : Type*} [Fintype I] [CommRing R]
    (root : J → R) (D : Matrix I J R) (s : I ↪ J) :
    Matrix.fromCols (selectedSpatialPivot root D s) (selectedSpatialFreeColumns root D s) =
      (rootDifferenceMatrix root D).submatrix id (selectedSpatialColumnEquiv s) := by
  ext i j
  cases j with
  | inl j => cases j <;> cases i <;> rfl
  | inr j => cases i <;> rfl

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

omit [Fintype I] [Fintype J] [Fintype N] in
theorem splitFreeColumns_apply (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (C : (N → ℝ) →L[ℝ] (I → ℝ)) (y : J ⊕ N → ℝ) :
    splitFreeColumns B C y = B (fun j => y (.inl j)) + C (fun n => y (.inr n)) := rfl

omit [Fintype I] [Fintype J] [Fintype N] in
theorem splitFreeProfile_continuous {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (splitFreeProfile f g) := by
  unfold splitFreeProfile
  fun_prop

theorem splitFreeProfile_slice_integrable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (v : I → ℝ) :
    Integrable (fun p : (J → ℝ) × (N → ℝ) =>
      f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2) := by
  have hc : Continuous (fun p : (J → ℝ) × (N → ℝ) =>
      f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2) := by fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : (J → ℝ) × (N → ℝ)) (max R S))
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  apply hp
  have heq : ‖Sum.elim p.1 p.2‖ = ‖p‖ := (splitCoordinates_norm (Sum.elim p.1 p.2)).symm
  have hz := splitFreeProfile_zero_outside hfs hgs
    (Sum.elim p.1 p.2, A.symm (v - (B p.1 + C p.2)))
    (h.trans_le (heq ▸ norm_fst_le
      (Sum.elim p.1 p.2, A.symm (v - (B p.1 + C p.2)))))
  exact hz

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {I J N : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]

theorem normalizedIntegerColumns_fromCols (B : Matrix I J ℤ) (C : Matrix I N ℤ)
    (T : J → ℝ) (Q : N → ℝ) (P : I → ℝ) :
    normalizedIntegerColumns (Matrix.fromCols B C) (Sum.elim T Q) P =
      Matrix.fromCols (normalizedIntegerColumns B T P) (normalizedIntegerColumns C Q P) := by
  ext i k
  cases k <;> simp [normalizedIntegerColumns_entry]

omit [DecidableEq I] [DecidableEq J] [DecidableEq N] in
theorem matrixSupCLM_fromCols (B : Matrix I J ℝ) (C : Matrix I N ℝ) :
    matrixSupCLM (Matrix.fromCols B C) = splitFreeColumns (matrixSupCLM B) (matrixSupCLM C) := by
  apply ContinuousLinearMap.ext
  intro y
  rw [matrixSupCLM_apply, splitFreeColumns_apply, matrixSupCLM_apply, matrixSupCLM_apply]
  exact Matrix.fromCols_mulVec B C y

theorem normalizedIntegerColumns_split (B : Matrix I J ℤ) (C : Matrix I N ℤ)
    (T : J → ℝ) (Q : N → ℝ) (P : I → ℝ) :
    matrixSupCLM (normalizedIntegerColumns (Matrix.fromCols B C) (Sum.elim T Q) P) =
      splitFreeColumns (matrixSupCLM (normalizedIntegerColumns B T P))
        (matrixSupCLM (normalizedIntegerColumns C Q P)) := by
  rw [normalizedIntegerColumns_fromCols, matrixSupCLM_fromCols]

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

theorem smoothSplitProfile_integral (J I : Type*) [Fintype J] [Fintype I] :
    (∫ p, smoothSplitProfile J I p) = 1 := by
  change (∫ p : (J → ℝ) × (I → ℝ), smoothProductProfile J p.1 * smoothProductProfile I p.2
    ∂(volume.prod volume)) = 1
  rw [integral_prod_mul, smoothProductProfile_integral, smoothProductProfile_integral, one_mul]

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

theorem splitFreeProfile_smooth (J I N : Type*) [Fintype J] [Fintype I] [Fintype N] :
    splitFreeProfile (smoothSplitProfile J I) (smoothProductProfile N) =
      smoothSplitProfile (J ⊕ N) I := by
  funext p
  have h := smoothProductProfile_sum J N (fun j => p.1 (.inl j)) (fun n => p.1 (.inr n))
  have he : Sum.elim (fun j => p.1 (.inl j)) (fun n => p.1 (.inr n)) = p.1 := by
    funext k
    cases k <;> rfl
  rw [he] at h
  simp only [splitFreeProfile, smoothSplitProfile, h]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledInputProbability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem scaledInputPMF_apply (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T)
    (p : (I → ℤ) × (J → ℤ)) :
    (scaledInputPMF f hf0 S T hS hT hsupport hM p).toReal =
      scaledIntegerWeight f S T p / scaledInputWeightSum f S T :=
  realWeightPMF_apply _ _ _ _ p

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SmoothSplitSampling
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem smoothCoefficientPMF_apply (S : ℝ) (hS : 0 < S) (k : ℤ) :
    (smoothCoefficientPMF S hS k).toReal = smoothProbabilityProfile ((k : ℝ) / S) / smoothSampleSum S :=
  realWeightPMF_apply _ _ _ _ k

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothProductPMF_apply {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) (z : I → ℤ) :
    (smoothProductPMF S hS z).toReal = ∏ i, (smoothCoefficientPMF (S i) (hS i) (z i)).toReal := by
  rw [smoothProductPMF, realWeightPMF_apply, smoothProductSamples_sum S hS]
  simp only [smoothProductProfile, smoothCoefficientPMF_apply, Finset.prod_div_distrib]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothSplit_inputPMF_apply {I J : Type*} [Fintype I] [Fintype J]
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    (p : (I → ℤ) × (J → ℤ)) :
    (scaledInputPMF (smoothSplitProfile J I) (fun p => (smoothSplitProfile_range J I p).1)
      S T hS hT (smoothSplitProfile_zero_outside J I) (smoothSplit_mass_pos S T hS hT) p).toReal =
      (∏ i, (smoothCoefficientPMF (S i) (hS i) (p.1 i)).toReal) *
        (∏ j, (smoothCoefficientPMF (T j) (hT j) (p.2 j)).toReal) := by
  rw [scaledInputPMF_apply, smoothSplit_weight_sum S T hS hT]
  simp only [scaledIntegerWeight, smoothSplitProfile, smoothProductProfile,
    smoothCoefficientPMF_apply, Finset.prod_div_distrib, div_mul_div_comm]
  rw [mul_comm (∏ j, smoothProbabilityProfile ((p.2 j : ℝ) / T j))]

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

theorem hasBoundedScalarPeriod_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (B : ℕ) (h : HasBoundedScalarPeriod L B) :
    L.toAddSubgroup.index ≤ B ^ Fintype.card I := by
  obtain ⟨a, ha, haB, hperiod⟩ := h
  let : NeZero a := ⟨ha.ne'⟩
  exact (residueLatticeImage_index_le L a hperiod).trans (Nat.pow_le_pow_left haB _)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RootDifferencePeriod
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem rootDifferenceMatrix_period {I J : Type*} [Fintype I] [Fintype J]
    (root : J → ℤ) (D : Matrix I J ℤ) (a : ℤ)
    (hperiod : integerScalarLattice I a ≤ D.mulVecLin.range) :
    integerScalarLattice (Unit ⊕ I) a ≤ (rootDifferenceMatrix root D).mulVecLin.range := by
  rintro y ⟨z, rfl⟩
  have hz : a • (fun i => z (Sum.inr i)) ∈ integerScalarLattice I a :=
    ⟨fun i => z (Sum.inr i), rfl⟩
  obtain ⟨v, hv⟩ := hperiod hz
  refine ⟨Sum.elim (fun _ : Unit => a * z (Sum.inl ()) - ∑ j, root j * v j) v, ?_⟩
  change rootDifferenceMatrix root D *ᵥ _ = a • z
  rw [rootDifferenceMatrix_mulVec]
  funext i
  cases i with
  | inl i => cases i; simp
  | inr i => exact congrFun hv i

theorem rootDifferenceMatrix_bounded_period {I J : Type*} [Fintype I] [Fintype J]
    (root : J → ℤ) (D : Matrix I J ℤ) {B : ℕ}
    (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B) :
    HasBoundedScalarPeriod (rootDifferenceMatrix root D).mulVecLin.range B := by
  obtain ⟨a, ha, haB, hp⟩ := hperiod
  exact ⟨a, ha, haB, rootDifferenceMatrix_period root D (a : ℤ) hp⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedImageMask
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

theorem maskedIntegerImageDensity_error {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (P : I → ℝ) (f g : (I → ℝ) → ℝ)
    {G ε : ℝ} (hε : 0 ≤ ε)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hfg : ∀ x, |f x - g x| ≤ ε) (v : I → ℤ) :
    |maskedIntegerImageDensity A B P f v - maskedIntegerImageDensity A B P g v| ≤ G * ε := by
  classical
  by_cases hv : v ∈ pivotFullImage A B
  · simp only [maskedIntegerImageDensity, hv, ite_true, ← mul_sub, abs_mul]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (pivotFullImage A B).toAddSubgroup.index from Nat.cast_nonneg _)]
    exact mul_le_mul hindex (hfg _) (abs_nonneg _) ((Nat.cast_nonneg _).trans hindex)
  · simp only [maskedIntegerImageDensity, hv, ite_false, sub_self, abs_zero]
    exact mul_nonneg ((Nat.cast_nonneg _).trans hindex) hε

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PivotDensitySupport
namespace OAI


namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

theorem splitPivotDensity_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (v : I → ℝ) :
    pivotOutputDensity A (splitFreeColumns B C) (splitFreeProfile f g) v =
      ∫ n, g n * pivotOutputDensity A B f (v - C n) := by
  let F : (J → ℝ) × (N → ℝ) → ℝ := fun p =>
    f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2
  have hi : Integrable F := splitFreeProfile_slice_integrable A B C hf hg hfs hgs v
  rw [pivotOutputDensity_formula]
  change inverseJacobian A * (∫ y, splitInputProfile F y) = _
  rw [splitInputProfile_integral, Measure.volume_eq_prod, integral_prod_symm _ hi,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with n
  have heq (y : J → ℝ) : v - (B y + C n) = (v - C n) - B y := by abel
  simp only [F, heq, integral_mul_const, pivotOutputDensity_formula]
  ring

theorem splitPivotDensity_displacement (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : Continuous g) {R S δ : ℝ} (hR : 0 ≤ R)
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1)
    (hmove : ∀ n, g n ≠ 0 → ‖C n‖ ≤ δ) (v : I → ℝ) :
    |pivotOutputDensity A (splitFreeColumns B C) (splitFreeProfile f g) v -
      pivotOutputDensity A B f v| ≤
        (inverseJacobian A * (2 * R) ^ Fintype.card J * K *
          ‖A.symm.toContinuousLinearMap‖) * δ := by
  let L := inverseJacobian A * (2 * R) ^ Fintype.card J * K * ‖A.symm.toContinuousLinearMap‖
  have hL : 0 ≤ L := by
    have hJ := inverseJacobian_pos A
    dsimp [L]
    positivity
  have hd : Continuous (pivotOutputDensity A B f) := by
    have hl : LipschitzWith (Real.toNNReal L) (pivotOutputDensity A B f) := by
      apply LipschitzWith.of_dist_le'
      intro u w
      simpa only [dist_eq_norm, Real.norm_eq_abs, L] using
        pivotOutputDensity_output_bound A B hf hR hfs u w
    exact hl.continuous
  have hi := compactBox_integrable
    (fun n => g n * pivotOutputDensity A B f (v - C n))
    (by fun_prop) S (fun n hn => by rw [hgs n hn, zero_mul])
  have hgi := compactBox_integrable g hg S hgs
  have hc := hgi.mul_const (pivotOutputDensity A B f v)
  have heq : (∫ n, g n * pivotOutputDensity A B f v) = pivotOutputDensity A B f v := by
    rw [integral_mul_const, hgmass, one_mul]
  rw [splitPivotDensity_formula A B C hf.continuous hg hfs hgs v, ← heq, ← integral_sub hi hc]
  have hb : ∀ n, ‖g n * pivotOutputDensity A B f (v - C n) -
      g n * pivotOutputDensity A B f v‖ ≤ g n * (L * δ) := by
    intro n
    by_cases hn : g n = 0
    · simp [hn]
    · rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hg0 n), Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (hg0 n)
      apply (pivotOutputDensity_output_bound A B hf hR hfs (v - C n) v).trans
      have hdif : (v - C n) - v = -(C n) := by abel
      rw [hdif, norm_neg]
      exact mul_le_mul_of_nonneg_left (hmove n hn) hL
  have ht := norm_integral_le_of_norm_le (hgi.mul_const (L * δ)) (Filter.Eventually.of_forall hb)
  rw [integral_mul_const, hgmass, one_mul] at ht
  simpa only [Real.norm_eq_abs] using ht

end Erdos3


namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem spatialKernelErrorConstant_nonneg (j d : ℕ) {U R : ℝ} (K : ℝ≥0)
    (hU : 0 ≤ U) (hR : 0 ≤ R) : 0 ≤ spatialKernelErrorConstant j d U R K := by
  unfold spatialKernelErrorConstant
  positivity

theorem supported_column_displacement {I N : Type*} [Fintype I] [Fintype N]
    (C : (N → ℝ) →L[ℝ] (I → ℝ)) (g : (N → ℝ) → ℝ) {R δ : ℝ}
    (hgs : ∀ n, R < ‖n‖ → g n = 0) (hC : ‖C‖ * R ≤ δ)
    (n : N → ℝ) (hn : g n ≠ 0) : ‖C n‖ ≤ δ := by
  have hnorm : ‖n‖ ≤ R := by
    by_contra! h
    exact hn (hgs n h)
  exact (C.le_opNorm n).trans ((mul_le_mul_of_nonneg_left hnorm (norm_nonneg C)).trans hC)

theorem normalizedSplitDensity_displacement {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (C : Matrix I N ℤ)
    (S P : I → ℝ) (T : J → ℝ) (Q : N → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : Continuous g) {R Rn δ U : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, Rn < ‖n‖ → g n = 0)
    (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hmove : ∀ n, g n ≠ 0 → ‖matrixSupCLM (normalizedIntegerColumns C Q P) n‖ ≤ δ)
    (v : I → ℝ) :
    |normalizedFiberDensity A hA (Matrix.fromCols B C) S P (Sum.elim T Q) hS hP
        (splitFreeProfile f g) v - normalizedFiberDensity A hA B S P T hS hP f v| ≤
      spatialKernelErrorConstant (Fintype.card I) (Fintype.card J) U R K * δ := by
  unfold normalizedFiberDensity
  rw [normalizedIntegerColumns_split]
  have h := splitPivotDensity_displacement (normalizedPivotEquiv A hA S P hS hP)
    (matrixSupCLM (normalizedIntegerColumns B T P))
    (matrixSupCLM (normalizedIntegerColumns C Q P)) hf hg hR hfs hgs hg0 hgmass hmove v
  have hU : 0 ≤ U := (norm_nonneg _).trans hinv
  have hJ := inverseJacobian_le_norm_bound (normalizedPivotEquiv A hA S P hS hP) hinv
  apply h.trans
  unfold spatialKernelErrorConstant
  gcongr

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedJetDensitySupport
namespace OAI


namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

theorem splitFreeProfile_integrable {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0) :
    Integrable (splitFreeProfile f g) := by
  apply (splitFreeProfile_continuous hf hg).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : (J ⊕ N → ℝ) × (I → ℝ)) (max R S))
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  exact hp (splitFreeProfile_zero_outside hfs hgs p h)

theorem splitFreeProfile_integral {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0) :
    (∫ p, splitFreeProfile f g p) = (∫ p, f p) * ∫ n, g n := by
  have hfi : Integrable f := by
    apply hf.integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : (J → ℝ) × (I → ℝ)) R)
    intro p hp
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra! h
    exact hp (hfs p h)
  have hi := splitFreeProfile_integrable hf hg hfs hgs
  rw [Measure.volume_eq_prod, integral_prod _ hi]
  have heq (y : J ⊕ N → ℝ) :
      (∫ x : I → ℝ, splitFreeProfile f g (y, x)) =
        splitInputProfile (fun p : (J → ℝ) × (N → ℝ) => (∫ x, f (p.1, x)) * g p.2) y := by
    unfold splitFreeProfile splitInputProfile
    exact integral_mul_const (g (fun n => y (.inr n)))
      (fun x => f ((fun j => y (.inl j)), x))
  simp_rw [heq]
  rw [splitInputProfile_integral, Measure.volume_eq_prod,
    integral_prod_mul (fun y : J → ℝ => ∫ x, f (y, x)) g, ← integral_prod f hfi]
  rfl

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedSpatialReplacement
namespace OAI


namespace Erdos3

open scoped BigOperators

theorem norm_weighted_density_mean_sub_le {X : Type*} (s : Finset X)
    (D a b : X → ℝ) (φ : X → ℂ) {ε : ℝ}
    (hD : ∀ x ∈ s, 0 ≤ D x) (hφ : ∀ x ∈ s, ‖φ x‖ ≤ 1)
    (hab : ∀ x ∈ s, |a x - b x| ≤ ε) :
    ‖(𝔼 x ∈ s, ((D x * a x : ℝ) : ℂ) * φ x) -
      (𝔼 x ∈ s, ((D x * b x : ℝ) : ℂ) * φ x)‖ ≤ ε * (𝔼 x ∈ s, D x) := by
  rw [← Finset.expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  calc
    _ ≤ 𝔼 x ∈ s, ε * D x := by
      apply Finset.expect_le_expect
      intro x hx
      have heq : ((D x * a x : ℝ) : ℂ) * φ x - ((D x * b x : ℝ) : ℂ) * φ x =
          ((D x * (a x - b x) : ℝ) : ℂ) * φ x := by push_cast; ring
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hD x hx)]
      calc
        _ ≤ D x * |a x - b x| * 1 :=
          mul_le_mul_of_nonneg_left (hφ x hx) (mul_nonneg (hD x hx) (abs_nonneg _))
        _ ≤ ε * D x := by
          rw [mul_one, mul_comm ε]
          exact mul_le_mul_of_nonneg_left (hab x hx) (hD x hx)
    _ = _ := (Finset.mul_expect s D ε).symm

end Erdos3


namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem normalizedSpatial_probability_comparison {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ) (C : Matrix I N ℤ)
    (S P : I → ℝ) (T : J → ℝ) (Q : N → ℝ)
    (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hFree : ∀ j, 0 < Sum.elim T Q j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (g : (N → ℝ) → ℝ)
    (hf0 : ∀ p, 0 ≤ f p) (hg0 : ∀ n, 0 ≤ g n)
    {K Kfull : ℝ≥0} (hf : LipschitzWith K f) (hg : Continuous g)
    (hfull : LipschitzWith Kfull (splitFreeProfile f g))
    {R Rn δ G U V D L ρ H : ℝ} (h : ℕ)
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hscaleS : ∀ i, ρ ≤ S i) (hscaleFree : ∀ j, ρ ≤ Sum.elim T Q j)
    (hsmall : (A.det.natAbs : ℝ) ≤ ρ) (hcoeff : ∀ i j, |(A i j : ℝ)| ≤ D * L ^ h)
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, Rn < ‖n‖ → g n = 0)
    (hfmass : (∫ p, f p) = 1) (hgmass : (∫ n, g n) = 1)
    (hsmallMass : (2 * max R Rn + 2) ^ (Fintype.card I + Fintype.card (J ⊕ N)) * Kfull *
      ((A.det.natAbs : ℝ) / ρ) ≤ 1 / 2)
    (hbound : ∀ p, ‖splitFreeProfile f g p‖ ≤ H)
    (hindex : ((pivotFullImage A (Matrix.fromCols B C)).toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns (Matrix.fromCols B C) (Sum.elim T Q) P)‖ ≤ V)
    (hmove : ∀ n, g n ≠ 0 → ‖matrixSupCLM (normalizedIntegerColumns C Q P) n‖ ≤ δ) :
    ∃ hM : 0 < scaledInputMass (splitFreeProfile f g) S (Sum.elim T Q),
      let p := integerImagePMF A (Matrix.fromCols B C) (splitFreeProfile f g)
        (splitFreeProfile_nonneg hf0 hg0) S (Sum.elim T Q) hS hFree
        (splitFreeProfile_zero_outside hfs hgs) hM
      let w := maskedIntegerImageDensity A (Matrix.fromCols B C) P
        (normalizedFiberDensity A hA B S P T hS hP f)
      let E := (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card (J ⊕ N))
          G U V (max R Rn) H Kfull * ((Fintype.card I).factorial * D ^ Fintype.card I)) *
          L ^ (h * Fintype.card I) / ρ +
        G * (spatialKernelErrorConstant (Fintype.card I) (Fintype.card J) U R K * δ)
      (∀ v, |(∏ i, P i) * (p v).toReal - w v| ≤ E) ∧
      (∀ (s : Finset (I → ℤ)) (weight : (I → ℤ) → ℝ) (φ : (I → ℤ) → ℂ),
        (∀ v ∈ s, 0 ≤ weight v) → (∀ v ∈ s, ‖φ v‖ ≤ 1) →
        ‖(𝔼 v ∈ s, ((weight v * ((∏ i, P i) * (p v).toReal) : ℝ) : ℂ) * φ v) -
          (𝔼 v ∈ s, ((weight v * w v : ℝ) : ℂ) * φ v)‖ ≤ E * (𝔼 v ∈ s, weight v)) := by
  have hmass : (∫ p, splitFreeProfile f g p) = 1 := by
    rw [splitFreeProfile_integral hf.continuous hg hfs hgs, hfmass, hgmass, one_mul]
  obtain ⟨hM, hdiscrete⟩ := normalizedIntegerImage_polynomial_error_s2 A hA (Matrix.fromCols B C)
    S P (Sum.elim T Q) hS hP hFree (splitFreeProfile f g) (splitFreeProfile_nonneg hf0 hg0)
    hfull h (hR.trans (le_max_left _ _)) hρ hH hscaleS hscaleFree hsmall hcoeff
    (splitFreeProfile_zero_outside hfs hgs) hmass hsmallMass hbound hindex hinv hcol
  refine ⟨hM, ?_⟩
  dsimp only
  have hU : 0 ≤ U := (norm_nonneg _).trans hinv
  have hreal := normalizedSplitDensity_displacement A hA B C S P T Q hS hP
    hf hg hR hδ hfs hgs hg0 hgmass hinv hmove
  have hmasked := maskedIntegerImageDensity_error A (Matrix.fromCols B C) P
    (normalizedFiberDensity A hA (Matrix.fromCols B C) S P (Sum.elim T Q) hS hP (splitFreeProfile f g))
    (normalizedFiberDensity A hA B S P T hS hP f)
    (mul_nonneg (spatialKernelErrorConstant_nonneg _ _ K hU hR) hδ) hindex hreal
  have hpoint (v : I → ℤ) := (abs_sub_le
    ((∏ i, P i) * (integerImagePMF A (Matrix.fromCols B C) (splitFreeProfile f g)
      (splitFreeProfile_nonneg hf0 hg0) S (Sum.elim T Q) hS hFree
      (splitFreeProfile_zero_outside hfs hgs) hM v).toReal)
    (maskedIntegerImageDensity A (Matrix.fromCols B C) P
      (normalizedFiberDensity A hA (Matrix.fromCols B C) S P (Sum.elim T Q) hS hP
        (splitFreeProfile f g)) v)
    (maskedIntegerImageDensity A (Matrix.fromCols B C) P
      (normalizedFiberDensity A hA B S P T hS hP f) v)).trans
        (add_le_add (hdiscrete v) (hmasked v))
  refine ⟨hpoint, ?_⟩
  intro s weight φ hw hφ
  exact norm_weighted_density_mean_sub_le s weight _ _ φ hw hφ (fun v _ => hpoint v)

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI


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

theorem pivotFullImage_eq_range {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) :
    pivotFullImage A B = (Matrix.fromCols A B).mulVecLin.range :=
  (integerMatrix_fromCols_range A B).symm

theorem pivotFullImage_split {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (C : Matrix I N ℤ) :
    pivotFullImage A (Matrix.fromCols B C) = pivotFullImage A B ⊔ C.mulVecLin.range := by
  unfold pivotFullImage
  rw [integerMatrix_fromCols_range, sup_assoc]

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarSpatialScaleBounds
namespace OAI


namespace Erdos3

theorem integerColumnEquiv_range {I J K : Type*} [Fintype J] [Fintype K]
    (A : Matrix I J ℤ) (e : K ≃ J) : (A.submatrix id e).mulVecLin.range = A.mulVecLin.range := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  change Submodule.span ℤ (Set.range (fun k => fun i => A i (e k))) =
    Submodule.span ℤ (Set.range (fun j => fun i => A i j))
  congr 1
  ext v
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨e k, hk⟩
  · rintro ⟨j, hj⟩
    exact ⟨e.symm j, by simpa only [e.apply_symm_apply] using hj⟩

theorem selectedSpatial_full_image {I J : Type*} [Fintype I] [Fintype J]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) :
    pivotFullImage (selectedSpatialPivot root D s) (selectedSpatialFreeColumns root D s) =
      (rootDifferenceMatrix root D).mulVecLin.range := by
  rw [pivotFullImage_eq_range, selectedSpatial_fromCols]
  exact integerColumnEquiv_range _ _

theorem selectedSpatial_extended_period {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) (C : Matrix (Unit ⊕ I) N ℤ)
    {B : ℕ} (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B) :
    HasBoundedScalarPeriod
      (pivotFullImage (selectedSpatialPivot root D s) (Matrix.fromCols (selectedSpatialFreeColumns root D s) C)) B := by
  obtain ⟨a, ha, haB, hp⟩ := rootDifferenceMatrix_bounded_period root D hperiod
  refine ⟨a, ha, haB, ?_⟩
  rw [pivotFullImage_split, selectedSpatial_full_image]
  exact hp.trans le_sup_left

theorem selectedSpatial_extended_index {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) (C : Matrix (Unit ⊕ I) N ℤ)
    {B : ℕ} (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B) :
    (pivotFullImage (selectedSpatialPivot root D s)
      (Matrix.fromCols (selectedSpatialFreeColumns root D s) C)).toAddSubgroup.index ≤
        B^(Fintype.card I + 1) := by
  simpa only [Fintype.card_sum, Fintype.card_unit, Nat.add_comm] using
    hasBoundedScalarPeriod_index_le _ B (selectedSpatial_extended_period root D s C hperiod)


end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothProfileReindexing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_map_equiv_apply {X Y : Type*} (p : PMF X) (e : X ≃ Y) (y : Y) :
    (p.map e) y = p (e.symm y) := by
  classical
  rw [PMF.map_apply, tsum_eq_single (e.symm y)]
  · simp
  · intro z hz
    have he : y ≠ e z := by
      intro he
      apply hz
      apply e.injective
      simpa only [e.apply_symm_apply] using he.symm
    simp only [ite_eq_right_iff]
    exact fun h => (he h).elim

theorem smoothProductPMF_reindex_apply {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (S : J → ℝ) (hS : ∀ j, 0 < S j) (z : J → ℤ) :
    smoothProductPMF (S ∘ e) (fun i => hS (e i)) (z ∘ e) = smoothProductPMF S hS z := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [smoothProductPMF_apply, smoothProductPMF_apply]
  exact Equiv.prod_comp e (fun j => (smoothCoefficientPMF (S j) (hS j) (z j)).toReal)

theorem smoothProductPMF_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (S : J → ℝ) (hS : ∀ j, 0 < S j) :
    (smoothProductPMF (S ∘ e) (fun i => hS (e i))).map
      (fun z => z ∘ e.symm) = smoothProductPMF S hS := by
  let E : (I → ℤ) ≃ (J → ℤ) := Equiv.arrowCongr e (Equiv.refl ℤ)
  change (smoothProductPMF (S ∘ e) (fun i => hS (e i))).map E = _
  ext z
  rw [pmf_map_equiv_apply]
  exact smoothProductPMF_reindex_apply e S hS z

theorem smoothSplit_inputPMF_join {I J : Type*} [Fintype I] [Fintype J]
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    (scaledInputPMF (smoothSplitProfile J I) (fun p => (smoothSplitProfile_range J I p).1)
      S T hS hT (smoothSplitProfile_zero_outside J I) (smoothSplit_mass_pos S T hS hT)).map
        (fun p => Sum.elim p.1 p.2) =
      smoothProductPMF (Sum.elim S T) (fun k => Sum.rec hS hT k) := by
  let E := (Equiv.sumPiEquivProdPi (fun _ : I ⊕ J => ℤ)).symm
  change (scaledInputPMF _ _ _ _ _ _ _ _).map E = _
  ext z
  rw [pmf_map_equiv_apply]
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [smoothSplit_inputPMF_apply, smoothProductPMF_apply]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothIntegerImage
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem smoothIntegerImagePMF_eq_matrix {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) :
    smoothIntegerImagePMF A B S T hS hT =
      smoothMatrixImagePMF (Matrix.fromCols A B) (Sum.elim S T) (fun k => Sum.rec hS hT k) := by
  unfold smoothIntegerImagePMF integerImagePMF smoothMatrixImagePMF
  rw [← smoothSplit_inputPMF_join S T hS hT, PMF.map_comp]
  congr 1
  funext p
  simp only [Function.comp_def, Matrix.fromCols_mulVec, Sum.elim_inl, Sum.elim_inr]

theorem smoothMatrixImagePMF_reindex {O I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix O J ℤ) (e : I ≃ J) (S : J → ℝ) (hS : ∀ j, 0 < S j) :
    smoothMatrixImagePMF (A.submatrix id e) (S ∘ e) (fun i => hS (e i)) =
      smoothMatrixImagePMF A S hS := by
  unfold smoothMatrixImagePMF
  rw [← smoothProductPMF_reindex e S hS, PMF.map_comp]
  congr 1
  funext z
  exact Matrix.submatrix_mulVec_equiv A z id e

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowReindex
namespace OAI


namespace Erdos3

theorem enormousCoefficient_mesh_conditions {j h : ℕ} {D Z L H : ℝ}
    (hD : 0 ≤ D) (hZ : 0 ≤ Z) (hL : 0 < L) (hH : 0 < H)
    (hlarge : 2 * (1 + Z) * D * L ^ (h * (j + 1)) ≤ H) :
    D * L ^ (h * j) ≤ H / L ^ h ∧
      Z * (D * L ^ (h * j) / (H / L ^ h)) ≤ 1 / 2 := by
  have hp : L ^ (h * (j + 1)) = L ^ (h * j) * L ^ h := by
    rw [Nat.mul_add, Nat.mul_one, pow_add]
  have hprod : D * L ^ (h * j) * L ^ h ≤ H := by
    rw [hp] at hlarge
    have hnon : 0 ≤ D * L ^ (h * j) * L ^ h := by positivity
    nlinarith
  refine ⟨(le_div_iff₀ (pow_pos hL h)).mpr hprod, ?_⟩
  have he : Z * (D * L ^ (h * j) / (H / L ^ h)) =
      Z * D * L ^ (h * (j + 1)) / H := by rw [hp]; field_simp
  rw [he]
  apply (div_le_iff₀ hH).mpr
  have hnon : 0 ≤ D * L ^ (h * (j + 1)) := by positivity
  nlinarith


open MeasureTheory
open scoped BigOperators NNReal

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SmoothSelectedSpatialLaw
namespace OAI

section

namespace Erdos3

theorem selectedFullSpatial_fromCols {I J N : Type*} [Fintype I]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) (C : Matrix (Unit ⊕ I) N ℤ) :
    Matrix.fromCols (selectedSpatialPivot root D s)
        (Matrix.fromCols (selectedSpatialFreeColumns root D s) C) =
      (Matrix.fromCols (rootDifferenceMatrix root D) C).submatrix id
        (selectedFullSpatialColumnEquiv s N) := by
  ext i k
  cases k with
  | inl k => cases k <;> cases i <;> rfl
  | inr k => cases k <;> cases i <;> rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialScales
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

theorem physicalCube_coefficient_bound {α K : Type*}
    (root : K → ℤ) (D : Matrix α K ℤ) {C : ℝ} (hC : 1 ≤ C)
    (hr : ∀ k, |(root k : ℝ)| ≤ C) (hD : ∀ i k, |(D i k : ℝ)| ≤ C) :
    ∀ i k, |(physicalCubeCoefficient root D i k : ℝ)| ≤ C := by
  rintro (i | i) (k | k)
  · simpa [physicalCubeCoefficient] using hC
  · exact hr k
  · simpa [physicalCubeCoefficient] using (zero_le_one.trans hC)
  · exact hD i k

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

theorem selectedFullSpatial_anisotropic_scale {I J N : Type*} [Fintype I]
    (s : I ↪ J) (A R : ℝ) (Q : N → ℝ) :
    Sum.elim (anisotropicSpatialScale I A R) (Sum.elim (fun _ : UnselectedColumn s => R) Q) =
      Sum.elim (anisotropicSpatialScale J A R) Q ∘ selectedFullSpatialColumnEquiv s N := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k <;> rfl

theorem smoothSelectedSpatial_anisotropic_law {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) (C : Matrix (Unit ⊕ I) N ℤ)
    {A R : ℝ} (hA : 0 < A) (hR : 0 < R) (Q : N → ℝ) (hQ : ∀ j, 0 < Q j) :
    smoothIntegerImagePMF (selectedSpatialPivot root D s)
      (Matrix.fromCols (selectedSpatialFreeColumns root D s) C)
      (anisotropicSpatialScale I A R) (Sum.elim (fun _ : UnselectedColumn s => R) Q)
      (anisotropicSpatialScale_pos I hA hR) (fun j => Sum.rec (fun _ => hR) hQ j) =
      anisotropicSpatialOutputLaw root D C A R Q hA hR hQ := by
  rw [smoothIntegerImagePMF_eq_matrix, selectedFullSpatial_fromCols]
  simpa only [← selectedFullSpatial_anisotropic_scale s A R Q, anisotropicSpatialOutputLaw] using
    (smoothMatrixImagePMF_reindex (Matrix.fromCols (rootDifferenceMatrix root D) C)
    (selectedFullSpatialColumnEquiv s N) (Sum.elim (anisotropicSpatialScale J A R) Q)
    (fun j => Sum.rec (anisotropicSpatialScale_pos J hA hR) hQ j))

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

theorem normalizedIntegerColumns_variable_entry_bound {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) {C : ℝ}
    (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 ≤ T j)
    (hM : ∀ i j, |(M i j : ℝ)| * T j ≤ C * P i) :
    ∀ i j, |normalizedIntegerColumns M T P i j| ≤ C := by
  intro i j
  rw [normalizedIntegerColumns_entry_div, abs_div, abs_mul,
    abs_of_nonneg (hT j), abs_of_pos (hP i)]
  exact (div_le_iff₀ (hP i)).mpr (hM i j)

theorem normalizedIntegerColumns_variable_norm_bound {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) {C : ℝ}
    (hP : ∀ i, 0 < P i) (hC : 0 ≤ C) (hT : ∀ j, 0 ≤ T j)
    (hM : ∀ i j, |(M i j : ℝ)| * T j ≤ C * P i) :
    ‖matrixSupCLM (normalizedIntegerColumns M T P)‖ ≤ Fintype.card J * C :=
  matrixSupCLM_norm_le _ hC (normalizedIntegerColumns_variable_entry_bound M T P hP hT hM)

theorem anisotropicSpatialFree_scaled_bound {I J : Type*}
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J) {A R L : ℝ}
    (hR : 0 ≤ R) (hr : ∀ j, |(root j : ℝ)| * R ≤ A)
    (hD : ∀ i j, |(D i j : ℝ)| ≤ L) :
    ∀ i j, |(selectedSpatialFreeColumns root D s i j : ℝ)| * R ≤
      physicalSpatialOutputScale I A R L i := by
  rintro (i | i) j
  · exact hr j.val
  · exact mul_le_mul_of_nonneg_right (hD i j.val) hR

theorem anisotropicSpatial_free_norm_bound {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J)
    (C : Matrix (Unit ⊕ I) N ℤ) (Q : N → ℝ) {A R L ξ : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hξ : ξ ≤ 1)
    (hQ : ∀ j, 0 ≤ Q j) (hr : ∀ j, |(root j : ℝ)| * R ≤ A)
    (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hC : ∀ i j, |(C i j : ℝ)| * Q j ≤ ξ * physicalSpatialOutputScale I A R L i) :
    ‖matrixSupCLM (normalizedIntegerColumns
      (Matrix.fromCols (selectedSpatialFreeColumns root D s) C)
      (Sum.elim (fun _ : UnselectedColumn s => R) Q) (physicalSpatialOutputScale I A R L))‖ ≤
        Fintype.card (UnselectedColumn s ⊕ N) := by
  have hP := physicalSpatialOutputScale_pos I hA hR hL
  have hscale : ∀ j, 0 ≤ Sum.elim (fun _ : UnselectedColumn s => R) Q j := by
    rintro (j | j)
    · exact hR.le
    · exact hQ j
  have hcolumns : ∀ i j,
      |((Matrix.fromCols (selectedSpatialFreeColumns root D s) C) i j : ℝ)| *
        Sum.elim (fun _ : UnselectedColumn s => R) Q j ≤
          1 * physicalSpatialOutputScale I A R L i := by
    intro i j
    cases j with
    | inl j =>
      change |(selectedSpatialFreeColumns root D s i j : ℝ)| * R ≤
        1 * physicalSpatialOutputScale I A R L i
      simpa only [one_mul] using anisotropicSpatialFree_scaled_bound root D s hR.le hr hD i j
    | inr j => exact (hC i j).trans (mul_le_mul_of_nonneg_right hξ (hP i).le)
  simpa only [mul_one] using normalizedIntegerColumns_variable_norm_bound _ _ _ hP zero_le_one hscale hcolumns

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AnisotropicGoodKernelComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal

theorem anisotropicSpatial_original_error {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (root : J → ℤ) (D : Matrix I J ℤ) (s : I ↪ J)
    (C : Matrix (Unit ⊕ I) N ℤ) (Q : N → ℝ)
    {A R L κ C₀ ρ ξ : ℝ} {B : ℕ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hC₀ : 1 ≤ C₀) (hr : ∀ j, |(root j : ℝ)| * R ≤ A)
    (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hrC : ∀ j, |(root j : ℝ)| ≤ C₀) (hDC : ∀ i j, |(D i j : ℝ)| ≤ C₀)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|)
    (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B)
    (hQ : ∀ j, 0 < Q j) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hC : ∀ i j, |(C i j : ℝ)| * Q j ≤ ξ * physicalSpatialOutputScale I A R L i)
    (hscaleA : ρ ≤ A) (hscaleR : ρ ≤ R) (hscaleQ : ∀ j, ρ ≤ Q j)
    (hmesh : anisotropicSpatialMeshThreshold s N C₀ ≤ ρ) :
    let hp := (anisotropicSpatialPivot_control root D s hA hR hL hκ hr hD hminor).1
    ∀ v, |(∏ i, physicalSpatialOutputScale I A R L i) *
        (anisotropicSpatialOutputLaw root D C A R Q hA hR hQ v).toReal -
      maskedIntegerImageDensity (selectedSpatialPivot root D s)
        (Matrix.fromCols (selectedSpatialFreeColumns root D s) C) (physicalSpatialOutputScale I A R L)
        (anisotropicSpatialKernelDensity s root D hp A R L hA hR hL) v| ≤
      anisotropicSpatialError s N B κ C₀ ρ ξ := by
  intro hp
  let M := selectedSpatialPivot root D s
  let M' := selectedSpatialFreeColumns root D s
  let S := anisotropicSpatialScale I A R
  let P := physicalSpatialOutputScale I A R L
  let lip : ℝ≥0 := (Fintype.card (UnselectedColumn s ⊕ N) + Fintype.card (Unit ⊕ I)) * probabilityProfileLipschitz
  have hS := anisotropicSpatialScale_pos I hA hR
  have hP := physicalSpatialOutputScale_pos I hA hR hL
  have hFree : ∀ j, 0 < Sum.elim (fun _ : UnselectedColumn s => R) Q j := by
    rintro (j | j)
    · exact hR
    · exact hQ j
  have hscaleS : ∀ i, ρ ≤ S i := by
    rintro (i | i)
    · exact hscaleA
    · exact hscaleR
  have hscaleFree : ∀ j, ρ ≤ Sum.elim (fun _ : UnselectedColumn s => R) Q j := by
    rintro (j | j)
    · exact hscaleR
    · exact hscaleQ j
  have hcoeff : ∀ i j, |(M i j : ℝ)| ≤ C₀ * (1 : ℝ) ^ 0 := by
    intro i j
    have heq : M = (physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s) :=
      (physicalCubeCoefficient_pivot root D s).symm
    rw [heq]
    simpa only [Matrix.submatrix_apply, id_eq, pow_zero, mul_one] using
      physicalCube_coefficient_bound root D hC₀ hrC hDC i (physicalCubePivotIndex s j)
  have hdet : (M.det.natAbs : ℝ) ≤ anisotropicSpatialDetAllowance I C₀ := by
    simpa only [anisotropicSpatialDetAllowance, one_pow, mul_one] using
      integerPivot_polynomial_period_bound M 0 hcoeff
  have hm := enormousCoefficient_mesh_conditions (j := Fintype.card (Unit ⊕ I)) (h := 0)
    (D := anisotropicSpatialDetAllowance I C₀)
    (Z := 4 ^ (Fintype.card (Unit ⊕ I) + Fintype.card (UnselectedColumn s ⊕ N)) * (lip : ℝ))
    (L := 1) (H := ρ) (by unfold anisotropicSpatialDetAllowance; positivity) (by positivity)
    (by norm_num) hρ (by
      simpa only [anisotropicSpatialMeshThreshold, lip, NNReal.coe_mul, NNReal.coe_add,
        NNReal.coe_natCast, one_pow, mul_one] using hmesh)
  simp only [one_pow, mul_one, div_one] at hm
  have hsmallMass : 4 ^ (Fintype.card (Unit ⊕ I) + Fintype.card (UnselectedColumn s ⊕ N)) *
      (lip : ℝ) * ((M.det.natAbs : ℝ) / ρ) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hdet hρ.le) (by positivity)).trans hm.2
  have hindex : ((pivotFullImage M (Matrix.fromCols M' C)).toAddSubgroup.index : ℝ) ≤
      (B : ℝ) ^ (Fintype.card I + 1) := by
    exact_mod_cast selectedSpatial_extended_index root D s C hperiod
  have hinv : ‖(normalizedPivotEquiv M hp S P hS hP).symm.toContinuousLinearMap‖ ≤
      physicalSpatialInverseBound I κ := by
    rw [normalizedPivotEquiv_inverse_eq]
    exact (anisotropicSpatialPivot_control root D s hA hR hL hκ hr hD hminor).2
  have hcol := anisotropicSpatial_free_norm_bound root D s C Q hA hR hL hξ1
    (fun j => (hQ j).le) hr hD hC
  have hmove : ∀ n, smoothProductProfile N n ≠ 0 →
      ‖matrixSupCLM (normalizedIntegerColumns C Q P) n‖ ≤ Fintype.card N * ξ := by
    apply supported_column_displacement _ _ (smoothProductProfile_zero_outside N)
    simpa only [mul_one] using normalizedIntegerColumns_variable_norm_bound C Q P hP hξ0
      (fun j => (hQ j).le) hC
  have hfull : LipschitzWith lip
      (splitFreeProfile (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) (smoothProductProfile N)) := by
    rw [splitFreeProfile_smooth]
    exact smoothSplitProfile_lipschitz _ _
  have hbound : ∀ p, ‖splitFreeProfile
      (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) (smoothProductProfile N) p‖ ≤ 1 := by
    rw [splitFreeProfile_smooth]
    exact smoothSplitProfile_norm_le _ _
  obtain ⟨hM, hpoint, _⟩ := normalizedSpatial_probability_comparison M hp M' C S P
    (fun _ : UnselectedColumn s => R) Q hS hP hFree
    (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) (smoothProductProfile N)
    (fun p => (smoothSplitProfile_range _ _ p).1) (fun n => (smoothProductProfile_range _ n).1)
    (smoothSplitProfile_lipschitz _ _) (smoothProductProfile_contDiff N).continuous hfull
    0 zero_le_one (mul_nonneg (Nat.cast_nonneg _) hξ0) hρ zero_le_one hscaleS hscaleFree
    (hdet.trans hm.1) hcoeff (smoothSplitProfile_zero_outside _ _) (smoothProductProfile_zero_outside N)
    (smoothSplitProfile_integral _ _) (smoothProductProfile_integral N)
    (by simpa only [max_self, show (2 : ℝ) * 1 + 2 = 4 by norm_num] using hsmallMass)
    hbound hindex hinv hcol hmove
  rw [← smoothSelectedSpatial_anisotropic_law root D s C hA hR Q hQ]
  simpa only [splitFreeProfile_smooth, max_self, one_pow, mul_one, lip, M, M', S, P,
    smoothIntegerImagePMF, anisotropicSpatialError, anisotropicSpatialDetAllowance,
    anisotropicSpatialKernelDensity] using hpoint

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

theorem goodScalarKernelTuple_anisotropic_error_s2_oai {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    {L B : ℕ} (hL : 0 < L) (s : I ↪ J) (x : J → IntegerScalarCubeBox I L)
    (root : J → ℤ) (C : Matrix (Unit ⊕ I) N ℤ) (Q : N → ℝ)
    {A R κ C₀ ρ ξ : ℝ} (hA : 0 < A) (hR : 0 < R) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple s κ B x) (hC₀ : 1 ≤ C₀) (hLC : (L : ℝ) ≤ C₀)
    (hr : ∀ j, |(root j : ℝ)| * R ≤ A) (hrC : ∀ j, |(root j : ℝ)| ≤ C₀)
    (hQ : ∀ j, 0 < Q j) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hC : ∀ i j, |(C i j : ℝ)| * Q j ≤ ξ * physicalSpatialOutputScale I A R L i)
    (hscaleA : ρ ≤ A) (hscaleR : ρ ≤ R) (hscaleQ : ∀ j, ρ ≤ Q j)
    (hmesh : anisotropicSpatialMeshThreshold s N C₀ ≤ ρ) :
    let hp := goodScalarKernelTuple_spatial_det_ne_zero s x root hκ hx
    ∀ v, |(∏ i, physicalSpatialOutputScale I A R L i) *
        (anisotropicSpatialOutputLaw root (scalarCubeDifferenceMatrix x) C A R Q hA hR hQ v).toReal -
      maskedIntegerImageDensity (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s) C)
        (physicalSpatialOutputScale I A R L)
        (anisotropicSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hp A R L
          hA hR (Nat.cast_pos.mpr hL)) v| ≤ anisotropicSpatialError s N B κ C₀ ρ ξ := by
  intro hp
  have hD : ∀ i j, |(scalarCubeDifferenceMatrix x i j : ℝ)| ≤ L := by
    intro i j
    have hi := Finset.mem_Ico.mp (x j (some i)).property
    exact_mod_cast (abs_le.mpr ⟨hi.1, hi.2.le⟩)
  have hminor : κ ≤ |(Matrix.of (fun i j => (scalarCubeDifferenceMatrix x i (s j) : ℝ) / (L : ℝ))).det| := by
    change κ ≤ |(normalizedScalarCubePivot s x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  exact anisotropicSpatial_original_error root (scalarCubeDifferenceMatrix x) s C Q
    hA hR (Nat.cast_pos.mpr hL) hκ hρ hC₀ hr hD hrC (fun i j => (hD i j).trans hLC)
    hminor hx.2 hQ hξ0 hξ1 hC hscaleA hscaleR hscaleQ hmesh

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.goodScalarKernelTuple_anisotropic_error_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.goodScalarKernelTuple_anisotropic_error_s2_oai.{u_1, u_2, u_3}
