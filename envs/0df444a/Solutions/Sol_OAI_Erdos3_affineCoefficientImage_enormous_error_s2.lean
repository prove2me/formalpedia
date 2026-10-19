-- Prove2me | solution 1 for OAI.Erdos3.affineCoefficientImage_enormous_error_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:47:43.156696+00:00
-- url     : https://prove2.me/submissions/67c92de2-edad-4861-8c47-aa68732669d7

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B098
import Definitions.Def_OAIE3v2B100
import Theorems.Thm_OAI_Erdos3_normalizedIntegerImage_polynomial_error_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialPivotNormalization
namespace OAI

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
open scoped NNReal

theorem selectedCoefficientProfile_norm_le {I J : Type*} [Fintype I]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} {H : ℝ} (hf : ∀ x, ‖f x‖ ≤ H) :
    ∀ p, ‖selectedCoefficientProfile s f p‖ ≤ H := fun p => hf (selectedCoefficientEquiv s ℝ p)

theorem selectedCoefficientProfile_lipschitz {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (selectedCoefficientProfile s f) := by
  simpa only [mul_one, selectedCoefficientProfile] using hf.comp (selectedCoefficientEquiv_lipschitz s)

theorem selectedCoefficientProfile_integral {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) :
    (∫ p, selectedCoefficientProfile s f p) = ∫ x, f x := by
  let e := selectedFreeFirstEquiv s
  have hsum := (volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : UnselectedColumn s ⊕ I => ℝ)).integral_comp
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : UnselectedColumn s ⊕ I => ℝ)).symm.measurableEmbedding
    (fun z => f (z ∘ e.symm))
  have hpi := (volume_measurePreserving_piCongrLeft (fun _ : J => ℝ) e).integral_comp
    (MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e).measurableEmbedding f
  apply hsum.trans
  simpa only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft',
    Equiv.coe_fn_symm_mk, eq_rec_constant, Function.comp_def] using hpi

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScaleIndependence
namespace OAI


namespace Erdos3


open scoped Matrix

theorem selectedMatrix_fromCols {I J R : Type*} [Fintype I]
    (A : Matrix I J R) (s : I ↪ J) :
    Matrix.fromCols (A.submatrix id s) (remainingMatrixColumns A s) =
      A.submatrix id (selectedColumnEquiv s) := by
  ext i j
  cases j <;> rfl

theorem selectedMatrix_full_image {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (s : I ↪ J) :
    pivotFullImage (A.submatrix id s) (remainingMatrixColumns A s) = A.mulVecLin.range := by
  rw [pivotFullImage_eq_range, selectedMatrix_fromCols]
  exact integerColumnEquiv_range _ _

theorem normalized_remainingMatrixColumns {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (P : I → ℝ) :
    normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P =
      remainingMatrixColumns (normalizedIntegerColumns A S P) s := by
  classical
  ext i j
  simp only [remainingMatrixColumns, Matrix.submatrix_apply, id_eq,
    normalizedIntegerColumns_entry_div]

theorem normalized_remainingMatrixColumns_norm {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (P : I → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hentry : ∀ i j, |normalizedIntegerColumns A S P i j| ≤ C) :
    ‖matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s)
      (fun j => S j.val) P)‖ ≤ Fintype.card (UnselectedColumn s) * C := by
  classical
  rw [normalized_remainingMatrixColumns]
  exact matrixSupCLM_norm_le _ hC (fun i j => hentry i j.val)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedProductCoordinateLaw
namespace OAI


namespace Erdos3

open scoped Matrix

theorem coefficientPMF_apply {J : Type*} [Fintype J]
    (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < coefficientWeightSum f S)
    (z : J → ℤ) :
    (coefficientPMF f hf S hS hsupport hZ z).toReal = coefficientWeight f S z / coefficientWeightSum f S :=
  realWeightPMF_apply _ _ _ _ z

theorem selectedCoefficient_input_law {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {R : ℝ}
    (hsupport : ∀ x, R < ‖x‖ → f x = 0)
    (hM : 0 < scaledInputMass (selectedCoefficientProfile s f)
      (fun i => S (s i)) (fun j => S j.val)) :
    (scaledInputPMF (selectedCoefficientProfile s f) (selectedCoefficientProfile_nonneg s hf)
      (fun i => S (s i)) (fun j => S j.val) (fun i => hS (s i)) (fun j => hS j.val)
      (selectedCoefficientProfile_zero_outside s hsupport) hM).map (selectedIntegerCoefficientEquiv s) =
    coefficientPMF f hf S hS hsupport (selectedCoefficient_weight_sum_pos s f S hS hM) := by
  ext z
  rw [pmf_map_equiv_apply]
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [scaledInputPMF_apply, coefficientPMF_apply, selectedCoefficient_weight_sum]
  rw [← selectedIntegerCoefficient_weight, Equiv.apply_symm_apply]

theorem selectedIntegerCoefficient_mulVec {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (s : I ↪ J) (p : (I → ℤ) × (UnselectedColumn s → ℤ)) :
    A *ᵥ selectedIntegerCoefficientEquiv s p =
      A.submatrix id s *ᵥ p.1 + remainingMatrixColumns A s *ᵥ p.2 := by
  have he : selectedIntegerCoefficientEquiv s p =
      Sum.elim p.1 p.2 ∘ (selectedColumnEquiv s).symm := by
    funext j
    change Sum.elim p.2 p.1 ((Equiv.sumComm _ _) ((selectedColumnEquiv s).symm j)) =
      Sum.elim p.1 p.2 ((selectedColumnEquiv s).symm j)
    cases (selectedColumnEquiv s).symm j <;> rfl
  rw [he]
  have hm := Matrix.submatrix_mulVec_equiv A (Sum.elim p.1 p.2) id (selectedColumnEquiv s)
  rw [← selectedMatrix_fromCols, Matrix.fromCols_mulVec] at hm
  exact hm.symm

theorem selectedCoefficient_image_law {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (s : I ↪ J) (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {R : ℝ}
    (hsupport : ∀ x, R < ‖x‖ → f x = 0)
    (hM : 0 < scaledInputMass (selectedCoefficientProfile s f)
      (fun i => S (s i)) (fun j => S j.val)) :
    integerImagePMF (A.submatrix id s) (remainingMatrixColumns A s)
      (selectedCoefficientProfile s f) (selectedCoefficientProfile_nonneg s hf)
      (fun i => S (s i)) (fun j => S j.val) (fun i => hS (s i)) (fun j => hS j.val)
      (selectedCoefficientProfile_zero_outside s hsupport) hM =
    coefficientImagePMF A f hf S hS hsupport (selectedCoefficient_weight_sum_pos s f S hS hM) := by
  unfold coefficientImagePMF
  rw [← selectedCoefficient_input_law s f hf S hS hsupport hM, PMF.map_comp]
  unfold integerImagePMF
  congr 1
  funext p
  exact (selectedIntegerCoefficient_mulVec A s p).symm

end Erdos3


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

theorem enormousCoefficient_error_rate {j h : ℕ} (C L H : ℝ) :
    C * L ^ (h * j) / (H / L ^ h) = C * L ^ (h * (j + 1)) / H := by
  rw [Nat.mul_add, Nat.mul_one, pow_add, div_div_eq_mul_div]
  ring


open MeasureTheory
open scoped BigOperators NNReal

theorem selectedCoefficient_mask {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (s : I ↪ J) (P : I → ℝ) (f : (I → ℝ) → ℝ) :
    maskedIntegerImageDensity (A.submatrix id s) (remainingMatrixColumns A s) P f =
      coefficientImageMask A P f := by
  classical
  funext v
  simp only [maskedIntegerImageDensity, coefficientImageMask, selectedMatrix_full_image]

theorem coefficientImage_polynomial_error {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R G U V C L ρ H : ℝ} (h : ℕ) (hR : 0 ≤ R) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hscale : ∀ j, ρ ≤ S j) (hsmall : ((A.submatrix id s).det.natAbs : ℝ) ≤ ρ)
    (hcoeff : ∀ i j, |(A i (s j) : ℝ)| ≤ C * L ^ h)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hmass : (∫ x, f x) = 1)
    (hsmallMass : (2 * R + 2) ^ (Fintype.card I + Fintype.card (UnselectedColumn s)) * K *
      (((A.submatrix id s).det.natAbs : ℝ) / ρ) ≤ 1 / 2)
    (hbound : ∀ x, ‖f x‖ ≤ H) (hindex : (A.mulVecLin.range.toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(matrixSupCLM (normalizedIntegerPivot (A.submatrix id s)
      (fun i => S (s i)) P)).inverse‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s)
      (fun j => S j.val) P)‖ ≤ V) :
    ∃ hZ : 0 < coefficientWeightSum f S, ∀ v,
      |(∏ i, P i) * (coefficientImagePMF A f hf0 S hS hsupport hZ v).toReal -
        coefficientImageMask A P (selectedCoefficientDensity A s hA S P hS hP f) v| ≤
      (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card (UnselectedColumn s))
        G U V R H K * ((Fintype.card I).factorial * C ^ Fintype.card I)) *
          L ^ (h * Fintype.card I) / ρ := by
  classical
  have hmass' : (∫ p, selectedCoefficientProfile s f p) = 1 :=
    (selectedCoefficientProfile_integral s f).trans hmass
  have hindex' := hindex
  rw [← selectedMatrix_full_image A s] at hindex'
  obtain ⟨hM, herror⟩ := normalizedIntegerImage_polynomial_error_s2 (U := U)
    (A.submatrix id s) hA (remainingMatrixColumns A s)
    (fun i => S (s i)) P (fun j => S j.val) (fun i => hS (s i)) hP (fun j => hS j.val)
    (selectedCoefficientProfile s f) (selectedCoefficientProfile_nonneg s hf0)
    (selectedCoefficientProfile_lipschitz s hf) h hR hρ hH
    (fun i => hscale (s i)) (fun j => hscale j.val) hsmall hcoeff
    (selectedCoefficientProfile_zero_outside s hsupport) hmass' hsmallMass
    (selectedCoefficientProfile_norm_le s hbound) hindex'
    (by rwa [normalizedPivotEquiv_inverse_eq]) hcol
  refine ⟨selectedCoefficient_weight_sum_pos s f S hS hM, fun v => ?_⟩
  have he := herror v
  rw [selectedCoefficient_image_law A s f hf0 S hS hsupport hM, selectedCoefficient_mask] at he
  exact he

end Erdos3


namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem coefficientImage_enormous_error {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j)
    (f : (J → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R G U C L Hcap H : ℝ} (h : ℕ) (hR : 0 ≤ R) (hL : 0 < L)
    (hH : 0 < H) (hcap : 0 ≤ Hcap) (hC : 0 ≤ C)
    (hscale : ∀ j, H / L ^ h ≤ S j)
    (hcoeff : ∀ i j, |(A i (s j) : ℝ)| ≤ C * L ^ h)
    (hentry : ∀ i j, |normalizedIntegerColumns A S (fun _ => H) i j| ≤ C)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hmass : (∫ x, f x) = 1)
    (hbound : ∀ x, ‖f x‖ ≤ Hcap) (hindex : (A.mulVecLin.range.toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(matrixSupCLM (normalizedIntegerPivot (A.submatrix id s)
      (fun i => S (s i)) (fun _ => H))).inverse‖ ≤ U)
    (hlarge : 2 * (1 + (2 * R + 2) ^ (Fintype.card I + Fintype.card (UnselectedColumn s)) * K) *
      ((Fintype.card I).factorial * C ^ Fintype.card I) * L ^ (h * (Fintype.card I + 1)) ≤ H) :
    ∃ hZ : 0 < coefficientWeightSum f S, ∀ v,
      |H ^ Fintype.card I * (coefficientImagePMF A f hf0 S hS hsupport hZ v).toReal -
        coefficientImageMask A (fun _ => H)
          (selectedCoefficientDensity A s hA S (fun _ => H) hS (fun _ => hH) f) v| ≤
      (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card (UnselectedColumn s))
        G U (Fintype.card (UnselectedColumn s) * C) R Hcap K *
        ((Fintype.card I).factorial * C ^ Fintype.card I)) *
          L ^ (h * (Fintype.card I + 1)) / H := by
  classical
  have hρ : 0 < H / L ^ h := div_pos hH (pow_pos hL h)
  have hm := enormousCoefficient_mesh_conditions (j := Fintype.card I) (h := h)
    (D := (Fintype.card I).factorial * C ^ Fintype.card I)
    (Z := (2 * R + 2) ^ (Fintype.card I + Fintype.card (UnselectedColumn s)) * K)
    (by positivity) (by positivity) hL hH hlarge
  have hd := integerPivot_polynomial_period_bound (A.submatrix id s) h hcoeff
  have hsmall := hd.trans hm.1
  have hsmallMass : (2 * R + 2) ^ (Fintype.card I + Fintype.card (UnselectedColumn s)) * K *
      (((A.submatrix id s).det.natAbs : ℝ) / (H / L ^ h)) ≤ 1 / 2 := by
    apply le_trans _ hm.2
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hd hρ.le) (by positivity)
  obtain ⟨hZ, he⟩ := coefficientImage_polynomial_error A s hA S (fun _ => H) hS (fun _ => hH)
    f hf0 hf h hR hρ hcap hscale hsmall hcoeff hsupport hmass hsmallMass hbound hindex hinv
    (normalized_remainingMatrixColumns_norm A s S (fun _ => H) hC hentry)
  refine ⟨hZ, fun v => ?_⟩
  simpa only [Finset.prod_const, Finset.card_univ, enormousCoefficient_error_rate] using he v

end Erdos3


namespace Erdos3


open MeasureTheory
open scoped BigOperators NNReal

theorem coefficientImage_enormous_of_control {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {H L C U G : ℝ} (h : ℕ) (ctrl : CoefficientFiberControl A s S H L h C U G)
    (hL : 0 < L) (hH : 0 < H) (hC : 0 ≤ C)
    (f : (J → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R Hcap : ℝ} (hR : 0 ≤ R) (hcap : 0 ≤ Hcap)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hmass : (∫ x, f x) = 1)
    (hbound : ∀ x, ‖f x‖ ≤ Hcap)
    (hlarge : 2 * (1 + (2 * R + 2) ^ (Fintype.card I + Fintype.card (UnselectedColumn s)) * K) *
      ((Fintype.card I).factorial * C ^ Fintype.card I) * L ^ (h * (Fintype.card I + 1)) ≤ H) :
    ∃ hZ : 0 < coefficientWeightSum f S, ∀ v,
      |H ^ Fintype.card I * (coefficientImagePMF A f hf0 S hS hsupport hZ v).toReal -
        coefficientImageMask A (fun _ => H)
          (selectedCoefficientDensity A s ctrl.det_ne_zero S (fun _ => H) hS (fun _ => hH) f) v| ≤
      (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card (UnselectedColumn s))
        G U (Fintype.card (UnselectedColumn s) * C) R Hcap K *
        ((Fintype.card I).factorial * C ^ Fintype.card I)) *
          L ^ (h * (Fintype.card I + 1)) / H :=
  coefficientImage_enormous_error A s ctrl.det_ne_zero S hS f hf0 hf h hR hL hH hcap hC
    ctrl.scale_lower ctrl.integer_entry_bound ctrl.normalized_entry_bound hsupport hmass
    hbound ctrl.index_bound ctrl.inverse_bound hlarge

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

theorem affineProductProfile_integral {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : (∫ x, affineProductProfile c w x) = 1 := by
  change (∫ x, tensorCutoffWeight (fun i => affineProbabilityProfile (c i) (w i)) x) = 1
  rw [tensorCutoffWeight_integral]
  simp only [affineProbabilityProfile_integral _ (hw _), Finset.prod_const_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem affineCoefficientImage_enormous_error_s2_oai {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {H L C U G : ℝ} (h : ℕ) (ctrl : CoefficientFiberControl A s S H L h C U G)
    (hL : 0 < L) (hH : 0 < H) (hC : 0 ≤ C)
    (c w : J → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) {R : ℝ} (hR : 0 ≤ R) (hsupport : ∀ j, |c j| + w j ≤ R)
    (hlarge : 2 * (1 + (2 * R + 2) ^ (Fintype.card I + Fintype.card (UnselectedColumn s)) *
      affineProductProfileLip J δ) * ((Fintype.card I).factorial * C ^ Fintype.card I) *
      L ^ (h * (Fintype.card I + 1)) ≤ H) :
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w) S, ∀ v,
      |H ^ Fintype.card I *
        (coefficientImagePMF A (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
          S hS (affineProductProfile_zero_outside c w hw hR hsupport) hZ v).toReal -
        coefficientImageMask A (fun _ => H)
          (selectedCoefficientDensity A s ctrl.det_ne_zero S (fun _ => H) hS (fun _ => hH)
            (affineProductProfile c w)) v| ≤
      (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card (UnselectedColumn s))
        G U (Fintype.card (UnselectedColumn s) * C) R ((δ : ℝ)⁻¹ ^ Fintype.card J)
        (affineProductProfileLip J δ) * ((Fintype.card I).factorial * C ^ Fintype.card I)) *
          L ^ (h * (Fintype.card I + 1)) / H := by
  exact coefficientImage_enormous_of_control A s S hS h ctrl hL hH hC
    (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
    (affineProductProfile_lipschitz c w hδ hwidth) hR (by positivity)
    (affineProductProfile_zero_outside c w hw hR hsupport)
    (affineProductProfile_integral c w hw) (affineProductProfile_cap c w hδ hwidth) hlarge

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.affineCoefficientImage_enormous_error_s2_oai.{u_1, u_2} := @OAI.Erdos3.affineCoefficientImage_enormous_error_s2_oai.{u_1, u_2}
