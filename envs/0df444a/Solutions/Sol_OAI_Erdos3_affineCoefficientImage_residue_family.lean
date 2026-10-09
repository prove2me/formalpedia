-- Prove2me | solution 1 for OAI.Erdos3.affineCoefficientImage_residue_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T23:05:07.981178+00:00
-- url     : https://prove2.me/submissions/e2338ebe-a6ba-4b7f-be1f-c4f1314e83b4

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B100
import Theorems.Thm_OAI_Erdos3_affineCoefficientImage_tolerance

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

theorem residueLatticeImage_comap {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L m).comap (integerResidueMap I m) = L := by
  apply Submodule.comap_map_eq_self
  rwa [integerResidueMap_ker]

theorem residueLatticeImage_determines_lattice {I : Type*} [Fintype I]
    (L K : Submodule ℤ (I → ℤ)) (m : ℕ)
    (hL : integerScalarLattice I (m : ℤ) ≤ L) (hK : integerScalarLattice I (m : ℤ) ≤ K)
    (h : residueLatticeImage L m = residueLatticeImage K m) : L = K := by
  rw [← residueLatticeImage_comap L m hL, ← residueLatticeImage_comap K m hK, h]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem integerMatrixResidue_mem {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ) (v : I → ZMod m) :
    v ∈ residueLatticeImage A.mulVecLin.range m ↔
      ∃ x : J → ZMod m, integerResidueMatrix A m *ᵥ x = v := by
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, hy⟩
    exact ⟨integerResidueMap J m x, (integerResidueMap_mulVec A m x).symm.trans hy⟩
  · rintro ⟨x, hx⟩
    obtain ⟨z, hz⟩ := integerResidueMap_surjective J m x
    refine ⟨A *ᵥ z, ⟨z, rfl⟩, ?_⟩
    rw [integerResidueMap_mulVec, hz, hx]

theorem integerMatrixResidue_image_eq {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (m : ℕ) :
    residueLatticeImage A.mulVecLin.range m =
      (integerResidueMatrix A m).mulVecLin.range.restrictScalars ℤ := by
  ext v
  exact integerMatrixResidue_mem A m v

theorem integerMatrixImage_eq_of_residueMatrix {I J : Type*} [Fintype I] [Fintype J]
    (A B : Matrix I J ℤ) (m : ℕ)
    (hA : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hB : integerScalarLattice I (m : ℤ) ≤ B.mulVecLin.range)
    (hAB : integerResidueMatrix A m = integerResidueMatrix B m) :
    A.mulVecLin.range = B.mulVecLin.range := by
  apply residueLatticeImage_determines_lattice _ _ m hA hB
  rw [integerMatrixResidue_image_eq, integerMatrixResidue_image_eq, hAB]

end Erdos3

end

section

namespace Erdos3

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixSupInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Erdos3

end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BinaryDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem binaryDensity_integrable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite ν] {f : X → ℝ} {g : Y → ℝ}
    (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (binaryDensity f g) (μ.prod ν) := hf.mul_prod hg

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SampledWeightCellLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

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
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

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

theorem continuousDensity_eq_of_measure_eq {I : Type*} [Fintype I]
    {f g : (I → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (he : realDensityMeasure volume f = realDensityMeasure volume g) : f = g := by
  have hae := (withDensity_eq_iff_of_sigmaFinite
    hf.measurable.ennreal_ofReal.aemeasurable hg.measurable.ennreal_ofReal.aemeasurable).mp he
  apply (hf.ae_eq_iff_eq volume hg).mp
  filter_upwards [hae] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (hf0 x) (hg0 x)).mp hx

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ENNReal

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalDensityTransport
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*}

variable [Fintype ι]

theorem inverse_map_volume (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    Measure.map A.symm volume = ENNReal.ofReal ((inverseJacobian A)⁻¹) • volume := by
  have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    A.symm.toLinearEquiv.isUnit_det'.ne_zero
  simpa only [inverseJacobian, abs_inv, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PivotCoordinateChange
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotCoordinateChange_inverse_map (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) :
    Measure.map (pivotCoordinateChange A B).symm volume =
      ENNReal.ofReal ((inverseJacobian A)⁻¹) • volume := by
  have hs (y : J → ℝ) :
      Measure.map (fun x => A.symm (x - B y)) volume =
        ENNReal.ofReal ((inverseJacobian A)⁻¹) • volume := by
    have ht : Measure.map (fun x : I → ℝ => x - B y) volume = volume := by
      simpa only [sub_eq_add_neg] using (measurePreserving_add_right volume (-B y)).map_eq
    rw [show (fun x => A.symm (x - B y)) = A.symm ∘ (fun x => x - B y) from rfl,
      ← Measure.map_map A.symm.continuous.measurable (by fun_prop), ht]
    exact inverse_map_volume A
  have hp := (MeasurePreserving.id (volume : Measure (J → ℝ))).skew_product
    (g := fun y x => A.symm (x - B y)) (by fun_prop) (Filter.Eventually.of_forall hs)
  change Measure.map (fun p : (J → ℝ) × (I → ℝ) => (p.1, A.symm (p.2 - B p.1)))
    (volume.prod volume) = _
  simpa only [id_eq, Measure.prod_smul_right, Measure.volume_eq_prod] using hp.map_eq

theorem integral_comp_inverse_pivot (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) :
    (∫ p, f ((pivotCoordinateChange A B).symm p)) =
      (inverseJacobian A)⁻¹ * ∫ p, f p := by
  have h := (pivotCoordinateChange A B).symm.measurableEmbedding.integral_map
    (μ := volume) f
  rw [pivotCoordinateChange_inverse_map, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (inverseJacobian_pos A).le)] at h
  exact h.symm

theorem pivotDensityPullback_integrable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Integrable f) : Integrable (pivotDensityPullback A B f) := by
  have hm : Integrable f (Measure.map (pivotCoordinateChange A B).symm volume) := by
    rw [pivotCoordinateChange_inverse_map]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact ((pivotCoordinateChange A B).symm.measurableEmbedding.integrable_map_iff.mp hm).const_mul _

theorem pivotDensityPullback_integral (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) :
    (∫ p, pivotDensityPullback A B f p) = ∫ p, f p := by
  unfold pivotDensityPullback
  rw [integral_const_mul, integral_comp_inverse_pivot, ← mul_assoc,
    mul_inv_cancel₀ (inverseJacobian_pos A).ne', one_mul]

theorem pivotDensityPullback_test_integral (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f φ : (J → ℝ) × (I → ℝ) → ℝ) :
    (∫ p, pivotDensityPullback A B f p * φ p) =
      ∫ p, f p * φ ((pivotCoordinateChange A B) p) := by
  have heq (p : (J → ℝ) × (I → ℝ)) :
      pivotDensityPullback A B f p * φ p =
        pivotDensityPullback A B (fun q => f q * φ (pivotCoordinateChange A B q)) p := by
    simp only [pivotDensityPullback, Homeomorph.apply_symm_apply, mul_assoc]
  simp_rw [heq]
  exact pivotDensityPullback_integral A B _

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

omit [Fintype I] in
theorem pivotOutputDensity_nonneg (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : ∀ p, 0 ≤ f p) (v : I → ℝ) : 0 ≤ pivotOutputDensity A B f v :=
  integral_nonneg fun _ => mul_nonneg (inverseJacobian_pos A).le (hf _)

theorem pivotOutputDensity_integrable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Integrable f) : Integrable (pivotOutputDensity A B f) :=
  (pivotDensityPullback_integrable A B hf).integral_prod_right

theorem pivotOutputDensity_test_integral (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Integrable f) (φ : (I → ℝ) → ℝ) (hφ : Measurable φ)
    {C : ℝ} (hC : ∀ v, ‖φ v‖ ≤ C) :
    (∫ v, pivotOutputDensity A B f v * φ v) =
      ∫ p, f p * φ (A p.2 + B p.1) := by
  have hi : Integrable (fun p : (J → ℝ) × (I → ℝ) => pivotDensityPullback A B f p * φ p.2) :=
    (pivotDensityPullback_integrable A B hf).mul_bdd
      (hφ.comp measurable_snd).aestronglyMeasurable (Filter.Eventually.of_forall fun p => hC p.2)
  calc
    _ = ∫ v, ∫ y, pivotDensityPullback A B f (y, v) * φ v := by
      apply integral_congr_ae
      filter_upwards [] with v
      exact (integral_mul_const _ _).symm
    _ = ∫ p : (J → ℝ) × (I → ℝ), pivotDensityPullback A B f p * φ p.2 :=
      (integral_prod_symm _ hi).symm
    _ = _ := pivotDensityPullback_test_integral A B f (fun p => φ p.2)

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

theorem pivotOutputDensity_law {I J : Type*} [Fintype I] [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} (hf : Integrable f) (hf0 : ∀ p, 0 ≤ f p) :
    Measure.map (fun p => A p.2 + B p.1) (realDensityMeasure volume f) =
      realDensityMeasure volume (pivotOutputDensity A B f) := by
  have hm : Measurable (fun p : (J → ℝ) × (I → ℝ) => A p.2 + B p.1) := by fun_prop
  ext s hs
  rw [Measure.map_apply hm hs, realDensityMeasure_apply volume f hf hf0 (hm hs),
    realDensityMeasure_apply volume _ (pivotOutputDensity_integrable A B hf)
      (pivotOutputDensity_nonneg A B hf0) hs]
  congr 1
  have h := pivotOutputDensity_test_integral A B hf (s.indicator (fun _ => 1))
    (measurable_const.indicator hs) (C := 1) (fun x => by
      by_cases hx : x ∈ s <;> simp [hx])
  have hl (v : I → ℝ) :
      pivotOutputDensity A B f v * s.indicator (fun _ => 1) v =
        s.indicator (pivotOutputDensity A B f) v := by
    by_cases hv : v ∈ s <;> simp [hv]
  have hr (p : (J → ℝ) × (I → ℝ)) :
      f p * s.indicator (fun _ => 1) (A p.2 + B p.1) =
        ((fun p : (J → ℝ) × (I → ℝ) => A p.2 + B p.1) ⁻¹' s).indicator f p := by
    by_cases hp : A p.2 + B p.1 ∈ s <;> simp [hp]
  simp_rw [hl, hr] at h
  rw [integral_indicator hs, integral_indicator (hm hs)] at h
  exact h.symm

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

theorem splitInputProfile_lipschitz {f : (J → ℝ) × (I → ℝ) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : LipschitzWith K (splitInputProfile f) := by
  have hs : LipschitzWith 1 (fun x : J ⊕ I → ℝ =>
      ((fun j => x (.inl j)), (fun i => x (.inr i)))) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact (splitCoordinates_norm (x - y)).le
  unfold splitInputProfile
  simpa only [mul_one, Function.comp_def] using hf.comp hs

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

theorem normalizedFiberDensity_law {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    {f : (J → ℝ) × (I → ℝ) → ℝ} (hf : Integrable f) (hf0 : ∀ p, 0 ≤ f p) :
    Measure.map (fun p : (J → ℝ) × (I → ℝ) =>
      normalizedIntegerPivot A S P *ᵥ p.2 + normalizedIntegerColumns B T P *ᵥ p.1)
      (realDensityMeasure volume f) =
      realDensityMeasure volume (normalizedFiberDensity A hA B S P T hS hP f) := by
  have he : (fun p : (J → ℝ) × (I → ℝ) =>
      (normalizedPivotEquiv A hA S P hS hP) p.2 +
        matrixSupCLM (normalizedIntegerColumns B T P) p.1) =
      fun p : (J → ℝ) × (I → ℝ) =>
        normalizedIntegerPivot A S P *ᵥ p.2 + normalizedIntegerColumns B T P *ᵥ p.1 := by
    funext p
    change (normalizedPivotEquiv A hA S P hS hP).toContinuousLinearMap p.2 + _ = _
    rw [normalizedPivotEquiv_coe, matrixSupCLM_apply, matrixSupCLM_apply]
  rw [← he]
  exact pivotOutputDensity_law _ _ hf hf0

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

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

omit [Fintype I] [Fintype J] [Fintype N] in
theorem splitFreeProfile_nonneg {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : ∀ p, 0 ≤ f p) (hg : ∀ n, 0 ≤ g n) (p) :
    0 ≤ splitFreeProfile f g p := mul_nonneg (hf _) (hg _)

theorem splitFreeProfile_zero_outside {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} {R S : ℝ}
    (hf : ∀ p, R < ‖p‖ → f p = 0) (hg : ∀ n, S < ‖n‖ → g n = 0)
    (p : (J ⊕ N → ℝ) × (I → ℝ)) (hp : max R S < ‖p‖) :
    splitFreeProfile f g p = 0 := by
  let y : J → ℝ := fun j => p.1 (.inl j)
  let n : N → ℝ := fun n => p.1 (.inr n)
  by_cases hy : R < ‖(y, p.2)‖
  · exact mul_eq_zero_of_left (hf _ hy) _
  · have hn : S < ‖n‖ := by
      by_contra! hn
      have hy' : ‖(y, p.2)‖ ≤ R := le_of_not_gt hy
      have hnorm : ‖p‖ ≤ max R S := by
        rw [Prod.norm_def]
        apply max_le
        · rw [← splitCoordinates_norm p.1, Prod.norm_def]
          exact max_le ((norm_fst_le (y, p.2)).trans (hy'.trans (le_max_left _ _)))
            (hn.trans (le_max_right _ _))
        · exact (norm_snd_le (y, p.2)).trans (hy'.trans (le_max_left _ _))
      exact (not_le_of_gt hp) hnorm
    exact mul_eq_zero_of_right _ (hg _ hn)

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

theorem normalizedIntegerColumns_fromCols (B : Matrix I J ℤ) (C : Matrix I N ℤ)
    (T : J → ℝ) (Q : N → ℝ) (P : I → ℝ) :
    normalizedIntegerColumns (Matrix.fromCols B C) (Sum.elim T Q) P =
      Matrix.fromCols (normalizedIntegerColumns B T P) (normalizedIntegerColumns C Q P) := by
  ext i k
  cases k <;> simp [normalizedIntegerColumns_entry]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

theorem splitFreeCoordinates_norm_le (p : (J ⊕ N → ℝ) × (I → ℝ)) :
    ‖((fun j => p.1 (.inl j)), p.2)‖ ≤ ‖p‖ ∧
      ‖fun n => p.1 (.inr n)‖ ≤ ‖p‖ := by
  have hleft : ‖fun j => p.1 (.inl j)‖ ≤ ‖p.1‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => norm_le_pi_norm p.1 (.inl j)
  have hright : ‖fun n => p.1 (.inr n)‖ ≤ ‖p.1‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun n => norm_le_pi_norm p.1 (.inr n)
  refine ⟨?_, hright.trans (norm_fst_le p)⟩
  rw [Prod.norm_def]
  exact max_le (hleft.trans (norm_fst_le p)) (norm_snd_le p)

theorem splitFreeProfile_lipschitz {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} {Kf Kg Hf Hg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfcap : ∀ p, ‖f p‖ ≤ Hf) (hgcap : ∀ n, ‖g n‖ ≤ Hg) :
    LipschitzWith (Hf * Kg + Hg * Kf) (splitFreeProfile f g) := by
  let F := fun p : (J ⊕ N → ℝ) × (I → ℝ) => f ((fun j => p.1 (.inl j)), p.2)
  let G := fun p : (J ⊕ N → ℝ) × (I → ℝ) => g (fun n => p.1 (.inr n))
  have hkernel : LipschitzWith 1 (fun p : (J ⊕ N → ℝ) × (I → ℝ) =>
      ((fun j => p.1 (.inl j)), p.2)) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact (splitFreeCoordinates_norm_le (p - q)).1
  have hnonkernel : LipschitzWith 1 (fun p : (J ⊕ N → ℝ) × (I → ℝ) =>
      fun n => p.1 (.inr n)) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact (splitFreeCoordinates_norm_le (p - q)).2
  have hF : LipschitzWith Kf F := by simpa only [mul_one, Function.comp_def] using hf.comp hkernel
  have hG : LipschitzWith Kg G := by simpa only [mul_one, Function.comp_def] using hg.comp hnonkernel
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change dist (F p * G p) (F q * G q) ≤ _
  rw [dist_eq_norm]
  have heq : F p * G p - F q * G q = F p * (G p - G q) + (F p - F q) * G q := by ring
  rw [heq]
  calc
    _ ≤ ‖F p * (G p - G q)‖ + ‖(F p - F q) * G q‖ := norm_add_le _ _
    _ = ‖F p‖ * ‖G p - G q‖ + ‖F p - F q‖ * ‖G q‖ := by rw [norm_mul, norm_mul]
    _ ≤ Hf * (Kg * dist p q) + (Kf * dist p q) * Hg := by
      apply add_le_add
      · exact mul_le_mul (hfcap _) (by simpa only [dist_eq_norm] using hG.dist_le_mul p q)
          (norm_nonneg _) Hf.coe_nonneg
      · exact mul_le_mul (by simpa only [dist_eq_norm] using hF.dist_le_mul p q) (hgcap _)
          (norm_nonneg _) (mul_nonneg Kf.coe_nonneg dist_nonneg)
    _ = _ := by push_cast; ring

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem selectedCoefficientProfile_nonneg {I J : Type*} [Fintype I]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∀ p, 0 ≤ selectedCoefficientProfile s f p := fun p => hf (selectedCoefficientEquiv s ℝ p)

theorem selectedCoefficientProfile_norm_le {I J : Type*} [Fintype I]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} {H : ℝ} (hf : ∀ x, ‖f x‖ ≤ H) :
    ∀ p, ‖selectedCoefficientProfile s f p‖ ≤ H := fun p => hf (selectedCoefficientEquiv s ℝ p)

theorem selectedCoefficientProfile_lipschitz {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (selectedCoefficientProfile s f) := by
  simpa only [mul_one, selectedCoefficientProfile] using hf.comp (selectedCoefficientEquiv_lipschitz s)

theorem selectedCoefficientProfile_zero_outside {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} {R : ℝ}
    (hf : ∀ x, R < ‖x‖ → f x = 0) :
    ∀ p, R < ‖p‖ → selectedCoefficientProfile s f p = 0 := by
  intro p hp
  exact hf _ (by rwa [selectedCoefficientEquiv_norm])

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

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

namespace Erdos3

open scoped NNReal

end Erdos3

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

theorem integerResidueMatrix_fromCols {I J N : Type*}
    (B : Matrix I J ℤ) (C : Matrix I N ℤ) (m : ℕ) :
    integerResidueMatrix (Matrix.fromCols B C) m =
      Matrix.fromCols (integerResidueMatrix B m) (integerResidueMatrix C m) := by
  ext i k
  cases k <;> rfl

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

end Erdos3

namespace Erdos3

open scoped Matrix Classical

end Erdos3

namespace Erdos3

open scoped Classical

end Erdos3

namespace Erdos3

open scoped BigOperators

theorem liftResidueMatrix_residue {I N : Type*} {m : ℕ} (r : Matrix I N (ZMod m)) :
    integerResidueMatrix (liftResidueMatrix r) m = r := by
  ext i n
  exact (ZMod.intCast_surjective (r i n)).choose_spec

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScaleIndependence
namespace OAI

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

theorem normalizedIntegerColumns_submatrix {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (S : J → ℝ) (P : I → ℝ) (p : I → J) :
    (normalizedIntegerColumns A S P).submatrix id p =
      normalizedIntegerPivot (A.submatrix id p) (fun i => S (p i)) P := by
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, normalizedIntegerColumns_entry_div,
    normalizedIntegerPivot_entry]

open scoped Matrix

theorem selectedMatrix_fromCols {I J R : Type*} [Fintype I]
    (A : Matrix I J R) (s : I ↪ J) :
    Matrix.fromCols (A.submatrix id s) (remainingMatrixColumns A s) =
      A.submatrix id (selectedColumnEquiv s) := by
  ext i j
  cases j <;> rfl

theorem normalized_remainingMatrixColumns {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (P : I → ℝ) :
    normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P =
      remainingMatrixColumns (normalizedIntegerColumns A S P) s := by
  classical
  ext i j
  simp only [remainingMatrixColumns, Matrix.submatrix_apply, id_eq,
    normalizedIntegerColumns_entry_div]

end Erdos3

namespace Erdos3

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowReindex
namespace OAI

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

namespace Erdos3

theorem coefficientImageMask_eq_multiplier {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (P : I → ℝ) (f : (I → ℝ) → ℝ) (v : I → ℤ) :
    coefficientImageMask A P f v = coefficientImageMultiplier A v * f (fun i => (v i : ℝ)/P i) := by
  classical
  by_cases hv : v ∈ A.mulVecLin.range <;> simp [coefficientImageMask, coefficientImageMultiplier, hv]

theorem coefficientImageMultiplier_nonneg {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (v : I → ℤ) : 0 ≤ coefficientImageMultiplier A v := by
  classical
  unfold coefficientImageMultiplier
  split <;> positivity

theorem coefficientImageMultiplier_le_index {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (v : I → ℤ) :
    coefficientImageMultiplier A v ≤ (A.mulVecLin.range.toAddSubgroup.index : ℝ) := by
  classical
  unfold coefficientImageMultiplier
  split <;> simp

theorem integerFromCols_image_eq_of_kernel_residues {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I J ℤ) (C D : Matrix I N ℤ) (m : ℕ)
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hCD : integerResidueMatrix C m = integerResidueMatrix D m) :
    (Matrix.fromCols A C).mulVecLin.range = (Matrix.fromCols A D).mulVecLin.range := by
  apply integerMatrixImage_eq_of_residueMatrix _ _ m
  · rw [integerMatrix_fromCols_range]
    exact hperiod.trans le_sup_left
  · rw [integerMatrix_fromCols_range]
    exact hperiod.trans le_sup_left
  · simp only [integerResidueMatrix_fromCols, hCD]

theorem coefficientImageMultiplier_eq_residue {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I J ℤ) (C : Matrix I N ℤ) (m : ℕ) (r : Matrix I N (ZMod m))
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hr : integerResidueMatrix C m = r) (v : I → ℤ) :
    coefficientImageMultiplier (Matrix.fromCols A C) v = coefficientResidueMultiplier A r v := by
  classical
  have he := integerFromCols_image_eq_of_kernel_residues A C (liftResidueMatrix r) m hperiod
    (by rw [liftResidueMatrix_residue, hr])
  unfold coefficientImageMultiplier coefficientResidueMultiplier
  simp only [coefficientImageMultiplier, he]

theorem coefficientResidueMultiplier_bounds {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I J ℤ) (C : Matrix I N ℤ) (m : ℕ) (r : Matrix I N (ZMod m))
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hr : integerResidueMatrix C m = r) {G : ℝ}
    (hG : ((Matrix.fromCols A C).mulVecLin.range.toAddSubgroup.index : ℝ) ≤ G) (v : I → ℤ) :
    0 ≤ coefficientResidueMultiplier A r v ∧ coefficientResidueMultiplier A r v ≤ G := by
  rw [← coefficientImageMultiplier_eq_residue A C m r hperiod hr v]
  exact ⟨coefficientImageMultiplier_nonneg _ _, (coefficientImageMultiplier_le_index _ _).trans hG⟩

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

namespace Erdos3

open scoped Matrix

variable {I I' J : Type*} [Fintype J]

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SelectedDensityNormalization
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem selectedCoefficientMeasurableEquiv_preserving {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) : MeasurePreserving (selectedCoefficientMeasurableEquiv s) volume volume := by
  have hm := (volume_measurePreserving_piCongrLeft (fun _ : J => ℝ) (selectedFreeFirstEquiv s)).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : UnselectedColumn s ⊕ I => ℝ))
  convert hm using 1
  funext p j
  simp only [Function.comp_def, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft', Equiv.coe_fn_symm_mk, eq_rec_constant]
  rfl

theorem selectedCoefficientProfile_measure {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) :
    (realDensityMeasure volume (selectedCoefficientProfile s f)).map (selectedCoefficientMeasurableEquiv s) =
      realDensityMeasure volume f := by
  rw [realDensityMeasure_map_equiv, (selectedCoefficientMeasurableEquiv_preserving s).map_eq]
  congr 1
  funext x
  change f ((selectedCoefficientMeasurableEquiv s) ((selectedCoefficientMeasurableEquiv s).symm x)) = f x
  rw [MeasurableEquiv.apply_symm_apply]

theorem selectedCoefficientProfile_integrable {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} (hf : Integrable f) :
    Integrable (selectedCoefficientProfile s f) :=
  (selectedCoefficientMeasurableEquiv_preserving s).integrable_comp_of_integrable hf

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

theorem selectedCoefficient_matrix_apply {I J R : Type*} [Fintype I] [Fintype J] [CommRing R]
    (A : Matrix I J R) (s : I ↪ J) (p : (UnselectedColumn s → R) × (I → R)) :
    A *ᵥ selectedCoefficientEquiv s R p =
      A.submatrix id s *ᵥ p.2 + remainingMatrixColumns A s *ᵥ p.1 := by
  have he : selectedCoefficientEquiv s R p = Sum.elim p.2 p.1 ∘ (selectedColumnEquiv s).symm := by
    funext j
    change Sum.elim p.1 p.2 ((Equiv.sumComm _ _) ((selectedColumnEquiv s).symm j)) =
      Sum.elim p.2 p.1 ((selectedColumnEquiv s).symm j)
    cases (selectedColumnEquiv s).symm j <;> rfl
  rw [he]
  have hm := Matrix.submatrix_mulVec_equiv A (Sum.elim p.2 p.1) id (selectedColumnEquiv s)
  rw [← selectedMatrix_fromCols, Matrix.fromCols_mulVec] at hm
  exact hm.symm

theorem selectedCoefficientDensity_law {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x) :
    (realDensityMeasure volume f).map (fun x => normalizedIntegerColumns A S P *ᵥ x) =
      realDensityMeasure volume (selectedCoefficientDensity A s hA S P hS hP f) := by
  classical
  have hmap : (fun p : (UnselectedColumn s → ℝ) × (I → ℝ) =>
      normalizedIntegerPivot (A.submatrix id s) (fun i => S (s i)) P *ᵥ p.2 +
        normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P *ᵥ p.1) =
      (fun x => normalizedIntegerColumns A S P *ᵥ x) ∘ selectedCoefficientMeasurableEquiv s := by
    funext p
    change _ = normalizedIntegerColumns A S P *ᵥ selectedCoefficientEquiv s ℝ p
    rw [selectedCoefficient_matrix_apply, normalizedIntegerColumns_submatrix,
      ← normalized_remainingMatrixColumns]
  have hF : Measurable (fun x => normalizedIntegerColumns A S P *ᵥ x) :=
    (matrixSupCLM (normalizedIntegerColumns A S P)).continuous.measurable
  rw [← selectedCoefficientProfile_measure s f,
    Measure.map_map hF
      (selectedCoefficientMeasurableEquiv s).measurable, ← hmap]
  exact normalizedFiberDensity_law _ _ _ _ _ _ _ _
    (selectedCoefficientProfile_integrable s hf) (selectedCoefficientProfile_nonneg s hf0)

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

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JoinedCoefficientProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem joinedCoefficientProfile_nonneg {J N : Type*}
    {f : (J → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ y, 0 ≤ g y) (x) :
    0 ≤ joinedCoefficientProfile f g x := mul_nonneg (hf _) (hg _)

theorem joinedCoefficientProfile_lipschitz {J N : Type*} [Fintype J] [Fintype N]
    {f : (J → ℝ) → ℝ} {g : (N → ℝ) → ℝ} (H Q K L : ℝ≥0)
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfr : ∀ x, f x ∈ Set.Icc (0 : ℝ) H) (hgr : ∀ y, g y ∈ Set.Icc (0 : ℝ) Q) :
    LipschitzWith (Q*K+H*L) (joinedCoefficientProfile f g) :=
  splitInputProfile_lipschitz (binaryDensity_lipschitz f g H Q K L hfr hgr hf hg)

theorem joinedCoefficientProfile_zero_outside {J N : Type*} [Fintype J] [Fintype N]
    {f : (J → ℝ) → ℝ} {g : (N → ℝ) → ℝ} {R S : ℝ}
    (hfs : ∀ x, R < ‖x‖ → f x = 0) (hgs : ∀ y, S < ‖y‖ → g y = 0) :
    ∀ x, max R S < ‖x‖ → joinedCoefficientProfile f g x = 0 := by
  intro x hx
  rw [← splitCoordinates_norm x, Prod.norm_def] at hx
  rcases lt_max_iff.mp hx with h | h
  · exact mul_eq_zero_of_left (hfs _ ((le_max_left R S).trans_lt h)) _
  · exact mul_eq_zero_of_right _ (hgs _ ((le_max_right R S).trans_lt h))

theorem joinedCoefficientProfile_integrable {J N : Type*} [Fintype J] [Fintype N]
    {f : (J → ℝ) → ℝ} {g : (N → ℝ) → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (joinedCoefficientProfile f g) :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).integrable_comp_of_integrable
    (binaryDensity_integrable hf hg)

theorem joinedCoefficientProfile_measure {J N : Type*} [Fintype J] [Fintype N]
    (f : (J → ℝ) → ℝ) (g : (N → ℝ) → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x) :
    ((realDensityMeasure volume f).prod (realDensityMeasure volume g)).map
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).symm =
      realDensityMeasure volume (joinedCoefficientProfile f g) := by
  rw [binaryDensity_measure volume volume f g hf hg hf0,
    ← Measure.volume_eq_prod,
    realDensityMeasure_map_equiv,
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : J ⊕ N => ℝ)).map_eq]
  rfl

theorem affineProductProfile_joined {J N : Type*} [Fintype J] [Fintype N]
    (c w : J ⊕ N → ℝ) :
    affineProductProfile c w = joinedCoefficientProfile
      (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j)))
      (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n))) := by
  funext x
  simp only [affineProductProfile, joinedCoefficientProfile, Fintype.prod_sum_type]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SplitFreeCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem splitFreeCoordinates_preserving (I J N : Type*) [Fintype I] [Fintype J] [Fintype N] :
    MeasurePreserving (splitFreeCoordinates I J N) volume volume := by
  have h₁ := (volume_measurePreserving_sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).prod
    (MeasurePreserving.id (volume : Measure (I → ℝ)))
  have h₂ : MeasurePreserving
      (MeasurableEquiv.prodAssoc : ((J → ℝ) × (N → ℝ)) × (I → ℝ) ≃ᵐ _)
      volume volume := volume_preserving_prodAssoc
  have h₃ := (MeasurePreserving.id (volume : Measure (J → ℝ))).prod
    (Measure.measurePreserving_swap (μ := (volume : Measure (N → ℝ))) (ν := (volume : Measure (I → ℝ))))
  have h₄ : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm : (J → ℝ) × ((I → ℝ) × (N → ℝ)) ≃ᵐ _)
      volume volume := volume_preserving_prodAssoc.symm MeasurableEquiv.prodAssoc
  exact h₄.comp (h₃.comp (h₂.comp h₁))

theorem splitFreeProfile_measure {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (f : (J → ℝ) × (I → ℝ) → ℝ) (g : (N → ℝ) → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ p, 0 ≤ f p) :
    (realDensityMeasure volume (splitFreeProfile f g)).map (splitFreeCoordinates I J N) =
      (realDensityMeasure volume f).prod (realDensityMeasure volume g) := by
  rw [realDensityMeasure_map_equiv, (splitFreeCoordinates_preserving I J N).map_eq,
    binaryDensity_measure volume volume f g hf hg hf0]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedFiniteComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteProbability_exists_nonzero_weight {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) : ∃ x, p.weight x ≠ 0 := by
  by_contra! h
  have he := p.total
  simp only [h, Finset.sum_const_zero] at he
  norm_num at he

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientDensitySplit
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

theorem selectedSplitCoefficients_measurable {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J) :
    Measurable (selectedSplitCoefficients (N := N) s) := by
  change Measurable ((MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).symm ∘
    (Prod.map (selectedCoefficientMeasurableEquiv s) id ∘
      splitFreeCoordinates I (UnselectedColumn s) N))
  exact (MeasurableEquiv.measurable _).comp
    (((selectedCoefficientMeasurableEquiv s).measurable.prodMap measurable_id).comp
      (splitFreeCoordinates I (UnselectedColumn s) N).measurable)

theorem selectedSplitCoefficients_law {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J)
    (f : (J → ℝ) → ℝ) (g : (N → ℝ) → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hfi : Integrable f) (hgi : Integrable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (realDensityMeasure volume (splitFreeProfile (selectedCoefficientProfile s f) g)).map
        (selectedSplitCoefficients s) =
      realDensityMeasure volume (joinedCoefficientProfile f g) := by
  let : IsFiniteMeasure (realDensityMeasure volume (selectedCoefficientProfile s f)) :=
    realDensityMeasure_finite _ _ (selectedCoefficientProfile_integrable s hfi)
      (selectedCoefficientProfile_nonneg s hf0)
  let : IsFiniteMeasure (realDensityMeasure volume g) := realDensityMeasure_finite _ _ hgi hg0
  have hsel : Measurable (selectedCoefficientProfile s f) :=
    hf.comp (selectedCoefficientMeasurableEquiv s).measurable
  have hprod := (selectedCoefficientMeasurableEquiv s).measurable.prodMap
    (measurable_id : Measurable (id : (N → ℝ) → (N → ℝ)))
  change Measure.map ((MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ N => ℝ)).symm ∘
    (Prod.map (selectedCoefficientMeasurableEquiv s) id ∘
      splitFreeCoordinates I (UnselectedColumn s) N)) _ = _
  rw [← Measure.map_map (MeasurableEquiv.measurable _) (hprod.comp (MeasurableEquiv.measurable _)),
    ← Measure.map_map hprod (MeasurableEquiv.measurable _),
    splitFreeProfile_measure _ _ hsel hg (selectedCoefficientProfile_nonneg s hf0),
    ← Measure.map_prod_map _ _ (selectedCoefficientMeasurableEquiv s).measurable measurable_id,
    selectedCoefficientProfile_measure s f, Measure.map_id,
    joinedCoefficientProfile_measure f g hf hg hf0]

theorem selectedSplitCoefficients_matrix {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I J ℝ) (C : Matrix I N ℝ) (s : I ↪ J)
    (p : (UnselectedColumn s ⊕ N → ℝ) × (I → ℝ)) :
    Matrix.fromCols A C *ᵥ selectedSplitCoefficients s p =
      A.submatrix id s *ᵥ p.2 + remainingMatrixColumns A s *ᵥ (fun j => p.1 (.inl j)) +
        C *ᵥ (fun n => p.1 (.inr n)) := by
  rw [Matrix.fromCols_mulVec]
  change A *ᵥ selectedCoefficientEquiv s ℝ ((fun j => p.1 (.inl j)), p.2) + _ = _
  rw [selectedCoefficient_matrix_apply]
  rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

theorem selectedSplitCoefficients_normalized_matrix {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (C : Matrix I N ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (T : N → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (p : (UnselectedColumn s ⊕ N → ℝ) × (I → ℝ)) :
    normalizedIntegerColumns (Matrix.fromCols A C) (Sum.elim S T) P *ᵥ selectedSplitCoefficients s p =
      normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) P (fun i => hS (s i)) hP p.2 +
        splitFreeColumns
          (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P))
          (matrixSupCLM (normalizedIntegerColumns C T P)) p.1 := by
  have he (x : I → ℝ) :
      normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) P (fun i => hS (s i)) hP x =
        normalizedIntegerPivot (A.submatrix id s) (fun i => S (s i)) P *ᵥ x := by
    change (normalizedPivotEquiv _ _ _ _ _ _).toContinuousLinearMap x = _
    rw [normalizedPivotEquiv_coe, matrixSupCLM_apply]
  rw [normalizedIntegerColumns_fromCols, selectedSplitCoefficients_matrix,
    normalizedIntegerColumns_submatrix, ← normalized_remainingMatrixColumns,
    he, splitFreeColumns_apply, matrixSupCLM_apply, matrixSupCLM_apply]
  exact add_assoc _ _ _

theorem coefficientSplitDensity_law {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (C : Matrix I N ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (T : N → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) (g : (N → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g)
    {R Q : ℝ} (hfs : ∀ x, R < ‖x‖ → f x = 0) (hgs : ∀ y, Q < ‖y‖ → g y = 0)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y) :
    (realDensityMeasure volume (joinedCoefficientProfile f g)).map
      (fun x => normalizedIntegerColumns (Matrix.fromCols A C) (Sum.elim S T) P *ᵥ x) =
      realDensityMeasure volume
        (pivotOutputDensity
          (normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) P (fun i => hS (s i)) hP)
          (splitFreeColumns
            (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P))
            (matrixSupCLM (normalizedIntegerColumns C T P)))
          (splitFreeProfile (selectedCoefficientProfile s f) g)) := by
  have hF : Measurable (fun x => normalizedIntegerColumns (Matrix.fromCols A C) (Sum.elim S T) P *ᵥ x) :=
    (matrixSupCLM _).continuous.measurable
  have hsel : Continuous (selectedCoefficientProfile s f) :=
    hf.comp (selectedCoefficientEquiv_lipschitz s).continuous
  rw [← selectedSplitCoefficients_law s f g hf.measurable hg.measurable
    (compactBox_integrable f hf R hfs) (compactBox_integrable g hg Q hgs) hf0 hg0,
    Measure.map_map hF (selectedSplitCoefficients_measurable s)]
  have he := funext (selectedSplitCoefficients_normalized_matrix A C s hA S T P hS hP)
  change (fun p => normalizedIntegerColumns (Matrix.fromCols A C) (Sum.elim S T) P *ᵥ
    selectedSplitCoefficients s p) = _ at he
  rw [show (fun x => normalizedIntegerColumns (Matrix.fromCols A C) (Sum.elim S T) P *ᵥ x) ∘
      selectedSplitCoefficients s = _ from he]
  exact pivotOutputDensity_law _ _
    (splitFreeProfile_integrable hsel hg (selectedCoefficientProfile_zero_outside s hfs) hgs)
    (splitFreeProfile_nonneg (selectedCoefficientProfile_nonneg s hf0) hg0)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem selectedCoefficientDensity_split {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (C : Matrix I N ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (hfull : ((Matrix.fromCols A C).submatrix id (s.trans Function.Embedding.inl)).det ≠ 0)
    (S : J → ℝ) (T : N → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hT : ∀ n, 0 < T n)
    (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) (g : (N → ℝ) → ℝ) (R Q H V K L : ℝ≥0)
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfr : ∀ x, f x ∈ Set.Icc (0 : ℝ) H) (hgr : ∀ y, g y ∈ Set.Icc (0 : ℝ) V)
    (hfs : ∀ x, (R : ℝ) < ‖x‖ → f x = 0) (hgs : ∀ y, (Q : ℝ) < ‖y‖ → g y = 0) :
    selectedCoefficientDensity (Matrix.fromCols A C) (s.trans Function.Embedding.inl) hfull
      (Sum.elim S T) P (Sum.rec hS hT) hP (joinedCoefficientProfile f g) =
      pivotOutputDensity
        (normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) P (fun i => hS (s i)) hP)
        (splitFreeColumns
          (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P))
          (matrixSupCLM (normalizedIntegerColumns C T P)))
        (splitFreeProfile (selectedCoefficientProfile s f) g) := by
  have hj := joinedCoefficientProfile_lipschitz H V K L hf hg hfr hgr
  have hjs := joinedCoefficientProfile_zero_outside hfs hgs
  have hfcap : ∀ x, ‖f x‖ ≤ H := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hfr x).1]
    exact (hfr x).2
  have hgcap : ∀ y, ‖g y‖ ≤ V := fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hgr y).1]
    exact (hgr y).2
  have hsplit := splitFreeProfile_lipschitz (selectedCoefficientProfile_lipschitz s hf) hg
    (selectedCoefficientProfile_norm_le s hfcap) hgcap
  have hss := splitFreeProfile_zero_outside (selectedCoefficientProfile_zero_outside s hfs) hgs
  have hj0 := joinedCoefficientProfile_nonneg (fun x => (hfr x).1) (fun y => (hgr y).1)
  have hs0 := splitFreeProfile_nonneg (selectedCoefficientProfile_nonneg s (fun x => (hfr x).1))
    (fun y => (hgr y).1)
  apply continuousDensity_eq_of_measure_eq
    (pivotOutputDensity_lipschitz _ _ (max R Q) _
      (selectedCoefficientProfile_lipschitz _ hj) (selectedCoefficientProfile_zero_outside _ hjs)).continuous
    (pivotOutputDensity_lipschitz _ _ (max R Q) _ hsplit hss).continuous
    (pivotOutputDensity_nonneg _ _ (selectedCoefficientProfile_nonneg _ hj0))
    (pivotOutputDensity_nonneg _ _ hs0)
  exact (selectedCoefficientDensity_law _ _ hfull (Sum.elim S T) P (Sum.rec hS hT) hP _
    (joinedCoefficientProfile_integrable
      (compactBox_integrable f hf.continuous R hfs) (compactBox_integrable g hg.continuous Q hgs)) hj0).symm.trans
    (coefficientSplitDensity_law A C s hA S T P hS hP f g hf.continuous hg.continuous hfs hgs
      (fun x => (hfr x).1) (fun y => (hgr y).1))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineL1Parameter
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem affineProductProfile_range_bound {J : Type*} [Fintype J]
    (c w : J → ℝ) {δ : ℝ≥0} (hδ : 0 < δ) (hw : ∀ j, (δ : ℝ) ≤ w j) (x : J → ℝ) :
    affineProductProfile c w x ∈ Set.Icc (0 : ℝ) ((δ⁻¹^Fintype.card J : ℝ≥0) : ℝ) := by
  have hwpos : ∀ j, 0 < w j := fun j => (show (0 : ℝ) < δ from hδ).trans_le (hw j)
  refine ⟨affineProductProfile_nonneg c w hwpos x, ?_⟩
  have hb := affineProductProfile_cap c w (show (0 : ℝ) < δ from hδ) hw x
  rw [Real.norm_eq_abs, abs_of_nonneg (affineProductProfile_nonneg c w hwpos x)] at hb
  simpa only [NNReal.coe_pow, NNReal.coe_inv] using hb

theorem affineCoefficientDensity_split {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (C : Matrix I N ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (hfull : ((Matrix.fromCols A C).submatrix id (s.trans Function.Embedding.inl)).det ≠ 0)
    (S : J → ℝ) (T : N → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hT : ∀ n, 0 < T n)
    (hP : ∀ i, 0 < P i) (c w : J ⊕ N → ℝ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hw : ∀ j, (δ : ℝ) ≤ w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R) :
    selectedCoefficientDensity (Matrix.fromCols A C) (s.trans Function.Embedding.inl) hfull
      (Sum.elim S T) P (Sum.rec hS hT) hP (affineProductProfile c w) =
      pivotOutputDensity
        (normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) P (fun i => hS (s i)) hP)
        (splitFreeColumns
          (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P))
          (matrixSupCLM (normalizedIntegerColumns C T P)))
        (splitFreeProfile
          (selectedCoefficientProfile s (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j))))
          (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n)))) := by
  have hwpos : ∀ j, 0 < w j := fun j => (show (0 : ℝ) < δ from hδ).trans_le (hw j)
  rw [affineProductProfile_joined]
  exact selectedCoefficientDensity_split A C s hA hfull S T P hS hT hP _ _ R R
    (δ⁻¹^Fintype.card J) (δ⁻¹^Fintype.card N) (affineProductProfileLip J δ) (affineProductProfileLip N δ)
    (affineProductProfile_lipschitz _ _ hδ (fun j => hw (.inl j)))
    (affineProductProfile_lipschitz _ _ hδ (fun n => hw (.inr n)))
    (affineProductProfile_range_bound _ _ hδ (fun j => hw (.inl j)))
    (affineProductProfile_range_bound _ _ hδ (fun n => hw (.inr n)))
    (affineProductProfile_zero_outside _ _ (fun j => hwpos (.inl j)) R.coe_nonneg (fun j => hsupport (.inl j)))
    (affineProductProfile_zero_outside _ _ (fun n => hwpos (.inr n)) R.coe_nonneg (fun n => hsupport (.inr n)))

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

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

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

open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientDensity
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem selectedCoefficientDensity_eq_kernel {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (C : Matrix I N ℤ) (T : N → ℝ) (hT : ∀ n, 0 < T n)
    (hfull : ((Matrix.fromCols A C).submatrix id (s.trans Function.Embedding.inl)).det ≠ 0)
    (c w : J ⊕ N → ℝ) {δ : ℝ≥0} (hδ : 0 < δ) (hw : ∀ j, (δ : ℝ) ≤ w j)
    (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R) :
    selectedCoefficientDensity (Matrix.fromCols A C) (s.trans Function.Embedding.inl) hfull
      (Sum.elim S T) P (Sum.rec hS hT) hP (affineProductProfile c w) =
      kernelCoefficientDensity A s hA S P hS hP C T c w :=
  affineCoefficientDensity_split A C s hA hfull S T P hS hT hP c w hδ hw R hsupport

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueCoefficientFamily
namespace OAI

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem affineCoefficientImage_residue_tolerance {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0) (C : Matrix I N ℤ)
    (S : J → ℝ) (T : N → ℝ) (hS : ∀ j, 0 < S j) (hT : ∀ n, 0 < T n)
    {H L B U G : ℝ} (h : ℕ)
    (ctrl : CoefficientFiberControl (Matrix.fromCols A C) (s.trans Function.Embedding.inl)
      (Sum.elim S T) H L h B U G)
    (hL : 0 < L) (hH : 0 < H) (hB0 : 0 ≤ B) (hU0 : 0 ≤ U) (hG0 : 0 ≤ G)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    {b t ε : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (hε : 0 < ε)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hB : B ≤ Real.exp b) (hR : (R : ℝ) ≤ Real.exp b)
    (hi : (δ : ℝ)⁻¹ ≤ Real.exp t)
    (hlarge : coefficientReplacementScale (J := J ⊕ N) (s.trans Function.Embedding.inl) b t ε L h ≤ H)
    (m : ℕ) (r : Matrix I N (ZMod m))
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range) (hr : integerResidueMatrix C m = r) :
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w) (Sum.elim S T), ∀ v,
      |H ^ Fintype.card I *
        (coefficientImagePMF (Matrix.fromCols A C) (affineProductProfile c w)
          (affineProductProfile_nonneg c w hw) (Sum.elim S T) (Sum.rec hS hT)
          (affineProductProfile_zero_outside c w hw R.coe_nonneg hsupport) hZ v).toReal -
        coefficientResidueMultiplier A r v *
          kernelCoefficientDensity A s hA S (fun _ => H) hS (fun _ => hH) C T c w
            (fun i => (v i : ℝ)/H)| ≤ ε := by
  obtain ⟨hZ, herr⟩ := affineCoefficientImage_tolerance (Matrix.fromCols A C)
    (s.trans Function.Embedding.inl) (Sum.elim S T) (Sum.rec hS hT) h ctrl hL hH hB0 hU0 hG0
    c w hw hδ hwidth R.coe_nonneg hsupport hb ht hε hG hU hB hR hi hlarge
  refine ⟨hZ, fun v => ?_⟩
  have he := herr v
  rw [coefficientImageMask_eq_multiplier,
    selectedCoefficientDensity_eq_kernel A s hA S (fun _ => H) hS (fun _ => hH) C T hT
      ctrl.det_ne_zero c w hδ hwidth R hsupport,
    coefficientImageMultiplier_eq_residue A C m r hperiod hr] at he
  exact he

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

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem affineCoefficientImage_residue_family {Ω I J N : Type*} [Fintype Ω]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (p : FiniteProbabilityWeights Ω)
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0) (C : Ω → Matrix I N ℤ)
    (S : J → ℝ) (T : N → ℝ) (hS : ∀ j, 0 < S j) (hT : ∀ n, 0 < T n)
    {H L B U G : ℝ} (h : ℕ)
    (ctrl : ∀ ω, p.weight ω ≠ 0 → CoefficientFiberControl (Matrix.fromCols A (C ω))
      (s.trans Function.Embedding.inl) (Sum.elim S T) H L h B U G)
    (hL : 0 < L) (hH : 0 < H) (hB0 : 0 ≤ B) (hU0 : 0 ≤ U) (hG0 : 0 ≤ G)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    {b t ε : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (hε : 0 < ε)
    (hG : G ≤ Real.exp b) (hU : U ≤ Real.exp b) (hB : B ≤ Real.exp b) (hR : (R : ℝ) ≤ Real.exp b)
    (hi : (δ : ℝ)⁻¹ ≤ Real.exp t)
    (hlarge : coefficientReplacementScale (J := J ⊕ N) (s.trans Function.Embedding.inl) b t ε L h ≤ H)
    (m : ℕ) (r : Matrix I N (ZMod m))
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hr : ∀ ω, p.weight ω ≠ 0 → integerResidueMatrix (C ω) m = r) :
    ∃ hZ : 0 < coefficientWeightSum (affineProductProfile c w) (Sum.elim S T),
      (∀ v, 0 ≤ coefficientResidueMultiplier A r v ∧ coefficientResidueMultiplier A r v ≤ G) ∧
      ∀ ω, p.weight ω ≠ 0 → ∀ v,
        |H ^ Fintype.card I *
          (coefficientImagePMF (Matrix.fromCols A (C ω)) (affineProductProfile c w)
            (affineProductProfile_nonneg c w hw) (Sum.elim S T) (Sum.rec hS hT)
            (affineProductProfile_zero_outside c w hw R.coe_nonneg hsupport) hZ v).toReal -
          coefficientResidueMultiplier A r v *
            kernelCoefficientDensity A s hA S (fun _ => H) hS (fun _ => hH)
              (C ω) T c w (fun i => (v i : ℝ)/H)| ≤ ε := by
  obtain ⟨ω₀, hω₀⟩ := finiteProbability_exists_nonzero_weight p
  obtain ⟨hZ, _⟩ := affineCoefficientImage_residue_tolerance A s hA (C ω₀) S T hS hT h (ctrl ω₀ hω₀)
    hL hH hB0 hU0 hG0 c w hw hδ hwidth R hsupport hb ht hε hG hU hB hR hi hlarge
    m r hperiod (hr ω₀ hω₀)
  refine ⟨hZ, ?_, ?_⟩
  · exact coefficientResidueMultiplier_bounds A (C ω₀) m r hperiod (hr ω₀ hω₀)
      (ctrl ω₀ hω₀).index_bound
  · intro ω hω v
    obtain ⟨_, herr⟩ := affineCoefficientImage_residue_tolerance A s hA (C ω) S T hS hT h (ctrl ω hω)
      hL hH hB0 hU0 hG0 c w hw hδ hwidth R hsupport hb ht hε hG hU hB hR hi hlarge
      m r hperiod (hr ω hω)
    exact herr v

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.affineCoefficientImage_residue_family.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.affineCoefficientImage_residue_family.{u_1, u_2, u_3, u_4}
