-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_image_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T02:50:42.217508+00:00
-- url     : https://prove2.me/submissions/8364e689-ecab-400b-83e0-7cab94bb2347

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B136

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_div {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) (a : ℝ) :
    booleanCoefficient (fun t => f t / a) s = booleanCoefficient f s / a := by
  simp only [booleanCoefficient, ← mul_div_assoc, Finset.sum_div]

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass
namespace OAI

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

open _root_.MvPolynomial
open scoped BigOperators Classical

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

theorem polynomialMonomial_eval {K I : Type*}
    (a : K → MvPolynomial I ℝ) (m : K →₀ ℕ) (x : I → ℝ) :
    MvPolynomial.eval x (polynomialMonomial a m) =
      ∏ k ∈ m.support, MvPolynomial.eval x (a k) ^ m k := by
  simp only [polynomialMonomial, map_prod, map_pow]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealKernelJetInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem realJetMatrix_apply_coefficients {α K O J : Type*} [DecidableEq α] [Fintype J]
    (basis : J → MvPolynomial K ℝ) (vertices : Finset α → K → ℝ)
    (rows : O → Finset α) (c : J → ℝ) (o : O) :
    (realJetMatrix basis vertices rows *ᵥ c) o =
      booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
        (∑ j, MvPolynomial.C (c j) * basis j)) (rows o) := by
  simp only [map_sum, map_mul, MvPolynomial.eval_C,
    booleanCoefficient_sum, booleanCoefficient_const_mul]
  change (∑ j, realJetMatrix basis vertices rows o j * c j) = _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BooleanAffineInput
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanAffineInput_eval {I α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → MvPolynomial I ℝ) (t : Finset α) (x : I → ℝ) :
    MvPolynomial.eval x (booleanAffineInput a t) =
      ∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (a r) := by
  simp only [booleanAffineInput, map_sum, map_mul, MvPolynomial.eval_C]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem booleanJetColumnPolynomial_eval {K P α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ) (s : Finset α) (x : P → ℝ) :
    MvPolynomial.eval x (booleanJetColumnPolynomial e input s) =
      booleanCoefficient (fun t => ∏ k ∈ e.support,
        (∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (input k r)) ^ e k) s := by
  simp only [booleanJetColumnPolynomial, booleanCoefficient_map, polynomialMonomial_eval, booleanAffineInput_eval]

theorem booleanJetColumns_apply_coefficients {K P α O J : Type*} [Fintype α] [DecidableEq α]
    [Fintype O] [Fintype J] (e : J → K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ)
    (rows : O → Finset α) (x : P → ℝ) (c : J → ℝ) (o : O) :
    polynomialColumns (fun o j => booleanJetColumnPolynomial (e j) input (rows o)) x c o =
      booleanCoefficient (fun t => ∑ j, c j * ∏ k ∈ (e j).support,
        (∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (input k r)) ^ e j k) (rows o) := by
  simp only [booleanCoefficient_sum, booleanCoefficient_const_mul]
  change (∑ j, MvPolynomial.eval x (booleanJetColumnPolynomial (e j) input (rows o)) * c j) = _
  apply Finset.sum_congr rfl
  intro j _
  rw [booleanJetColumnPolynomial_eval, mul_comm]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SigmaAxisCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] (I : D → Type*) [∀ d, Fintype (I d)]

theorem sigmaAxisCoordinates_symm_measurePreserving :
    MeasurePreserving (sigmaAxisCoordinates I).symm volume volume := by
  refine ⟨(sigmaAxisCoordinates I).symm.continuous.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (sigmaAxisCoordinates I).symm.continuous.measurable (MeasurableSet.univ_pi hs)]
  have he : (sigmaAxisCoordinates I).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun d => Set.univ.pi (fun i : I d => s ⟨d, i⟩)) := by
    ext x
    constructor
    · intro hx d _ i _
      exact hx ⟨d, i⟩ (Set.mem_univ _)
    · intro hx t _
      exact hx t.1 (Set.mem_univ _) t.2 (Set.mem_univ _)
  rw [he, volume_pi_pi]
  simp only [volume_pi_pi, Fintype.prod_sigma]

theorem sigmaAxisCoordinates_measurePreserving :
    MeasurePreserving (sigmaAxisCoordinates I) volume volume :=
  (sigmaAxisCoordinates_symm_measurePreserving I).symm
    (sigmaAxisCoordinates I).symm.toHomeomorph.toMeasurableEquiv

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

theorem pivotDensityPullback_measurable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Measurable f) : Measurable (pivotDensityPullback A B f) :=
  measurable_const.mul (hf.comp (pivotCoordinateChange A B).symm.continuous.measurable)

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

theorem pivotOutputDensity_measurable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Measurable f) : Measurable (pivotOutputDensity A B f) :=
  (pivotDensityPullback_measurable A B hf).stronglyMeasurable.integral_prod_left'.measurable

omit [Fintype I] in
theorem pivotOutputDensity_nonneg (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : ∀ p, 0 ≤ f p) (v : I → ℝ) : 0 ≤ pivotOutputDensity A B f v :=
  integral_nonneg fun _ => mul_nonneg (inverseJacobian_pos A).le (hf _)

theorem pivotOutputDensity_integrable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Integrable f) : Integrable (pivotOutputDensity A B f) :=
  (pivotDensityPullback_integrable A B hf).integral_prod_right

theorem pivotOutputDensity_integral (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Integrable f) : (∫ v, pivotOutputDensity A B f v) = ∫ p, f p := by
  unfold pivotOutputDensity
  rw [← integral_prod_symm _ (pivotDensityPullback_integrable A B hf)]
  exact pivotDensityPullback_integral A B f

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

theorem splitInputProfile_integral (f : (J → ℝ) × (I → ℝ) → ℝ) :
    (∫ x, splitInputProfile f x) = ∫ p, f p :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)).integral_comp
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)).measurableEmbedding f

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem tensorCutoffWeight_tsupport {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, TopologicalSpace (E i)]
    (w : ∀ i, E i → ℝ) :
    tsupport (tensorCutoffWeight w) ⊆ {x | ∀ i, x i ∈ tsupport (w i)} := by
  have hc : IsClosed {x : ∀ i, E i | ∀ i, x i ∈ tsupport (w i)} := by
    have he : {x : ∀ i, E i | ∀ i, x i ∈ tsupport (w i)} =
        ⋂ i, (fun x : ∀ i, E i => x i) ⁻¹' tsupport (w i) := by ext; simp
    rw [he]
    exact isClosed_iInter (fun i => (isClosed_tsupport _).preimage (continuous_apply i))
  apply closure_minimal _ hc
  intro x hx i
  apply subset_closure
  change w i (x i) ≠ 0
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

theorem tensorCutoffWeight_compact {ι : Type*} {E : ι → Type*} [Fintype ι] [∀ i, TopologicalSpace (E i)]
    (w : ∀ i, E i → ℝ) (hw : ∀ i, HasCompactSupport (w i)) :
    HasCompactSupport (tensorCutoffWeight w) :=
  (isCompact_pi_infinite hw).of_isClosed_subset (isClosed_tsupport _)
    (tensorCutoffWeight_tsupport w)

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

omit [∀ d, Fintype (I d)] in
theorem sigmaAxisWeight_nonneg (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d y, 0 ≤ w d y) (x : (Σ d, I d) → ℝ) : 0 ≤ sigmaAxisWeight w x :=
  tensorCutoffWeight_nonneg w hw _

theorem sigmaAxisWeight_integral (w : ∀ d, (I d → ℝ) → ℝ) :
    (∫ x, sigmaAxisWeight w x) = ∏ d, ∫ y, w d y := by
  calc
    _ = ∫ x, tensorCutoffWeight w x :=
      (sigmaAxisCoordinates_measurePreserving I).integral_comp
        (sigmaAxisCoordinates I).toHomeomorph.toMeasurableEquiv.measurableEmbedding _
    _ = _ := tensorCutoffWeight_integral w

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MonomialArrayJet
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem realJetMatrix_monomialArray {α K O J : Type*} [DecidableEq α] [Fintype J]
    (e : J → K →₀ ℕ) (vertices : Finset α → K → ℝ) (rows : O → Finset α)
    (a : J → ℝ) (o : O) :
    (realJetMatrix (fun j => MvPolynomial.monomial (e j) 1) vertices rows *ᵥ a) o =
      booleanCoefficient (fun t => MvPolynomial.eval (vertices t) (monomialArrayPolynomial e a)) (rows o) := by
  rw [realJetMatrix_apply_coefficients]
  simp only [MvPolynomial.C_mul_monomial, mul_one, monomialArrayPolynomial]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SigmaProductMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem sigmaProductMeasure_flatten {D : Type*} [Fintype D] {I : D → Type*}
    [∀ d, Fintype (I d)] {X : (Σ d, I d) → Type*}
    [∀ s, MeasurableSpace (X s)] (μ : ∀ s, Measure (X s)) [∀ s, IsProbabilityMeasure (μ s)] :
    (Measure.pi (fun d => Measure.pi (fun i => μ ⟨d, i⟩))).map
      (fun x (s : Σ d, I d) => x s.1 s.2) = Measure.pi μ := by
  have hm : Measurable (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) :=
    measurable_pi_iff.mpr (fun index =>
      (measurable_pi_apply index.2).comp (measurable_pi_apply index.1))
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun d => Set.univ.pi (fun i => s ⟨d, i⟩)) := by
    ext x
    constructor
    · intro hx d _ i _
      exact hx ⟨d, i⟩ (Set.mem_univ _)
    · intro hx t _
      exact hx t.1 (Set.mem_univ _) t.2 (Set.mem_univ _)
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_sigma]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {T G : Type*} [MeasurableSpace T] [AddCommGroup G]
  [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

omit [∀ d, Fintype (O d)] in
theorem sigmaAxisSampler_measurable (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (hU : ∀ d, Measurable (U d)) : Measurable (sigmaAxisSampler U) :=
  measurable_pi_iff.mpr (fun s => (measurable_pi_apply s.2).comp
    ((hU s.1).comp (sigmaAxisProjection I s.1).continuous.measurable))

theorem sigmaAxisSampler_image_law (μ : ∀ d, Measure (I d → ℝ))
    [∀ d, IsProbabilityMeasure (μ d)]
    (U : ∀ d, (I d → ℝ) → (O d → ℝ)) (hU : ∀ d, Measurable (U d)) :
    Measure.map (sigmaAxisSampler U) (sigmaAxisMeasure μ) =
      sigmaAxisMeasure (fun d => Measure.map (U d) (μ d)) := by
  let : ∀ d, IsProbabilityMeasure (Measure.map (U d) (μ d)) :=
    fun d => Measure.isProbabilityMeasure_map (hU d).aemeasurable
  rw [sigmaAxisMeasure, Measure.map_map (sigmaAxisSampler_measurable U hU)
    (sigmaAxisCoordinates I).symm.continuous.measurable]
  have he : sigmaAxisSampler U ∘ (sigmaAxisCoordinates I).symm =
      (sigmaAxisCoordinates O).symm ∘ (fun x d => U d (x d)) := rfl
  have hPi : Measurable (fun x : ∀ d, I d → ℝ => fun d => U d (x d)) :=
    measurable_pi_iff.mpr (fun d => (hU d).comp (measurable_pi_apply d))
  rw [he, ← Measure.map_map (sigmaAxisCoordinates O).symm.continuous.measurable
    hPi]
  rw [Measure.pi_map_pi (fun d => (hU d).aemeasurable)]
  rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

theorem sigmaAxisMeasure_withDensity (μ : ∀ d, Measure (I d → ℝ)) [∀ d, SigmaFinite (μ d)]
    (f : ∀ d, (I d → ℝ) → ℝ) (hf : ∀ d, Integrable (f d) (μ d)) (hf0 : ∀ d x, 0 ≤ f d x) :
    sigmaAxisMeasure (fun d => realDensityMeasure (μ d) (f d)) =
      realDensityMeasure (sigmaAxisMeasure μ) (sigmaAxisWeight f) := by
  unfold sigmaAxisMeasure
  rw [realDensityMeasure_pi μ f hf hf0]
  exact realDensityMeasure_map_equiv
    (sigmaAxisCoordinates I).symm.toHomeomorph.toMeasurableEquiv _ _

theorem sigmaAxisMeasure_volume :
    sigmaAxisMeasure (fun d => (volume : Measure (I d → ℝ))) = volume :=
  (sigmaAxisCoordinates_symm_measurePreserving I).map_eq

theorem sigmaAxisMeasure_density (f : ∀ d, (I d → ℝ) → ℝ)
    (hf : ∀ d, Integrable (f d)) (hf0 : ∀ d x, 0 ≤ f d x) :
    sigmaAxisMeasure (fun d => realDensityMeasure volume (f d)) =
      realDensityMeasure volume (sigmaAxisWeight f) := by
  rw [sigmaAxisMeasure_withDensity _ f hf hf0, sigmaAxisMeasure_volume]

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

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

end Erdos3

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

end Erdos3.SlicedProductBlock

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B ι : Type*} [Fintype B] [Fintype ι] [DecidableEq B] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {J ι : Type*} [Fintype J] [Fintype ι] [DecidableEq J] [DecidableEq ι]

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem selectedCoefficientProfile_nonneg {I J : Type*} [Fintype I]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∀ p, 0 ≤ selectedCoefficientProfile s f p := fun p => hf (selectedCoefficientEquiv s ℝ p)

theorem selectedCoefficientProfile_zero_outside {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} {R : ℝ}
    (hf : ∀ x, R < ‖x‖ → f x = 0) :
    ∀ p, R < ‖p‖ → selectedCoefficientProfile s f p = 0 := by
  intro p hp
  exact hf _ (by rwa [selectedCoefficientEquiv_norm])

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

section

namespace Erdos3

variable {I J R : Type*} [Fintype I] (s : I ↪ J)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedJetColumns
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem frozenTupleCoordinate_eval {Z P : Type*} (z : Z → ℝ) (x : P → ℝ) (i : Z ⊕ P) :
    MvPolynomial.eval x (frozenTupleCoordinate z i) = Sum.elim z x i := by
  cases i <;> simp [frozenTupleCoordinate]

theorem normalizedJetColumns_apply_coefficients {Z P K α O J : Type*}
    [Fintype α] [DecidableEq α] [Fintype O] [Fintype J]
    (e : J → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (rows : O → Finset α)
    (x : P → ℝ) (c : J → ℝ) (o : O) :
    polynomialColumns (fun o j => normalizedJetColumn (e j) input z (rows o)) x c o =
      booleanCoefficient (fun t => ∑ j, c j * ∏ k ∈ (e j).support,
        (normalizedCubeTuple input z x t k)^e j k) (rows o) := by
  simpa only [normalizedJetColumn, frozenTupleCoordinate_eval, normalizedCubeTuple] using
    booleanJetColumns_apply_coefficients e (fun k r => frozenTupleCoordinate z (input k r)) rows x c o

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

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

namespace Erdos3

open MeasureTheory

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerNormalizedJetColumns
namespace OAI

namespace Erdos3

open scoped BigOperators

theorem real_monomial_eval_div_scale {K : Type*} (e : K →₀ ℕ) (x T : K → ℝ) :
    MvPolynomial.eval (fun k => x k / T k) (MvPolynomial.monomial e (1 : ℝ)) =
      MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℝ)) / monomialScale T e := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, monomialScale, Finsupp.prod,
    div_pow, Finset.prod_div_distrib]

theorem integer_monomial_eval_cast {K : Type*} (e : K →₀ ℕ) (x : K → ℤ) :
    (MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℤ)) : ℝ) =
      MvPolynomial.eval (fun k => (x k : ℝ)) (MvPolynomial.monomial e (1 : ℝ)) := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, Int.cast_prod, Int.cast_pow]

theorem normalizedIntegerMonomialJetMatrix_eq {α K O J : Type*} [DecidableEq α]
    [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    (e : J → K →₀ ℕ) (vertices : Finset α → K → ℤ) (rows : O → Finset α)
    (T : K → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns
      (integerJetMatrix (fun j => MvPolynomial.monomial (e j) 1) vertices rows)
      (fun j => H / monomialScale T (e j)) (fun _ => H) =
    realJetMatrix (fun j => MvPolynomial.monomial (e j) 1)
      (fun t k => (vertices t k : ℝ) / T k) rows := by
  ext o j
  rw [normalizedIntegerColumns_entry_div]
  change ((booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
    (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o) : ℤ) : ℝ) *
      (H / monomialScale T (e j)) / H =
    booleanCoefficient (fun t => MvPolynomial.eval (fun k => (vertices t k : ℝ) / T k)
      (MvPolynomial.monomial (e j) (1 : ℝ))) (rows o)
  have hcast := booleanCoefficient_map (Int.castRingHom ℝ)
    (fun t => MvPolynomial.eval (vertices t) (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o)
  change ((booleanCoefficient _ (rows o) : ℤ) : ℝ) =
    booleanCoefficient (fun t => (MvPolynomial.eval (vertices t)
      (MvPolynomial.monomial (e j) (1 : ℤ)) : ℝ)) (rows o) at hcast
  rw [hcast]
  simp only [real_monomial_eval_div_scale, integer_monomial_eval_cast]
  rw [booleanCoefficient_div]
  simp [div_eq_mul_inv, hH, mul_assoc, mul_comm]

theorem realAffineCube_normalized_integer {α K : Type*}
    (root : K → ℤ) (difference : α → K → ℤ) (T : K → ℝ) (t : Finset α) (k : K) :
    realAffineCube (fun k => (root k : ℝ) / T k)
      (fun r k => (difference r k : ℝ) / T k) t k =
        (integerAffineCube root difference t k : ℝ) / T k := by
  simp only [realAffineCube, integerAffineCube, Int.cast_add, Int.cast_sum,
    add_div, Finset.sum_div]

theorem normalizedBoundedIntegerJetMatrix_eq {α K O : Type*}
    [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (difference : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α)
    (T : K → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (boundedDegreeIntegerJetMatrix root difference h rows)
      (fun e => H / monomialScale T e.val) (fun _ => H) =
    boundedDegreeRealJetMatrix (fun k => (root k : ℝ) / T k)
      (fun r k => (difference r k : ℝ) / T k) h rows := by
  have hv : (fun t k => (integerAffineCube root difference t k : ℝ) / T k) =
      realAffineCube (fun k => (root k : ℝ) / T k)
        (fun r k => (difference r k : ℝ) / T k) := by
    funext t k
    exact (realAffineCube_normalized_integer root difference T t k).symm
  have he := normalizedIntegerMonomialJetMatrix_eq
    (fun e : BoundedIntegerExponent K h => e.val) (integerAffineCube root difference) rows T hH
  rw [hv] at he
  exact he

end Erdos3

namespace Erdos3

open scoped BigOperators Matrix

theorem normalizedJetColumns_eq_realJetMatrix {Z P K α I N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype N]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ)
    (rows : I → Finset α) (x : P → ℝ) :
    polynomialColumns (fun i n => normalizedJetColumn (e n) input z (rows i)) x =
      matrixSupCLM (realJetMatrix (fun n => MvPolynomial.monomial (e n) 1)
        (normalizedCubeTuple input z x) rows) := by
  unfold polynomialColumns
  congr 1
  funext i n
  simp only [normalizedJetColumn, booleanJetColumnPolynomial_eval, frozenTupleCoordinate_eval,
    realJetMatrix, MvPolynomial.eval_monomial, one_mul, Finsupp.prod, normalizedCubeTuple]

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

theorem normalizedScalarKernelJet_eq {I J O : Type*}
    [DecidableEq I] [Fintype J] [Fintype O] [DecidableEq O] {L : ℕ}
    (x : J → IntegerScalarCubeBox I L) (h : ℕ) (rows : O → Finset I)
    {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (scalarKernelIntegerJet x h rows)
      (fun e => H / monomialScale (fun _ => (L : ℝ)) e.val) (fun _ => H) =
      normalizedScalarKernelJet x h rows :=
  normalizedBoundedIntegerJetMatrix_eq _ _ _ _ _ hH

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

theorem affineProductProfile_compact {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : HasCompactSupport (affineProductProfile c w) :=
  tensorCutoffWeight_compact (fun i => affineProbabilityProfile (c i) (w i))
    (fun i => affineProbabilityProfile_compact (c i) (hw i))

theorem affineProductProfile_integrable {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : Integrable (affineProductProfile c w) :=
  (affineProductProfile_contDiff c w).continuous.integrable_of_hasCompactSupport
    (affineProductProfile_compact c w hw)

theorem affineProductProfile_integral {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : (∫ x, affineProductProfile c w x) = 1 := by
  change (∫ x, tensorCutoffWeight (fun i => affineProbabilityProfile (c i) (w i)) x) = 1
  rw [tensorCutoffWeight_integral]
  simp only [affineProbabilityProfile_integral _ (hw _), Finset.prod_const_one]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem affineProbabilityProfile_integral_test (c : ℝ) {w : ℝ} (hw : 0 < w) (φ : ℝ → ℝ) :
    (∫ x, affineProbabilityProfile c w x * φ x) =
      ∫ y, smoothProbabilityProfile y * φ (c + w*y) := by
  let g := fun y => smoothProbabilityProfile y * φ (c+w*y)
  have he (x : ℝ) : affineProbabilityProfile c w x * φ x = w⁻¹ * g ((x-c)/w) := by
    have hx : c + w*((x-c)/w) = x := by field_simp [hw.ne']; ring
    simp only [affineProbabilityProfile, g, hx]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_sub_right_eq_self (fun x => g (x/w)) c,
    Measure.integral_comp_div, smul_eq_mul, abs_of_pos hw, ← mul_assoc,
    inv_mul_cancel₀ hw.ne', one_mul]

theorem affineProbabilityProfile_law (c : ℝ) {w : ℝ} (hw : 0 < w) :
    (realDensityMeasure volume smoothProbabilityProfile).map (fun y => c + w*y) =
      realDensityMeasure volume (affineProbabilityProfile c w) := by
  have hψ : Integrable smoothProbabilityProfile :=
    smoothProbabilityProfile_contDiff.continuous.integrable_of_hasCompactSupport smoothProbabilityProfile_compact
  let : IsFiniteMeasure (realDensityMeasure volume smoothProbabilityProfile) :=
    realDensityMeasure_finite _ _ hψ (fun y => (smoothProbabilityProfile_range y).1)
  let : IsFiniteMeasure (realDensityMeasure volume (affineProbabilityProfile c w)) :=
    realDensityMeasure_finite _ _ (affineProbabilityProfile_integrable c hw) (affineProbabilityProfile_nonneg c hw)
  have hmap : Measurable (fun y : ℝ => c+w*y) := by fun_prop
  apply finiteMeasure_eq_of_integrals
  intro φ hφ
  rw [integral_map hmap.aemeasurable hφ.aestronglyMeasurable,
    realDensityMeasure_integral volume smoothProbabilityProfile
      smoothProbabilityProfile_contDiff.continuous.measurable (fun y => (smoothProbabilityProfile_range y).1),
    realDensityMeasure_integral volume (affineProbabilityProfile c w)
      (affineProbabilityProfile_contDiff c w).continuous.measurable (affineProbabilityProfile_nonneg c hw)]
  exact (affineProbabilityProfile_integral_test c hw φ).symm

theorem affineProductProfile_law {I : Type*} [Fintype I]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) :
    (realDensityMeasure volume (smoothProductProfile I)).map (fun y i => c i + w i * y i) =
      realDensityMeasure volume (affineProductProfile c w) := by
  have hψ : Integrable smoothProbabilityProfile :=
    smoothProbabilityProfile_contDiff.continuous.integrable_of_hasCompactSupport smoothProbabilityProfile_compact
  let : IsFiniteMeasure (realDensityMeasure volume smoothProbabilityProfile) :=
    realDensityMeasure_finite _ _ hψ (fun y => (smoothProbabilityProfile_range y).1)
  have hsrc := realDensityMeasure_pi (fun _ : I => (volume : Measure ℝ))
    (fun _ => smoothProbabilityProfile) (fun _ => hψ) (fun _ y => (smoothProbabilityProfile_range y).1)
  have hdst := realDensityMeasure_pi (fun _ : I => (volume : Measure ℝ))
    (fun i => affineProbabilityProfile (c i) (w i))
    (fun i => affineProbabilityProfile_integrable (c i) (hw i))
    (fun i => affineProbabilityProfile_nonneg (c i) (hw i))
  change (Measure.pi (fun _ : I => realDensityMeasure volume smoothProbabilityProfile)) =
    realDensityMeasure volume (smoothProductProfile I) at hsrc
  change (Measure.pi (fun i : I => realDensityMeasure volume (affineProbabilityProfile (c i) (w i)))) =
    realDensityMeasure volume (affineProductProfile c w) at hdst
  rw [← hsrc, Measure.pi_map_pi (fun i =>
    (show Measurable (fun y : ℝ => c i + w i * y) by fun_prop).aemeasurable)]
  simp_rw [affineProbabilityProfile_law _ (hw _)]
  exact hdst

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
open scoped Matrix

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedJetMeasurability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem normalizedCubeTuple_measurable_comp {Ω Z P K α : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] (input : K → Option α → Z ⊕ P)
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun ω => z ω j))
    (x : Ω → P → ℝ) (hx : ∀ j, Measurable (fun ω => x ω j)) (t : Finset α) (k : K) :
    Measurable (fun ω => normalizedCubeTuple input (z ω) (x ω) t k) := by
  have hs (i : Z ⊕ P) : Measurable (fun ω => Sum.elim (z ω) (x ω) i) := by
    cases i with
    | inl j => exact hz j
    | inr j => exact hx j
  unfold normalizedCubeTuple
  fun_prop

theorem normalizedJetColumns_measurable_comp {Ω Z P K α I N : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype N]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (rows : I → Finset α)
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun ω => z ω j))
    (x : Ω → P → ℝ) (hx : ∀ j, Measurable (fun ω => x ω j))
    (c : Ω → N → ℝ) (hc : ∀ j, Measurable (fun ω => c ω j)) :
    Measurable (fun ω => polynomialColumns (fun o n => normalizedJetColumn (e n) input (z ω) (rows o)) (x ω) (c ω)) := by
  apply measurable_pi_iff.mpr
  intro o
  simp_rw [normalizedJetColumns_apply_coefficients, booleanCoefficient]
  have ht (t : Finset α) (k : K) := normalizedCubeTuple_measurable_comp input z hz x hx t k
  fun_prop

theorem normalizedJetDensity_measurable_comp {Ω Z P K α I J N : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (rows : I → Finset α)
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    {R S : ℝ} (hfs : ∀ u, R < ‖u‖ → f u = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun ω => z ω j))
    (x : Ω → P → ℝ) (hx : ∀ j, Measurable (fun ω => x ω j))
    (v : Ω → I → ℝ) (hv : ∀ i, Measurable (fun ω => v ω i)) :
    Measurable (fun ω => normalizedJetDensity A F e input (z ω) rows f g (x ω) (v ω)) := by
  have he : (fun ω => normalizedJetDensity A F e input (z ω) rows f g (x ω) (v ω)) =
      (fun ω => ∫ n, g n * pivotOutputDensity A F f (v ω -
        polynomialColumns (fun o n => normalizedJetColumn (e n) input (z ω) (rows o)) (x ω) n)) :=
    funext (fun ω => splitPivotDensity_formula A F _ hf hg hfs hgs (v ω))
  rw [he]
  have hcols := normalizedJetColumns_measurable_comp (Ω := Ω × (N → ℝ)) e input rows
    (fun q => z q.1) (fun j => (hz j).comp measurable_fst)
    (fun q => x q.1) (fun j => (hx j).comp measurable_fst)
    (fun q => q.2) (fun j => (measurable_pi_apply j).comp measurable_snd)
  have hv' : Measurable v := measurable_pi_iff.mpr hv
  have htest := (hg.measurable.comp measurable_snd).mul
    ((pivotOutputDensity_measurable A F hf.measurable).comp ((hv'.comp measurable_fst).sub hcols))
  exact htest.stronglyMeasurable.integral_prod_right'.measurable

theorem normalizedJetDensity_measurable {Z P K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (rows : I → Finset α)
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    {R S : ℝ} (hfs : ∀ u, R < ‖u‖ → f u = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0) :
    Measurable (Function.uncurry (normalizedJetDensity A F e input z rows f g)) := by
  change Measurable (fun q : (P → ℝ) × (I → ℝ) => normalizedJetDensity A F e input z rows f g q.1 q.2)
  exact normalizedJetDensity_measurable_comp (Ω := (P → ℝ) × (I → ℝ))
    A F e input rows hf hg hfs hgs
    (fun _ => z) (fun _ => measurable_const) (fun q => q.1)
    (fun i => (measurable_pi_apply i).comp measurable_fst) (fun q => q.2)
    (fun i => (measurable_pi_apply i).comp measurable_snd)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitCoefficientSourceMarginal
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

theorem unitCoefficientSource_pi (I : Type*) [Fintype I] :
    unitCoefficientSource I = Measure.pi (fun _ : I => realDensityMeasure volume smoothProbabilityProfile) := by
  symm
  exact realDensityMeasure_pi (fun _ => volume) (fun _ => smoothProbabilityProfile)
    (fun _ => smoothProbabilityProfile_contDiff.continuous.integrable_of_hasCompactSupport
      smoothProbabilityProfile_compact) (fun _ r => (smoothProbabilityProfile_range r).1)

theorem unitCoefficientSource_reindex {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J) :
    (unitCoefficientSource I).map (fun r => r ∘ e.symm) = unitCoefficientSource J := by
  let : IsProbabilityMeasure (realDensityMeasure volume smoothProbabilityProfile) :=
    realDensityMeasure_probability volume _
      (smoothProbabilityProfile_contDiff.continuous.integrable_of_hasCompactSupport
        smoothProbabilityProfile_compact)
      (fun r => (smoothProbabilityProfile_range r).1) smoothProbabilityProfile_integral
  rw [unitCoefficientSource_pi, unitCoefficientSource_pi]
  have he : (MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e : (I → ℝ) → J → ℝ) =
      fun r => r ∘ e.symm := by
    funext r j
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [← he]
  exact Measure.pi_map_piCongrLeft e (fun _ => realDensityMeasure volume smoothProbabilityProfile)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory ProbabilityTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RegularizedSigmaDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

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
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem unitCoefficientSource_sigma {D : Type*} [Fintype D]
    (I : D → Type*) [∀ d, Fintype (I d)] :
    unitCoefficientSource (Σ d, I d) = sigmaAxisMeasure (fun d => unitCoefficientSource (I d)) := by
  let : IsProbabilityMeasure (realDensityMeasure volume smoothProbabilityProfile) :=
    realDensityMeasure_probability volume _
      (smoothProbabilityProfile_contDiff.continuous.integrable_of_hasCompactSupport
        smoothProbabilityProfile_compact)
      (fun r => (smoothProbabilityProfile_range r).1) smoothProbabilityProfile_integral
  unfold sigmaAxisMeasure
  simp only [unitCoefficientSource_pi]
  exact (sigmaProductMeasure_flatten
    (fun _ : Σ d, I d => realDensityMeasure volume smoothProbabilityProfile)).symm

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientDensitySplit
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

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

theorem affineSelectedJetProfile_probability_data {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J) (c w : J ⊕ N → ℝ)
    (hw : ∀ j, 0 < w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R) :
    Integrable (affineSelectedJetProfile s c w) ∧
      (∀ u, 0 ≤ affineSelectedJetProfile s c w u) ∧
      (∫ u, affineSelectedJetProfile s c w u) = 1 := by
  have hf : Continuous (selectedCoefficientProfile s
      (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j)))) :=
    (affineProductProfile_contDiff (fun j => c (.inl j)) (fun j => w (.inl j))).continuous.comp
      (selectedCoefficientEquiv_lipschitz s).continuous
  have hg := (affineProductProfile_contDiff (fun n => c (.inr n)) (fun n => w (.inr n))).continuous
  have hfs := selectedCoefficientProfile_zero_outside s
    (affineProductProfile_zero_outside _ _ (fun j => hw (.inl j)) R.coe_nonneg (fun j => hsupport (.inl j)))
  have hgs := affineProductProfile_zero_outside _ _ (fun n => hw (.inr n)) R.coe_nonneg
    (fun n => hsupport (.inr n))
  refine ⟨splitFreeProfile_integrable hf hg hfs hgs,
    splitFreeProfile_nonneg (selectedCoefficientProfile_nonneg s
      (affineProductProfile_nonneg _ _ (fun j => hw (.inl j))))
      (affineProductProfile_nonneg _ _ (fun n => hw (.inr n))), ?_⟩
  change (∫ u, splitFreeProfile _ _ u) = 1
  rw [splitFreeProfile_integral hf hg hfs hgs, selectedCoefficientProfile_integral,
    affineProductProfile_integral _ _ (fun j => hw (.inl j)),
    affineProductProfile_integral _ _ (fun n => hw (.inr n)), one_mul]

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

theorem affineSelectedJetDensity_probability_data {Z P K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (rows : I → Finset α)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) (R : ℝ≥0) (hsupport : ∀ j, |c j| + w j ≤ R)
    (x : P → ℝ) :
    (∀ v, 0 ≤ affineSelectedJetDensity s A F e input z rows c w x v) ∧
      Integrable (affineSelectedJetDensity s A F e input z rows c w x) ∧
      (∫ v, affineSelectedJetDensity s A F e input z rows c w x v) = 1 := by
  have hp := affineSelectedJetProfile_probability_data s c w hw R hsupport
  exact ⟨pivotOutputDensity_nonneg _ _ hp.2.1, pivotOutputDensity_integrable _ _ hp.1,
    (pivotOutputDensity_integral _ _ hp.1).trans hp.2.2⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedSplitUnitSource
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem selectedSplitMeasurableEquiv_symm_apply {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J) (r : J ⊕ N → ℝ) :
    (selectedSplitMeasurableEquiv s).symm r =
      (Sum.elim (fun j : UnselectedColumn s => r (.inl j.val)) (fun n => r (.inr n)),
        fun i => r (.inl (s i))) := rfl

theorem measurableEquiv_inverse_law {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (ν : Measure Y) (he : μ.map e = ν) :
    ν.map e.symm = μ := by
  rw [← he, Measure.map_map e.symm.measurable e.measurable]
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply, Measure.map_id']

theorem affineProductProfile_map_law {I Y : Type*} [Fintype I] [MeasurableSpace Y]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (F : (I → ℝ) → Y) (hF : Measurable F) :
    (realDensityMeasure volume (smoothProductProfile I)).map
      (fun r => F (fun i => c i+w i*r i)) =
      (realDensityMeasure volume (affineProductProfile c w)).map F := by
  have hm : Measurable (fun r : I → ℝ => fun i => c i+w i*r i) := by fun_prop
  change Measure.map (F ∘ (fun (r : I → ℝ) i => c i+w i*r i)) _ = _
  rw [← Measure.map_map hF hm, affineProductProfile_law c w hw]

theorem selectedSplit_affine_law {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) :
    (realDensityMeasure volume (affineSelectedJetProfile s c w)).map
      (selectedSplitMeasurableEquiv s) = realDensityMeasure volume (affineProductProfile c w) := by
  have hf := selectedSplitCoefficients_law s
    (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j)))
    (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n)))
    (affineProductProfile_contDiff _ _).continuous.measurable
    (affineProductProfile_contDiff _ _).continuous.measurable
    (affineProductProfile_integrable _ _ (fun j => hw (.inl j)))
    (affineProductProfile_integrable _ _ (fun n => hw (.inr n)))
    (affineProductProfile_nonneg _ _ (fun j => hw (.inl j)))
    (affineProductProfile_nonneg _ _ (fun n => hw (.inr n)))
  change (realDensityMeasure volume (affineSelectedJetProfile s c w)).map
    (selectedSplitMeasurableEquiv s) = _ at hf
  rw [← affineProductProfile_joined] at hf
  exact hf

theorem selectedSplit_unit_law {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N] (s : I ↪ J)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) :
    (realDensityMeasure volume (smoothProductProfile (J ⊕ N))).map
      (fun r => (selectedSplitMeasurableEquiv s).symm (fun j => c j+w j*r j)) =
      realDensityMeasure volume (affineSelectedJetProfile s c w) := by
  exact (affineProductProfile_map_law c w hw _ (selectedSplitMeasurableEquiv s).symm.measurable).trans
    (measurableEquiv_inverse_law (selectedSplitMeasurableEquiv s) _ _ (selectedSplit_affine_law s c w hw))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineUnitSource
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem affineJetUnitMap_measurable_comp {Ω Z X K α I J N : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (rows : I → Finset α)
    (c w r : Ω → J ⊕ N → ℝ) (hc : Measurable c) (hw : Measurable w) (hr : Measurable r)
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (x : Ω → X → ℝ) (hx : ∀ j, Measurable (fun a => x a j)) :
    Measurable (fun a => affineJetUnitMap s A F e input (z a) rows (c a) (w a) (x a) (r a)) := by
  have htail := normalizedJetColumns_measurable_comp e input rows z hz x hx
    (fun a n => c a (.inr n)+w a (.inr n)*r a (.inr n)) (fun _ => by fun_prop)
  have hker : Measurable (fun a =>
      A (fun i => c a (.inl (s i))+w a (.inl (s i))*r a (.inl (s i))) +
        F (fun j => c a (.inl j.val)+w a (.inl j.val)*r a (.inl j.val))) := by fun_prop
  exact hker.add htail

theorem affineSelectedJetDensity_unit_law {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : I → Finset α) (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j)
    (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R) (x : X → ℝ) :
    (realDensityMeasure volume (smoothProductProfile (J ⊕ N))).map
      (affineJetUnitMap s A F e input z rows c w x) =
      realDensityMeasure volume (affineSelectedJetDensity s A F e input z rows c w x) := by
  let C := polynomialColumns (fun o n => normalizedJetColumn (e n) input z (rows o)) x
  let H := fun p : (UnselectedColumn s ⊕ N → ℝ) × (I → ℝ) => A p.2+splitFreeColumns F C p.1
  have hH : Measurable H := by fun_prop
  have he : affineJetUnitMap s A F e input z rows c w x =
      H ∘ (fun r => (selectedSplitMeasurableEquiv s).symm (fun j => c j+w j*r j)) := by
    funext r
    simp only [Function.comp_def, selectedSplitMeasurableEquiv_symm_apply,
      H, splitFreeColumns_apply, affineJetUnitMap, add_assoc, C, Sum.elim_inl, Sum.elim_inr]
  have hinput : Measurable (fun r : J ⊕ N → ℝ =>
      (selectedSplitMeasurableEquiv s).symm (fun j => c j+w j*r j)) :=
    (selectedSplitMeasurableEquiv s).symm.measurable.comp (by fun_prop)
  rw [he, ← Measure.map_map hH hinput, selectedSplit_unit_law s c w hw]
  have hp := affineSelectedJetProfile_probability_data s c w hw R hsupport
  exact pivotOutputDensity_law A (splitFreeColumns F C) hp.1 hp.2.1

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem normalizedIntegerColumns_eq_of_instances {I J : Type*}
    [Fintype I] [instI : DecidableEq I] [Fintype J] [instJ : DecidableEq J]
    {dI : DecidableEq I} {dJ : DecidableEq J}
    {M : Matrix I J ℤ} {T : J → ℝ} {P : I → ℝ} {A : Matrix I J ℝ}
    (h : @normalizedIntegerColumns I J ‹Fintype I› dI ‹Fintype J› dJ M T P = A) :
    @normalizedIntegerColumns I J ‹Fintype I› instI ‹Fintype J› instJ M T P = A := by
  have hi : dI = instI := Subsingleton.elim _ _
  have hj : dJ = instJ := Subsingleton.elim _ _
  cases hi
  cases hj
  exact h

theorem kernelExponent_eval_real {G X : Type*} {h : ℕ} (x : G ⊕ X → ℝ)
    (d : BoundedIntegerExponent G h) :
    MvPolynomial.eval x (MvPolynomial.monomial (kernelExponentEmbedding G X h d).val 1) =
      MvPolynomial.eval (fun g => x (.inl g)) (MvPolynomial.monomial d.val 1) := by
  change MvPolynomial.eval x (MvPolynomial.monomial (d.val.embDomain Function.Embedding.inl) 1) = _
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_embDomain]
  rfl

theorem normalizedMappedKernelJet_eq {G X Z Y α O : Type*}
    [Fintype G] [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
    (h : ℕ) (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℝ) (y : Y → ℝ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℝ) / L)
    (rows : O → Finset α) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (scalarKernelIntegerJet x h rows)
        (kernelJetCoefficientScale G h L H) (fun _ => H) =
      realJetMatrix (fun d => MvPolynomial.monomial (kernelExponentEmbedding G X h d).val 1)
        (normalizedCubeTuple input z y) rows := by
  have hc (t : Finset α) : (fun g => normalizedCubeTuple input z y t (.inl g)) =
      realAffineCube (fun g => (x g none : ℝ) / L)
        (fun a g => (x g (some a) : ℝ) / L) t := by
    funext g
    simp only [normalizedCubeTuple, hfixed, Fintype.sum_option, booleanFeature,
      one_mul, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, realAffineCube]
  apply (normalizedScalarKernelJet_eq x h rows hH).trans
  funext o d
  change booleanCoefficient (fun t => MvPolynomial.eval
      (realAffineCube (fun g => (x g none : ℝ) / L) (fun a g => (x g (some a) : ℝ) / L) t)
      (MvPolynomial.monomial d.val 1)) (rows o) = _
  apply congrArg (fun f : Finset α → ℝ => booleanCoefficient f (rows o))
  funext t
  rw [kernelExponent_eval_real, hc]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "scales" => allocatedIntegerProfileScales B U basis S j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

include hR hσ hσ1 in
theorem allocatedKernelProfile_bound (d) : |centers d|+widths d ≤ R j :=
  (allocatedProfile_term_bound (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (layerIntegerPrincipalSlots_not_constant B j i) (hR j) (hσ j) hσ1 d).trans (by linarith [hR j])

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

include hR hσ in
theorem allocatedContinuousProfileWidths_pos (j : Fin m) (i : I j) (d) :
    0 < allocatedContinuousProfileWidths (G := G) B R σ j i d :=
  coefficientProfileWidth_pos _ _ (div_pos (hR j) (by norm_num))
    (principalProfileSize_pos (hR j) _) (tailProfileSize_pos (hR j) (hσ j) _) d

include hR hσ in
theorem allocatedContinuousProfile_bound (j : Fin m) (i : I j) (hσ1 : σ j ≤ 1) (d) :
    |allocatedContinuousProfileCenters (G := G) B R j i d| +
      allocatedContinuousProfileWidths B R σ j i d ≤ R j :=
  (allocatedProfile_term_bound (layerContinuousPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (layerContinuousPrincipalSlots_not_constant B j i) (hR j) (hσ j) hσ1 d).trans (by linarith [hR j])

variable (j : Fin m) (i : I j)

local notation "centers" => allocatedContinuousProfileCenters (G := G) B R j i
local notation "widths" => allocatedContinuousProfileWidths (G := G) B R σ j i
local notation "scales" => allocatedContinuousProfileScales B U basis S j
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators Matrix Classical

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : I j)

local notation "unitWidth" => allocatedUnitProfileWidth (R j) (σ j)
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))

local notation "centers" => allocatedContinuousProfileCenters (G := G) B R j i
local notation "widths" => allocatedContinuousProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => kernelScale (s o)) (fun _ => 1)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1)
    (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) zero_lt_one (s o))
  (fun _ => zero_lt_one)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => kernelScale (Subtype.val d)) (fun _ => 1))
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))

include hR hσ in
theorem allocatedContinuousKernelDensity_measurable (hσ1 : σ j ≤ 1) :
    Measurable (Function.uncurry (allocatedContinuousKernelDensity B U basis S j i x u rows s hA)) := by
  have hw (d) := allocatedContinuousProfileWidths_pos B hR hσ j i (reindex d)
  have hb (d) := allocatedContinuousProfile_bound B hR hσ j i hσ1 (reindex d)
  exact normalizedJetDensity_measurable pivot free (allocatedNonkernelExponent B j) input fixedReal rows
    ((affineProductProfile_contDiff _ _).continuous.comp (selectedCoefficientEquiv_lipschitz s).continuous)
    (affineProductProfile_contDiff _ _).continuous
    (selectedCoefficientProfile_zero_outside s
      (affineProductProfile_zero_outside _ _ (fun d => hw (.inl d)) (hR j).le (fun d => hb (.inl d))))
    (affineProductProfile_zero_outside _ _ (fun d => hw (.inr d)) (hR j).le (fun d => hb (.inr d)))

include hR hσ in
theorem allocatedContinuousKernelDensity_probability_data (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (∀ v, 0 ≤ allocatedContinuousKernelDensity B U basis S j i x u rows s hA y v) ∧
      Integrable (allocatedContinuousKernelDensity B U basis S j i x u rows s hA y) ∧
      (∫ v, allocatedContinuousKernelDensity B U basis S j i x u rows s hA y v) = 1 :=
  affineSelectedJetDensity_probability_data s pivot free (allocatedNonkernelExponent B j) input fixedReal rows
    (centers ∘ reindex) (widths ∘ reindex)
    (fun d => allocatedContinuousProfileWidths_pos B hR hσ j i (reindex d)) radius
    (fun d => allocatedContinuousProfile_bound B hR hσ j i hσ1 (reindex d)) y

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedIntegerKernelComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "scales" => allocatedIntegerProfileScales B U basis S j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))

local notation "unitWidth" => allocatedUnitProfileWidth (R j) (σ j)
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "height" => (basisAxisScale (basis j) i : ℝ)
local notation "heightPos" => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) height
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => kernelScale (s o)) (fun _ => height)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1)
    (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) heightPos (s o))
  (fun _ => heightPos)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => kernelScale (Subtype.val d)) (fun _ => height))
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))

include hR hσ in
theorem allocatedIntegerKernelDensity_measurable (hσ1 : σ j ≤ 1) :
    Measurable (Function.uncurry (allocatedIntegerKernelDensity B U basis S j i x u rows s hA)) := by
  have hw (d) := allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)
  have hb (d) := allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d)
  exact normalizedJetDensity_measurable pivot free (allocatedNonkernelExponent B j) input fixedReal rows
    ((affineProductProfile_contDiff _ _).continuous.comp (selectedCoefficientEquiv_lipschitz s).continuous)
    (affineProductProfile_contDiff _ _).continuous
    (selectedCoefficientProfile_zero_outside s
      (affineProductProfile_zero_outside _ _ (fun d => hw (.inl d)) (hR j).le (fun d => hb (.inl d))))
    (affineProductProfile_zero_outside _ _ (fun d => hw (.inr d)) (hR j).le (fun d => hb (.inr d)))

include hR hσ in
theorem allocatedIntegerKernelDensity_probability_data (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (∀ z, 0 ≤ allocatedIntegerKernelDensity B U basis S j i x u rows s hA y z) ∧
      Integrable (allocatedIntegerKernelDensity B U basis S j i x u rows s hA y) ∧
      (∫ z, allocatedIntegerKernelDensity B U basis S j i x u rows s hA y z) = 1 :=
  affineSelectedJetDensity_probability_data s pivot free (allocatedNonkernelExponent B j) input fixedReal rows
    (centers ∘ reindex) (widths ∘ reindex)
    (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)) radius
    (fun d => allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d)) y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

end Erdos3

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α) (j : Fin m)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

variable (i : Fin (n j)) (s : O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id s).det ≠ 0)
variable (hσ1 : σ j ≤ 1) (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "height" => (basisAxisScale (basis j) i : ℝ)
local notation "heightPos" => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) height
local notation "nonkernelScale" => fun d => height / monomialScale (layerSamplerBox B U basis S)
  (allocatedNonkernelExponent B j d)
local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j
local notation "unitWidth" => allocatedUnitProfileWidth (R j) (σ j)
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable [DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SelectedKernelReconstruction
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem selectedKernel_matrix_reconstruct {I J R : Type*} [Fintype I] [Fintype J] [CommRing R]
    (M : Matrix I J R) (s : I ↪ J) (a : J → R) :
    M *ᵥ a = M.submatrix id s *ᵥ (fun i => a (s i)) +
      remainingMatrixColumns M s *ᵥ (fun j => a j.val) := by
  have h := Matrix.submatrix_mulVec_equiv M (a ∘ selectedColumnEquiv s) id (selectedColumnEquiv s)
  rw [← selectedMatrix_fromCols, Matrix.fromCols_mulVec] at h
  have hl (i : I) : selectedColumnEquiv s (Sum.inl i) = s i := rfl
  have hr (j : UnselectedColumn s) : selectedColumnEquiv s (Sum.inr j) = j.val := rfl
  simpa only [Function.comp_def, Equiv.apply_symm_apply, id_eq, hl, hr] using h.symm

theorem normalizedKernel_reconstruct {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℤ) (s : I ↪ J) (hM : (M.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i) (a : J → ℝ) :
    matrixSupCLM (normalizedIntegerColumns M S P) a =
      normalizedPivotEquiv (M.submatrix id s) hM (fun i => S (s i)) P (fun i => hS (s i)) hP
        (fun i => a (s i)) +
      matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns M s) (fun j => S j.val) P)
        (fun j => a j.val) := by
  change _ =
    (normalizedPivotEquiv (M.submatrix id s) hM (fun i => S (s i)) P (fun i => hS (s i)) hP).toContinuousLinearMap
      (fun i => a (s i)) + _
  rw [normalizedPivotEquiv_coe, normalized_remainingMatrixColumns]
  simpa only [matrixSupCLM_apply, normalizedIntegerColumns_submatrix] using
    selectedKernel_matrix_reconstruct (normalizedIntegerColumns M S P) s a

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RawAffinePolynomialJet
namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

theorem realJetMatrix_sumColumns {α K I J N : Type*} [DecidableEq α]
    (eK : J → K →₀ ℕ) (eN : N → K →₀ ℕ)
    (vertices : Finset α → K → ℝ) (rows : I → Finset α) :
    realJetMatrix (fun j => MvPolynomial.monomial (Sum.elim eK eN j) 1) vertices rows =
      Matrix.fromCols (realJetMatrix (fun j => MvPolynomial.monomial (eK j) 1) vertices rows)
        (realJetMatrix (fun n => MvPolynomial.monomial (eN n) 1) vertices rows) := by
  funext i j
  cases j <;> rfl

theorem affineJetUnitMap_monomial_jet {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype N]
    (M : Matrix I J ℤ) (s : I ↪ J) (hM : (M.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {H : ℝ} (hH : 0 < H)
    (eK : J → K →₀ ℕ) (eN : N → K →₀ ℕ)
    (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (rows : I → Finset α) (x : X → ℝ)
    (hkernel : normalizedIntegerColumns M S (fun _ => H) =
      realJetMatrix (fun j => MvPolynomial.monomial (eK j) 1) (normalizedCubeTuple input z x) rows)
    (c w r : J ⊕ N → ℝ) (i : I) :
    let E := normalizedPivotEquiv (M.submatrix id s) hM (fun j => S (s j)) (fun _ => H)
      (fun j => hS (s j)) (fun _ => hH)
    let F := matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns M s) (fun j => S j.val) (fun _ => H))
    affineJetUnitMap s E F eN input z rows c w x r i =
      booleanCoefficient (fun t => MvPolynomial.eval (normalizedCubeTuple input z x t)
        (monomialArrayPolynomial (Sum.elim eK eN) (fun j => c j+w j*r j))) (rows i) := by
  dsimp only
  rw [← realJetMatrix_monomialArray (Sum.elim eK eN) (normalizedCubeTuple input z x) rows
    (fun j => c j+w j*r j) i, realJetMatrix_sumColumns, Matrix.fromCols_mulVec]
  unfold affineJetUnitMap
  rw [normalizedJetColumns_eq_realJetMatrix]
  have hk := normalizedKernel_reconstruct M s hM S (fun _ => H) hS (fun _ => hH)
    (fun j => c (.inl j)+w (.inl j)*r (.inl j))
  rw [hkernel] at hk
  rw [← hk]
  rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem monomialArrayPolynomial_equiv {C D K : Type*} [Fintype C] [Fintype D]
    (f : C ≃ D) (e : D → K →₀ ℕ) (a : D → ℝ) :
    monomialArrayPolynomial (e ∘ f) (a ∘ f) = monomialArrayPolynomial e a := by
  unfold monomialArrayPolynomial
  exact f.sum_comp (fun d => MvPolynomial.monomial (e d) (a d))

theorem originalMonomialJetMap_measurable_comp {Ω C Z X K α O : Type*}
    [MeasurableSpace Ω] [Fintype C] [Fintype α] [DecidableEq α] [Fintype O]
    (e : C → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (rows : O → Finset α)
    (c w : C → ℝ) (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (x : Ω → X → ℝ) (hx : ∀ j, Measurable (fun a => x a j))
    (r : Ω → C → ℝ) (hr : ∀ j, Measurable (fun a => r a j)) :
    Measurable (fun a => originalMonomialJetMap e input (z a) rows c w (x a) (r a)) := by
  have he (a : Ω) : originalMonomialJetMap e input (z a) rows c w (x a) (r a) =
      polynomialColumns (fun o j => normalizedJetColumn (e j) input (z a) (rows o))
        (x a) (fun j => c j + w j * r a j) := by
    rw [normalizedJetColumns_eq_realJetMatrix]
    funext o
    exact (realJetMatrix_monomialArray e (normalizedCubeTuple input (z a) (x a)) rows
      (fun j => c j + w j * r a j) o).symm
  simp_rw [he]
  exact normalizedJetColumns_measurable_comp e input rows z hz x hx _
    (fun j => measurable_const.add (measurable_const.mul (hr j)))

theorem originalMonomialJetMap_eq_affine {C Z X K α O J N : Type*}
    [Fintype C] [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
    [Fintype J] [DecidableEq J] [Fintype N]
    (f : J ⊕ N ≃ C) (e : C → K →₀ ℕ)
    (M : Matrix O J ℤ) (s : O ↪ J) (hM : (M.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {H : ℝ} (hH : 0 < H)
    (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (rows : O → Finset α) (x : X → ℝ)
    (hkernel : normalizedIntegerColumns M S (fun _ => H) =
      realJetMatrix (fun j => MvPolynomial.monomial (e (f (.inl j))) 1)
        (normalizedCubeTuple input z x) rows) (c w r : C → ℝ) :
    originalMonomialJetMap e input z rows c w x r =
      affineJetUnitMap s
        (normalizedPivotEquiv (M.submatrix id s) hM (fun j => S (s j)) (fun _ => H)
          (fun j => hS (s j)) (fun _ => hH))
        (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns M s)
          (fun j => S j.val) (fun _ => H)))
        (fun n => e (f (.inr n))) input z rows (c ∘ f) (w ∘ f) x (r ∘ f) := by
  have he : Sum.elim (fun j => e (f (.inl j))) (fun n => e (f (.inr n))) = e ∘ f := by
    funext j
    cases j <;> rfl
  funext o
  have hi := affineJetUnitMap_monomial_jet M s hM S hS hH
    (fun j => e (f (.inl j))) (fun n => e (f (.inr n))) input z rows x hkernel
    (c ∘ f) (w ∘ f) (r ∘ f) o
  rw [he] at hi
  have ha : (fun j => (c ∘ f) j + (w ∘ f) j * (r ∘ f) j) =
      (fun j => c j + w j * r j) ∘ f := rfl
  rw [ha, monomialArrayPolynomial_equiv] at hi
  exact hi.symm

theorem originalMonomialJetMap_unit_law {C Z X K α O J N : Type*}
    [Fintype C] [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
    [Fintype J] [DecidableEq J] [Fintype N]
    (f : J ⊕ N ≃ C) (e : C → K →₀ ℕ)
    (M : Matrix O J ℤ) (s : O ↪ J) (hM : (M.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {H : ℝ} (hH : 0 < H)
    (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (rows : O → Finset α) (x : X → ℝ)
    (hkernel : normalizedIntegerColumns M S (fun _ => H) =
      realJetMatrix (fun j => MvPolynomial.monomial (e (f (.inl j))) 1)
        (normalizedCubeTuple input z x) rows)
    (c w : C → ℝ) (hw : ∀ j, 0 < w j) (R : ℝ≥0) (hsupport : ∀ j, |c j| + w j ≤ R) :
    (unitCoefficientSource C).map (originalMonomialJetMap e input z rows c w x) =
      realDensityMeasure volume
        (affineSelectedJetDensity s
          (normalizedPivotEquiv (M.submatrix id s) hM (fun j => S (s j)) (fun _ => H)
            (fun j => hS (s j)) (fun _ => hH))
          (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns M s)
            (fun j => S j.val) (fun _ => H)))
          (fun n => e (f (.inr n))) input z rows (c ∘ f) (w ∘ f) x) := by
  let A := normalizedPivotEquiv (M.submatrix id s) hM (fun j => S (s j)) (fun _ => H)
    (fun j => hS (s j)) (fun _ => hH)
  let F := matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns M s)
    (fun j => S j.val) (fun _ => H))
  let U := affineJetUnitMap s A F (fun n => e (f (.inr n))) input z rows (c ∘ f) (w ∘ f) x
  have hU : Measurable U :=
    affineJetUnitMap_measurable_comp s A F (fun n => e (f (.inr n))) input rows
      (fun _ => c ∘ f) (fun _ => w ∘ f) id measurable_const measurable_const measurable_id
      (fun _ => z) (fun _ => measurable_const) (fun _ => x) (fun _ => measurable_const)
  have he : originalMonomialJetMap e input z rows c w x = U ∘ (fun r => r ∘ f) :=
    funext (fun r => originalMonomialJetMap_eq_affine f e M s hM S hS hH
      input z rows x hkernel c w r)
  rw [he, ← Measure.map_map hU (by fun_prop)]
  have hr : (unitCoefficientSource C).map (fun r => r ∘ f) =
      unitCoefficientSource (J ⊕ N) := by
    simpa only [Equiv.symm_symm] using unitCoefficientSource_reindex f.symm
  rw [hr]
  exact affineSelectedJetDensity_unit_law s A F (fun n => e (f (.inr n)))
    input z rows (c ∘ f) (w ∘ f) (fun j => hw (f j)) R (fun j => hsupport (f j)) x

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedDensityParameterBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

omit [DecidableEq O] in
theorem allocatedNormalizedProfileJet_measurable (a : LayerSamplerAxis I n) :
    Measurable (fun p :
      (PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) ×
        (SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) =>
      allocatedNormalizedProfileJet B U basis S x u rows a p.1 p.2) := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl i =>
    exact originalMonomialJetMap_measurable_comp Subtype.val input rows
      (allocatedContinuousProfileCenters (G := G) B R j i)
      (allocatedContinuousProfileWidths (G := G) B R σ j i)
      (fun _ => fixedReal) (fun _ => measurable_const) Prod.fst
      (fun k => (measurable_pi_apply k).comp measurable_fst) Prod.snd
      (fun k => (measurable_pi_apply k).comp measurable_snd)
  | inr i =>
    exact originalMonomialJetMap_measurable_comp Subtype.val input rows
      (allocatedIntegerProfileCenters (G := G) B R j i)
      (allocatedIntegerProfileWidths (G := G) B R σ j i)
      (fun _ => fixedReal) (fun _ => measurable_const) Prod.fst
      (fun k => (measurable_pi_apply k).comp measurable_fst) Prod.snd
      (fun k => (measurable_pi_apply k).comp measurable_snd)

theorem allocatedNormalizedKernelJet_eq (j : Fin m)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (scalarKernelIntegerJet x (j.val + 1) rows)
        (kernelJetCoefficientScale G (j.val + 1) S.value H) (fun _ => H) =
      realJetMatrix (fun d => MvPolynomial.monomial
        (kernelExponentEmbedding G (PrincipalTupleIndex B (layerSamplerDegree I n)) (j.val + 1) d).val 1)
        (normalizedCubeTuple input fixedReal y) rows := by
  have ht := normalizedMappedKernelJet_eq (j.val + 1) input fixedReal y x (fun _ _ => rfl) rows hH
  exact normalizedIntegerColumns_eq_of_instances ht

theorem allocatedMonomialProfile_unit_law (j : Fin m)
    (s : O ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ((scalarKernelIntegerJet x (j.val + 1) rows).submatrix id s).det ≠ 0)
    {H : ℝ} (hH : 0 < H)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    (c w : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℝ)
    (hw : ∀ e, 0 < w e) (L : ℝ≥0) (hbound : ∀ e, |c e| + w e ≤ L) :
    (unitCoefficientSource (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))).map
        (originalMonomialJetMap Subtype.val input fixedReal rows c w y) =
      realDensityMeasure volume (affineSelectedJetDensity s
        (normalizedPivotEquiv ((scalarKernelIntegerJet x (j.val + 1) rows).submatrix id s) hA
          (fun o => kernelJetCoefficientScale G (j.val + 1) S.value H (s o)) (fun _ => H)
          (fun o => kernelJetCoefficientScale_pos G (j.val + 1) (Nat.cast_pos.mpr S.positive) hH (s o))
          (fun _ => hH))
        (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns (scalarKernelIntegerJet x (j.val + 1) rows) s)
          (fun e => kernelJetCoefficientScale G (j.val + 1) S.value H e.val) (fun _ => H)))
        (allocatedNonkernelExponent B j) input fixedReal rows
        (c ∘ allocatedKernelCoefficientEquiv B j) (w ∘ allocatedKernelCoefficientEquiv B j) y) := by
  have hlaw := originalMonomialJetMap_unit_law
    (allocatedKernelCoefficientEquiv (G := G) B j) Subtype.val
    (scalarKernelIntegerJet x (j.val + 1) rows) s hA
    (kernelJetCoefficientScale G (j.val + 1) S.value H)
    (kernelJetCoefficientScale_pos G (j.val + 1) (Nat.cast_pos.mpr S.positive) hH)
    hH input fixedReal rows y
    (allocatedNormalizedKernelJet_eq B U basis S x u rows j y hH.ne') c w hw L hbound
  have he : (fun d : AllocatedNonkernelCoefficient (G := G) B j =>
      (allocatedKernelCoefficientEquiv (G := G) B j (.inr d)).val) =
      allocatedNonkernelExponent (G := G) B j := rfl
  rw [he] at hlaw
  exact hlaw

include hR hσ in
theorem allocatedContinuousProfileJet_unit_law (j : Fin m) (i : I j)
    (s : O ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ((scalarKernelIntegerJet x (j.val + 1) rows).submatrix id s).det ≠ 0)
    (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (unitCoefficientSource (SamplerCoefficientSlot G B (layerSamplerDegree I n) ⟨j, .inl i⟩)).map
        (allocatedNormalizedProfileJet B U basis S x u rows ⟨j, .inl i⟩ y) =
      realDensityMeasure volume (allocatedContinuousKernelDensity B U basis S j i x u rows s hA y) := by
  change (unitCoefficientSource (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))).map
      (originalMonomialJetMap Subtype.val input fixedReal rows
        (allocatedContinuousProfileCenters (G := G) B R j i)
        (allocatedContinuousProfileWidths (G := G) B R σ j i) y) = _
  exact allocatedMonomialProfile_unit_law B U basis S x u rows j s hA zero_lt_one y
    (allocatedContinuousProfileCenters (G := G) B R j i)
    (allocatedContinuousProfileWidths (G := G) B R σ j i)
    (allocatedContinuousProfileWidths_pos B hR hσ j i) ⟨R j, (hR j).le⟩
    (allocatedContinuousProfile_bound B hR hσ j i hσ1)

include hR hσ in
theorem allocatedIntegerProfileJet_unit_law (j : Fin m) (i : Fin (n j))
    (s : O ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ((scalarKernelIntegerJet x (j.val + 1) rows).submatrix id s).det ≠ 0)
    (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (unitCoefficientSource (SamplerCoefficientSlot G B (layerSamplerDegree I n) ⟨j, .inr i⟩)).map
        (allocatedNormalizedProfileJet B U basis S x u rows ⟨j, .inr i⟩ y) =
      realDensityMeasure volume (allocatedIntegerKernelDensity B U basis S j i x u rows s hA y) := by
  have hH : 0 < (basisAxisScale (basis j) i : ℝ) := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
  change (unitCoefficientSource (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))).map
      (originalMonomialJetMap Subtype.val input fixedReal rows
        (allocatedIntegerProfileCenters (G := G) B R j i)
        (allocatedIntegerProfileWidths (G := G) B R σ j i) y) = _
  exact allocatedMonomialProfile_unit_law B U basis S x u rows j s hA hH y
    (allocatedIntegerProfileCenters (G := G) B R j i)
    (allocatedIntegerProfileWidths (G := G) B R σ j i)
    (allocatedIntegerProfileWidths_pos B hR hσ j i) ⟨R j, (hR j).le⟩
    (allocatedKernelProfile_bound B hR hσ j i hσ1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a)
local notation "activeCoefficient" => ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) grid
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

include hR hσ in
theorem allocatedNormalizedLongJetFactor_probability (hσ1 : ∀ j, σ j ≤ 1)
    (y : activeInput → ℝ) (a : {a // ¬grid a}) :
    (∀ v, 0 ≤ allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a v) ∧
    Integrable (allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a) ∧
    (∫ v, allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a v) = 1 := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i => exact allocatedContinuousKernelDensity_probability_data B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j) y
  | inr i => exact allocatedIntegerKernelDensity_probability_data B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j) y

include hR hσ in
theorem allocatedNormalizedLongJetFactor_measurable (hσ1 : ∀ j, σ j ≤ 1)
    (a : {a // ¬grid a}) :
    Measurable (fun p : (activeInput → ℝ) × (O a.val.1 → ℝ) =>
      allocatedNormalizedLongJetFactor B U basis S x u rows s hA p.1 a p.2) := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i => exact allocatedContinuousKernelDensity_measurable B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j)
  | inr i => exact allocatedIntegerKernelDensity_measurable B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j)

omit [∀ j, DecidableEq (O j)] in
theorem allocatedNormalizedLongJetMap_measurable :
    Measurable (fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) =>
      allocatedNormalizedLongJetMap B U basis S x u rows p.1 p.2) := by
  unfold allocatedNormalizedLongJetMap sigmaAxisSampler
  apply measurable_pi_iff.mpr
  intro o
  have hc : Measurable (fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) =>
      (p.1, fun e : SamplerCoefficientSlot G B (layerSamplerDegree I n) o.1.val => p.2 ⟨o.1, e⟩)) :=
    measurable_fst.prodMk (measurable_pi_iff.mpr (fun e =>
      (measurable_pi_apply (⟨o.1, e⟩ : activeCoefficient)).comp measurable_snd))
  exact (measurable_pi_apply o.2).comp
    ((allocatedNormalizedProfileJet_measurable B U basis S x u (rows o.1.val.1) o.1.val).comp
      (f := fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) =>
        (p.1, fun e => p.2 ⟨o.1, e⟩)) hc)

include hR hσ in
theorem allocatedNormalizedLongJetDensity_measurable (hσ1 : ∀ j, σ j ≤ 1) :
    Measurable (Function.uncurry (allocatedNormalizedLongJetDensity B U basis S x u rows s hA)) := by
  change Measurable (fun p : (activeInput → ℝ) × (realOutput → ℝ) =>
    ∏ a, allocatedNormalizedLongJetFactor B U basis S x u rows s hA p.1 a (fun o => p.2 ⟨a, o⟩))
  apply Finset.measurable_prod
  intro a _
  have hc : Measurable (fun p : (activeInput → ℝ) × (realOutput → ℝ) =>
      (p.1, fun o : O a.val.1 => p.2 ⟨a, o⟩)) :=
    measurable_fst.prodMk (measurable_pi_iff.mpr (fun o =>
      (measurable_pi_apply (⟨a, o⟩ : realOutput)).comp measurable_snd))
  exact (allocatedNormalizedLongJetFactor_measurable B U basis hR hσ S x u rows s hA hσ1 a).comp
    (f := fun p : (activeInput → ℝ) × (realOutput → ℝ) => (p.1, fun o => p.2 ⟨a, o⟩)) hc

include hR hσ in
theorem allocatedNormalizedLongJetDensity_probability (hσ1 : ∀ j, σ j ≤ 1)
    (y : activeInput → ℝ) :
    (∀ v, 0 ≤ allocatedNormalizedLongJetDensity B U basis S x u rows s hA y v) ∧
    Integrable (allocatedNormalizedLongJetDensity B U basis S x u rows s hA y) ∧
    (∫ v, allocatedNormalizedLongJetDensity B U basis S x u rows s hA y v) = 1 := by
  have hp := allocatedNormalizedLongJetFactor_probability B U basis hR hσ S x u rows s hA hσ1 y
  have hm : (∫ v, allocatedNormalizedLongJetDensity B U basis S x u rows s hA y v) = 1 := by
    unfold allocatedNormalizedLongJetDensity
    rw [sigmaAxisWeight_integral]
    exact Finset.prod_eq_one (fun a _ => (hp a).2.2)
  exact ⟨sigmaAxisWeight_nonneg _ (fun a => (hp a).1),
    Integrable.of_integral_ne_zero (hm.trans_ne one_ne_zero), hm⟩

include hR hσ in
theorem allocatedNormalizedLongJetDensity_unit_law (hσ1 : ∀ j, σ j ≤ 1)
    (y : activeInput → ℝ) :
    (unitCoefficientSource activeCoefficient).map
        (allocatedNormalizedLongJetMap B U basis S x u rows y) =
      realDensityMeasure volume (allocatedNormalizedLongJetDensity B U basis S x u rows s hA y) := by
  have hm (a : {a // ¬grid a}) :
      Measurable (allocatedNormalizedProfileJet B U basis S x u (rows a.val.1) a.val y) :=
    Measurable.of_uncurry_left
      (f := allocatedNormalizedProfileJet B U basis S x u (rows a.val.1) a.val) (x := y)
      (allocatedNormalizedProfileJet_measurable B U basis S x u (rows a.val.1) a.val)
  have hlaw (a : {a // ¬grid a}) :
      (unitCoefficientSource (SamplerCoefficientSlot G B (layerSamplerDegree I n) a.val)).map
          (allocatedNormalizedProfileJet B U basis S x u (rows a.val.1) a.val y) =
        realDensityMeasure volume (allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a) := by
    rcases a with ⟨⟨j, a⟩, ha⟩
    cases a with
    | inl i => exact allocatedContinuousProfileJet_unit_law B U basis hR hσ S x u (rows j) j i (s j) (hA j) (hσ1 j) y
    | inr i => exact allocatedIntegerProfileJet_unit_law B U basis hR hσ S x u (rows j) j i (s j) (hA j) (hσ1 j) y
  unfold allocatedNormalizedLongJetMap
  rw [unitCoefficientSource_sigma, sigmaAxisSampler_image_law _ _ hm]
  simp_rw [hlaw]
  have hp := allocatedNormalizedLongJetFactor_probability B U basis hR hσ S x u rows s hA hσ1 y
  exact sigmaAxisMeasure_density _ (fun a => (hp a).2.1) (fun a => (hp a).1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m,
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "budget" => allocatedDensityLog (G := G) B α O P
local notation "bound" => NNReal.mk (Real.exp budget) (le_of_lt (Real.exp_pos budget))
local notation "radius" j => NNReal.mk (R j) (le_of_lt (hR j))

include hR hσ hM hi hP hMP hRP hRi hσi hcount

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "bound" => NNReal.mk (Real.exp (allocatedDensityLog (G := G) B α O P))
  (le_of_lt (Real.exp_pos _))
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

include hR hσ hM hi hP hMP hRP hRi hσi hcount

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineRadiusLog
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a)
local notation "activeCoefficient" => ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) grid
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) → ℝ)

include hR hσ in
theorem allocatedAffineLongJetDensity_measurable (hσ1 : ∀ j, σ j ≤ 1) :
    Measurable (Function.uncurry (allocatedAffineLongJetDensity B U basis S x u rows s hA center width)) := by
  have hin : Measurable (fun p : (activeInput → ℝ) × (realOutput → ℝ) =>
      ((fun i => center i + width i * p.1 i), p.2)) := by
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro i
      exact measurable_const.add (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst))
    · exact measurable_snd
  exact (allocatedNormalizedLongJetDensity_measurable B U basis hR hσ S x u rows s hA hσ1).comp
    (f := fun p : (activeInput → ℝ) × (realOutput → ℝ) => ((fun i => center i + width i * p.1 i), p.2)) hin

include hR hσ in
theorem allocatedAffineLongJetDensity_probability (hσ1 : ∀ j, σ j ≤ 1) (y : activeInput → ℝ) :
    (∀ v, 0 ≤ allocatedAffineLongJetDensity B U basis S x u rows s hA center width y v) ∧
    Integrable (allocatedAffineLongJetDensity B U basis S x u rows s hA center width y) ∧
    (∫ v, allocatedAffineLongJetDensity B U basis S x u rows s hA center width y v) = 1 :=
  allocatedNormalizedLongJetDensity_probability B U basis hR hσ S x u rows s hA hσ1 _

omit [∀ j, DecidableEq (O j)] in
theorem allocatedAffineLongJetMap_measurable :
    Measurable (fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) =>
      allocatedNormalizedLongJetMap B U basis S x u rows (fun i => center i + width i * p.1 i) p.2) := by
  have hin : Measurable (fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) =>
      ((fun i => center i + width i * p.1 i), p.2)) := by
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro i
      exact measurable_const.add (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst))
    · exact measurable_snd
  exact (allocatedNormalizedLongJetMap_measurable B U basis S x u rows).comp
    (f := fun p : (activeInput → ℝ) × (activeCoefficient → ℝ) => ((fun i => center i + width i * p.1 i), p.2)) hin

include hR hσ in
theorem allocatedAffineLongJetProxy_image_law (hσ1 : ∀ j, σ j ≤ 1) :
    ((jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)).prod
      (unitCoefficientSource activeCoefficient)).map
      (fun p => allocatedNormalizedLongJetMap B U basis S x u rows
        (fun i => center i + width i * p.1 i) p.2) =
      realDensityMeasure volume (allocatedAffineLongJetProxy B U basis S x u rows s hA center width) := by
  exact densityMixture_image_law _ _ volume _
    (allocatedAffineLongJetMap_measurable B U basis S x u rows center width) _
    (allocatedAffineLongJetDensity_measurable B U basis hR hσ S x u rows s hA center width hσ1)
    (allocatedAffineLongJetDensity_probability B U basis hR hσ S x u rows s hA center width hσ1)
    (by
      intro y
      change (unitCoefficientSource activeCoefficient).map
        (allocatedNormalizedLongJetMap B U basis S x u rows
          (fun i => center i + width i * y i)) =
        realDensityMeasure volume (allocatedNormalizedLongJetDensity B U basis S x u rows s hA
          (fun i => center i + width i * y i))
      exact allocatedNormalizedLongJetDensity_unit_law B U basis hR hσ S x u rows s hA hσ1 _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := degree) (α := α) (fun a => ¬grid a)
local notation "activeCoefficient" => ActiveProfileCoefficientIndex G B degree grid
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "sets" => (fun a : {a // ¬grid a} => rows (Sigma.fst (Subtype.val a)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := degree) (α := α) (fun a => ¬grid a)
local notation "activeCoefficient" => ActiveProfileCoefficientIndex G B degree grid
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "sets" => (fun a : {a // ¬grid a} => rows (Sigma.fst (Subtype.val a)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := degree) (α := α) (fun a => ¬grid a)
local notation "activeCoefficient" => ActiveProfileCoefficientIndex G B degree grid
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "sets" => (fun a : {a // ¬grid a} => rows (Sigma.fst (Subtype.val a)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  {α : Type*} [Fintype α] [DecidableEq α]
  {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  {α : Type*} [Fintype α] [DecidableEq α]
  {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_image_law.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_image_law.{u_1, u_2, u_3, u_4, u_5, u_6}
