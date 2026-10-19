-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedContinuousKernel_image_law_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:12:03.107307+00:00
-- url     : https://prove2.me/submissions/7b5134e6-8c4d-4999-819c-e70844e84b76

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B176

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

end OAI
end

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass
namespace OAI

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

open scoped BigOperators NNReal

theorem booleanJetColumnPolynomial_eval {K P α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ) (s : Finset α) (x : P → ℝ) :
    MvPolynomial.eval x (booleanJetColumnPolynomial e input s) =
      booleanCoefficient (fun t => ∏ k ∈ e.support,
        (∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (input k r)) ^ e k) s := by
  simp only [booleanJetColumnPolynomial, booleanCoefficient_map, polynomialMonomial_eval, booleanAffineInput_eval]

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedJetColumns
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem frozenTupleCoordinate_eval {Z P : Type*} (z : Z → ℝ) (x : P → ℝ) (i : Z ⊕ P) :
    MvPolynomial.eval x (frozenTupleCoordinate z i) = Sum.elim z x i := by
  cases i <;> simp [frozenTupleCoordinate]

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

theorem normalizedIntegerJetColumns_eq {Z P K α I N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ)
    (rows : I → Finset α) (x : P → ℝ) (vertices : Finset α → K → ℤ) (T : K → ℝ)
    (hcoords : ∀ t k, (vertices t k : ℝ) / T k = normalizedCubeTuple input z x t k)
    {H : ℝ} (hH : H ≠ 0) :
    matrixSupCLM (normalizedIntegerColumns
      (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) vertices rows)
      (fun n => H / monomialScale T (e n)) (fun _ => H)) =
      polynomialColumns (fun i n => normalizedJetColumn (e n) input z (rows i)) x := by
  rw [normalizedIntegerMonomialJetMatrix_eq e vertices rows T hH]
  simp_rw [hcoords]
  exact (normalizedJetColumns_eq_realJetMatrix e input z rows x).symm

theorem normalizedCubeTuple_eq_integerAffineCube {Z P K α : Type*}
    [Fintype α] [DecidableEq α] (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (x : P → ℝ)
    (root : K → ℤ) (difference : α → K → ℤ) (T : K → ℝ)
    (hroot : ∀ k, Sum.elim z x (input k none) = (root k : ℝ) / T k)
    (hdiff : ∀ i k, Sum.elim z x (input k (some i)) = (difference i k : ℝ) / T k)
    (t : Finset α) (k : K) :
    normalizedCubeTuple input z x t k = (integerAffineCube root difference t k : ℝ) / T k := by
  rw [← realAffineCube_normalized_integer]
  simp only [normalizedCubeTuple, Fintype.sum_option, booleanFeature, one_mul, hroot, hdiff,
    ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, realAffineCube]

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScaleIndependence
namespace OAI


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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalResidueMixture
namespace OAI

section

namespace Erdos3

theorem integerMappedCubeTuple_normalized {Z X K α : Type*} [Fintype α] [DecidableEq α]
    (input : K → Option α → Z ⊕ X) (z : Z → ℤ) (x : X → ℤ)
    (zr : Z → ℝ) (xr : X → ℝ) (T : K → ℝ)
    (hn : ∀ k a, ((Sum.elim z x (input k a) : ℤ) : ℝ)/T k = Sum.elim zr xr (input k a))
    (t : Finset α) (k : K) :
    (integerMappedCubeTuple input z x t k : ℝ)/T k = normalizedCubeTuple input zr xr t k := by
  exact (normalizedCubeTuple_eq_integerAffineCube input zr xr
    (fun k => Sum.elim z x (input k none)) (fun i k => Sum.elim z x (input k (some i))) T
    (fun k => (hn k none).symm) (fun i k => (hn k (some i)).symm) t k).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerMatrixRealDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix

variable {O J : Type*} [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
variable (A : Matrix O J ℤ) (s : O ↪ J) (hA : (A.submatrix id s).det ≠ 0)

omit [DecidableEq J] in
theorem affineCoefficientProduct_density (c w : J → ℝ) (hw : ∀ j, 0 < w j) :
    Measure.pi (fun j => affineCoefficientMeasure (c j) (w j)) =
      realDensityMeasure volume (affineProductProfile c w) :=
  independentCoordinateDensity_measure (fun j => affineProbabilityProfile (c j) (w j))
    (fun j => affineProbabilityProfile_integrable (c j) (hw j))
    (fun j => affineProbabilityProfile_nonneg (c j) (hw j))
    (fun j => affineProbabilityProfile_integral (c j) (hw j))

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

theorem unitCoefficientSource_affine_law {I : Type*} [Fintype I]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) :
    (unitCoefficientSource I).map (fun r i => c i+w i*r i) =
      realDensityMeasure volume (affineProductProfile c w) :=
  affineProductProfile_law c w hw

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

theorem affineCoefficientProduct_unit_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (c w : J → ℝ) (hw : ∀ j, 0 < w j) :
    (unitCoefficientSource I).map (fun r j => c j+w j*r (e.symm j)) =
      Measure.pi (fun j => affineCoefficientMeasure (c j) (w j)) := by
  have hm : Measurable (fun r : J → ℝ => fun j => c j+w j*r j) := by fun_prop
  have he : Measurable (fun r : I → ℝ => r ∘ e.symm) := by fun_prop
  change (unitCoefficientSource I).map
    ((fun r : J → ℝ => fun j => c j+w j*r j) ∘ (fun r => r ∘ e.symm)) = _
  rw [← Measure.map_map hm he, unitCoefficientSource_reindex,
    unitCoefficientSource_affine_law c w hw, affineCoefficientProduct_density c w hw]

theorem normalizedIntegerColumns_one_mulVec {O J : Type*}
    [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    (A : Matrix O J ℤ) (S v : J → ℝ) :
    A.map (Int.cast : ℤ → ℝ) *ᵥ (fun j => S j*v j) =
      normalizedIntegerColumns A S (fun _ => 1) *ᵥ v := by
  ext i
  change (∑ j, (A i j : ℝ)*(S j*v j)) = ∑ j, normalizedIntegerColumns A S (fun _ => 1) i j*v j
  simp only [normalizedIntegerColumns_entry_div, div_one]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem affineCoefficientProduct_scaled_image {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [DecidableEq O]
    (e : I ≃ J) (A : Matrix O J ℤ) (c w S : J → ℝ)
    (hw : ∀ j, 0 < w j) (hS : ∀ j, 0 < S j) :
    (Measure.pi (fun j => affineCoefficientMeasure (S j*c j) (S j*w j))).map
      (fun a => A.map (Int.cast : ℤ → ℝ) *ᵥ a) =
      (unitCoefficientSource I).map (fun r =>
        normalizedIntegerColumns (A.submatrix id e) (S ∘ e) (fun _ => 1) *ᵥ
          (fun i => c (e i)+w (e i)*r i)) := by
  have hsample : Measurable (fun r : I → ℝ => fun j => S j*c j+S j*w j*r (e.symm j)) := by fun_prop
  have hmatrix : Measurable (fun a => A.map (Int.cast : ℤ → ℝ) *ᵥ a) :=
    (matrixSupCLM _).continuous.measurable
  rw [← affineCoefficientProduct_unit_reindex e _ _ (fun j => mul_pos (hS j) (hw j)),
    Measure.map_map hmatrix hsample]
  congr 1
  funext r
  let v : I → ℝ := fun i => S (e i)*(c (e i)+w (e i)*r i)
  have hv : (fun j => S j*c j+S j*w j*r (e.symm j)) = v ∘ e.symm := by
    funext j
    simp only [v, Function.comp_apply, e.apply_symm_apply]
    ring
  change A.map (Int.cast : ℤ → ℝ) *ᵥ (fun j => S j*c j+S j*w j*r (e.symm j)) = _
  have hr := Matrix.submatrix_mulVec_equiv (A.map (Int.cast : ℤ → ℝ)) v id e
  simp only [Function.comp_id] at hr
  rw [hv, ← hr]
  exact normalizedIntegerColumns_one_mulVec (A.submatrix id e) (S ∘ e) _

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineL1Parameter
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

theorem partitionedPrincipalInput_normalized (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z) (zi : Z → ℤ) (zr : Z → ℝ) (T : G → ℝ)
    (hfixed : ∀ g a, (zi (extra g a) : ℝ)/T g = zr (extra g a))
    (L : PrincipalTupleIndex B h → ℕ)
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L)
    (k : SamplerTupleIndex G B h) (a : Option α) :
    ((Sum.elim (Sum.elim zi (principalTupleIntegers u)) (principalTupleIntegers v)
        (partitionedPrincipalInput P extra k a) : ℤ) : ℝ) /
        Sum.elim T (fun j => (L j : ℝ)) k =
      Sum.elim (Sum.elim zr (principalTupleNormalized (principalAxisLength P L) u))
        (principalTupleNormalized (principalAxisLength (fun d => ¬P d) L) v)
        (partitionedPrincipalInput P extra k a) := by
  rcases k with g | ⟨d, b, r⟩
  · exact hfixed g a
  · by_cases hp : P d <;>
      simp [partitionedPrincipalInput, principalTupleNormalized, principalAxisLength, hp]

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

theorem monomialScale_kernelExponent {G X : Type*} {h : ℕ} (T : G ⊕ X → ℝ)
    (d : BoundedIntegerExponent G h) :
    monomialScale T (kernelExponentEmbedding G X h d).val =
      monomialScale (fun g => T (.inl g)) d.val :=
  Finsupp.prod_embDomain

theorem kernelExponent_eval_monomial {G X : Type*} {h : ℕ} (x : G ⊕ X → ℤ)
    (d : BoundedIntegerExponent G h) :
    MvPolynomial.eval x (MvPolynomial.monomial (kernelExponentEmbedding G X h d).val 1) =
      MvPolynomial.eval (fun g => x (.inl g)) (MvPolynomial.monomial d.val 1) := by
  change MvPolynomial.eval x (MvPolynomial.monomial (d.val.embDomain Function.Embedding.inl) 1) = _
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_embDomain]
  rfl

theorem integerMappedCubeTuple_kernel {G X Z Y α : Type*}
    (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℤ) (y : Y → ℤ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℤ)) (t : Finset α) :
    (fun g => integerMappedCubeTuple input z y t (.inl g)) =
      integerAffineCube (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) t := by
  funext g
  simp only [integerMappedCubeTuple, integerAffineCube, hfixed, scalarCubeDifferenceMatrix, sampledColumnMatrix]

theorem integerMappedJetMatrix_kernel {G X Z Y α O : Type*} [Fintype G] [DecidableEq α]
    (h : ℕ) (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℤ) (y : Y → ℤ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℤ)) (rows : O → Finset α) :
    (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (G ⊕ X) h => d.val)
      input z rows y).submatrix id (kernelExponentEmbedding G X h) = scalarKernelIntegerJet x h rows := by
  ext o d
  change booleanCoefficient (fun t => MvPolynomial.eval (integerMappedCubeTuple input z y t)
      (MvPolynomial.monomial (kernelExponentEmbedding G X h d).val 1)) (rows o) =
    booleanCoefficient (fun t => MvPolynomial.eval
      (integerAffineCube (fun g => (x g none : ℤ)) (scalarCubeDifferenceMatrix x) t)
      (MvPolynomial.monomial d.val 1)) (rows o)
  apply congrArg (fun f : Finset α → ℤ => booleanCoefficient f (rows o))
  funext t
  rw [kernelExponent_eval_monomial, integerMappedCubeTuple_kernel input z y x hfixed t]

theorem integerMappedJetMatrix_kernel_split {G X Z Y α O : Type*} [Fintype G] [DecidableEq α]
    (h : ℕ) (input : G ⊕ X → Option α → Z ⊕ Y) (z : Z → ℤ) (y : Y → ℤ)
    {L : ℕ} (x : G → IntegerScalarCubeBox α L)
    (hfixed : ∀ g a, Sum.elim z y (input (.inl g) a) = (x g a : ℤ)) (rows : O → Finset α) :
    (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (G ⊕ X) h => d.val)
      input z rows y).submatrix id (kernelCoefficientEquiv G X h) =
      Matrix.fromCols (scalarKernelIntegerJet x h rows)
        (integerMappedJetMatrix (fun d : NonkernelCoefficient G X h => d.val.val) input z rows y) := by
  ext o d
  cases d with
  | inl d => exact congrFun (congrFun (integerMappedJetMatrix_kernel h input z y x hfixed rows) o) d
  | inr d => rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal

theorem normalizedJoinedMatrix_affineJetUnitMap {Z X K α O J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
    [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix O J ℤ) (C : Matrix O N ℤ) (s : O ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (T : N → ℝ) (hS : ∀ j, 0 < S j)
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : O → Finset α) (x : X → ℝ)
    (hC : matrixSupCLM (normalizedIntegerColumns C T (fun _ => 1)) =
      polynomialColumns (fun o n => normalizedJetColumn (e n) input z (rows o)) x)
    (c w r : J ⊕ N → ℝ) :
    normalizedIntegerColumns (Matrix.fromCols A C) (Sum.elim S T) (fun _ => 1) *ᵥ
      (fun j => c j+w j*r j) =
      affineJetUnitMap s
        (normalizedPivotEquiv (A.submatrix id s) hA (fun j => S (s j)) (fun _ => 1)
          (fun j => hS (s j)) (fun _ => zero_lt_one))
        (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s)
          (fun j => S j.val) (fun _ => 1))) e input z rows c w x r := by
  let v : J ⊕ N → ℝ := fun j => c j+w j*r j
  have hv : selectedSplitCoefficients s ((selectedSplitMeasurableEquiv s).symm v) = v :=
    (selectedSplitMeasurableEquiv s).apply_symm_apply v
  have hm := selectedSplitCoefficients_normalized_matrix A C s hA S T (fun _ => 1) hS
    (fun _ => zero_lt_one) ((selectedSplitMeasurableEquiv s).symm v)
  rw [hv, hC] at hm
  simpa only [v, selectedSplitMeasurableEquiv_symm_apply, splitFreeColumns_apply,
    Sum.elim_inl, Sum.elim_inr, affineJetUnitMap, add_assoc] using hm

theorem normalizedJoinedMatrix_affineDensity_law {Z X K α O J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
    [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix O J ℤ) (C : Matrix O N ℤ) (s : O ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (T : N → ℝ) (hS : ∀ j, 0 < S j)
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : O → Finset α) (x : X → ℝ)
    (hC : matrixSupCLM (normalizedIntegerColumns C T (fun _ => 1)) =
      polynomialColumns (fun o n => normalizedJetColumn (e n) input z (rows o)) x)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R) :
    (unitCoefficientSource (J ⊕ N)).map (fun r =>
      normalizedIntegerColumns (Matrix.fromCols A C) (Sum.elim S T) (fun _ => 1) *ᵥ
        (fun j => c j+w j*r j)) =
      realDensityMeasure volume
        (affineSelectedJetDensity s
          (normalizedPivotEquiv (A.submatrix id s) hA (fun j => S (s j)) (fun _ => 1)
            (fun j => hS (s j)) (fun _ => zero_lt_one))
          (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s)
            (fun j => S j.val) (fun _ => 1))) e input z rows c w x) := by
  simp_rw [normalizedJoinedMatrix_affineJetUnitMap A C s hA S T hS e input z rows x hC]
  exact affineSelectedJetDensity_unit_law s _ _ e input z rows c w hw R hsupport x

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

local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

theorem allocatedKernelJet_split {α O : Type*} [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (u : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) grid → ℤ)
    (v : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℤ)
    (rows : O → Finset α) :
    (integerMappedJetMatrix (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) => d.val)
      (partitionedPrincipalInput grid (fun g a => (g, a)))
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v).submatrix id reindex =
      Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) rows)
        (integerMappedJetMatrix (allocatedNonkernelExponent B j)
          (partitionedPrincipalInput grid (fun g a => (g, a)))
          (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) u) rows v) :=
  integerMappedJetMatrix_kernel_split (j.val+1) _ _ _ x (fun _ _ => rfl) rows

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

theorem allocatedContinuousProfileScales_pos (j : Fin m) (d) :
    0 < allocatedContinuousProfileScales B U basis S j d :=
  one_div_pos.mpr (monomialScale_pos _
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v)) d.val)

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

theorem allocatedLayerCenters_scale (j : Fin m) (i : I j) (d) :
    allocatedLayerCenters B U basis S j i d =
      allocatedContinuousProfileScales B U basis S j d * allocatedContinuousProfileCenters B R j i d := by
  unfold allocatedLayerCenters allocatedArrayCenters allocatedContinuousProfileScales
    allocatedContinuousProfileCenters
  ring

theorem allocatedLayerWidths_scale (j : Fin m) (i : I j) (d) :
    allocatedLayerWidths B U basis S j i d =
      allocatedContinuousProfileScales B U basis S j d * allocatedContinuousProfileWidths B R σ j i d := by
  unfold allocatedLayerWidths allocatedArrayWidths allocatedContinuousProfileScales
    allocatedContinuousProfileWidths
  ring

theorem allocatedContinuousProfileScales_split (j : Fin m) :
    allocatedContinuousProfileScales B U basis S j ∘ allocatedKernelCoefficientEquiv B j =
      Sum.elim (kernelJetCoefficientScale G (j.val+1) S.value 1)
        (fun d => 1 / monomialScale (layerSamplerBox B U basis S) (allocatedNonkernelExponent B j d)) := by
  funext d
  cases d with
  | inl d =>
    change 1 / monomialScale (layerSamplerBox B U basis S)
      (kernelExponentEmbedding G (PrincipalTupleIndex B (layerSamplerDegree I n)) (j.val+1) d).val = _
    rw [monomialScale_kernelExponent]
    rfl
  | inr d => rfl

variable (j : Fin m) (i : I j)

local notation "centers" => allocatedContinuousProfileCenters (G := G) B R j i
local notation "widths" => allocatedContinuousProfileWidths (G := G) B R σ j i
local notation "scales" => allocatedContinuousProfileScales B U basis S j
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

theorem allocatedContinuous_reindexed_image_law {O : Type*} [Fintype O] [DecidableEq O]
    (A : Matrix O (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) ℤ) :
    (allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inl i⟩).map
      (fun a => A.map (Int.cast : ℤ → ℝ) *ᵥ a) =
      (unitCoefficientSource (BoundedIntegerExponent G (j.val+1) ⊕ AllocatedNonkernelCoefficient B j)).map
        (fun r => normalizedIntegerColumns (A.submatrix id reindex) (scales ∘ reindex) (fun _ => 1) *ᵥ
          (fun d => centers (reindex d)+widths (reindex d)*r d)) := by
  change (Measure.pi (fun d => affineCoefficientMeasure
    (allocatedLayerCenters B U basis S j i d) (allocatedLayerWidths B U basis S j i d))).map _ = _
  simp_rw [allocatedLayerCenters_scale, allocatedLayerWidths_scale]
  exact affineCoefficientProduct_scaled_image reindex A centers widths scales
    (allocatedContinuousProfileWidths_pos B hR hσ j i) (allocatedContinuousProfileScales_pos B U basis S j)

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

omit [Fintype α] [DecidableEq α] in
theorem allocatedPartitionedInput_normalized
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (k : LayerSamplerVariables G I n B) (a : Option α) :
    ((Sum.elim fixedInteger (principalTupleIntegers v) (input k a) : ℤ) : ℝ) /
      layerSamplerBox B U basis S k =
      Sum.elim fixedReal (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
        (input k a) := by
  have hbox : layerSamplerBox B U basis S =
      Sum.elim (fun _ : G => (S.value : ℝ)) (fun d => (sides d : ℝ)) := by
    funext k
    cases k <;> rfl
  rw [hbox]
  exact partitionedPrincipalInput_normalized grid (fun g a => (g, a))
    (fun ga : G × Option α => (x ga.1 ga.2 : ℤ))
    (fun ga : G × Option α => ((x ga.1 ga.2 : ℤ) : ℝ) / (S.value : ℝ))
    (fun _ => (S.value : ℝ)) (fun _ _ => rfl) sides u v k a

theorem allocatedContinuousKernel_image_law_s2_oai (hσ1 : σ j ≤ 1)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    (allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inl i⟩).map
      (fun a => (integerMappedJetMatrix
        (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) => d.val)
        input fixedInteger rows (principalTupleIntegers v)).map (Int.cast : ℤ → ℝ) *ᵥ a) =
      realDensityMeasure volume
        (allocatedContinuousKernelDensity B U basis S j i x u rows s hA
          (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)) := by
  rw [allocatedContinuous_reindexed_image_law B U basis hR hσ S j i,
    allocatedKernelJet_split B U basis S j x (principalTupleIntegers u) (principalTupleIntegers v) rows,
    allocatedContinuousProfileScales_split]
  have hn := integerMappedCubeTuple_normalized input fixedInteger (principalTupleIntegers v) fixedReal
    (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v) (layerSamplerBox B U basis S)
    (allocatedPartitionedInput_normalized B U basis S x u v)
  have hc := normalizedIntegerJetColumns_eq (allocatedNonkernelExponent B j) input fixedReal rows
    (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
    (integerMappedCubeTuple input fixedInteger (principalTupleIntegers v)) (layerSamplerBox B U basis S)
    hn (H := 1) one_ne_zero
  have hlaw := normalizedJoinedMatrix_affineDensity_law (scalarKernelIntegerJet x (j.val+1) rows)
    (integerMappedJetMatrix (allocatedNonkernelExponent B j) input fixedInteger rows (principalTupleIntegers v))
    s hA kernelScale (fun d => 1 / monomialScale (layerSamplerBox B U basis S) (allocatedNonkernelExponent B j d))
    (kernelJetCoefficientScale_pos G (j.val+1) (by exact_mod_cast S.positive) zero_lt_one)
    (allocatedNonkernelExponent B j) input fixedReal rows
    (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v) hc
    (centers ∘ reindex) (widths ∘ reindex)
    (fun d => allocatedContinuousProfileWidths_pos B hR hσ j i (reindex d))
    ⟨R j, (hR j).le⟩ (fun d => allocatedContinuousProfile_bound B hR hσ j i hσ1 (reindex d))
  refine Eq.trans ?_ hlaw
  congr 1
  funext r
  apply congrArg (fun M => M *ᵥ (fun d => centers (reindex d)+widths (reindex d)*r d))
  congr 1
  exact Subsingleton.elim _ _

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedContinuousKernel_image_law_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedContinuousKernel_image_law_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
