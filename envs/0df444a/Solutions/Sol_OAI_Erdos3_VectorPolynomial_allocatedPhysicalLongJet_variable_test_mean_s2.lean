-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedPhysicalLongJet_variable_test_mean_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:31:47.857717+00:00
-- url     : https://prove2.me/submissions/da32189b-ab5c-400f-b86f-e97e0c492d3f

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedContinuousKernel_image_law_s2

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityMixtureAELaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_real_mass {X : Type*} (p : PMF X) : (∑' x, (p x).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (p.apply_ne_top), p.tsum_coe, ENNReal.toReal_one]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

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

open scoped BigOperators

theorem affineCoefficientPMF_apply {I : Type*} [Fintype I]
    (c w S : I → ℝ) (hw : ∀ i, 0 < w i) (hS : ∀ i, 0 < S i)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → affineProductProfile c w x = 0)
    (hZ : 0 < coefficientWeightSum (affineProductProfile c w) S) (z : I → ℤ) :
    (coefficientPMF (affineProductProfile c w) (affineProductProfile_nonneg c w hw)
      S hS hsupport hZ z).toReal =
      ∏ i, (shiftedSmoothCoefficientPMF (c i * S i) (w i * S i) (mul_pos (hw i) (hS i))
        (affineProfile_coordinate_sum_pos c w S hw hS hZ i) (z i)).toReal := by
  rw [coefficientPMF_apply, affineProductProfile_sample c w S hw hS,
    affineProductProfile_sample_sum c w S hw hS,
    mul_div_mul_left _ _ (profileWidthFactor_pos w hw).ne']
  simp only [shiftedSmoothCoefficientPMF_apply, smoothProductProfile, Finset.prod_div_distrib]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientJetScalar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val+1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val+1) → PMF ℤ)

theorem coefficientAxisLaw_probability [Fintype K]
    (hw : ∀ j i d, 0 < w j i d) (a : LayerSamplerAxis I n) :
    IsProbabilityMeasure (coefficientAxisLaw c w p a) := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl i =>
    let : ∀ d, IsProbabilityMeasure (affineCoefficientMeasure (c j i d) (w j i d)) :=
      fun d => affineCoefficientMeasure_probability _ (hw j i d)
    change IsProbabilityMeasure (Measure.pi (fun d => affineCoefficientMeasure (c j i d) (w j i d)))
    infer_instance
  | inr i =>
    change IsProbabilityMeasure (Measure.pi (fun d => (p j i d).toMeasure))
    infer_instance

theorem coefficientAxisEquiv_measurePreserving [Fintype K] [∀ j, Fintype (I j)]
    (hw : ∀ j i d, 0 < w j i d) :
    MeasurePreserving (coefficientAxisEquiv K I n)
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j)))
      (Measure.pi (coefficientAxisLaw c w p)) := by
  let laws := coefficientAxisLaw c w p
  let : ∀ a, IsProbabilityMeasure (laws a) := coefficientAxisLaw_probability c w p hw
  have hinner (j : Fin m) : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun a : I j ⊕ Fin (n j) => CoefficientAxisRow K ⟨j, a⟩)).symm
      (mixedScalarArrayLaw (c j) (w j) (p j))
      (Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)) :=
    measurePreserving_sumPiEquivProdPi_symm (fun a => laws ⟨j, a⟩)
  have houter := measurePreserving_pi
    (fun j => mixedScalarArrayLaw (c j) (w j) (p j))
    (fun j => Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)) hinner
  have hflat : MeasurePreserving
      (MeasurableEquiv.piCurry (fun j (a : I j ⊕ Fin (n j)) => CoefficientAxisRow K ⟨j, a⟩)).symm
      (Measure.pi (fun j => Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)))
      (Measure.pi laws) :=
    ⟨(MeasurableEquiv.piCurry (fun j (a : I j ⊕ Fin (n j)) => CoefficientAxisRow K ⟨j, a⟩)).symm.measurable,
      sigmaProductMeasure_flatten laws⟩
  exact hflat.comp houter

theorem coefficientAxisSplitEquiv_symm_right
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
    (u : ∀ a : {a // P a}, CoefficientAxisRow K a.val)
    (v : ∀ a : {a // ¬P a}, CoefficientAxisRow K a.val) (a : {a // ¬P a}) :
    coefficientAxisEquiv K I n ((coefficientAxisSplitEquiv K I n P).symm (u, v)) a.val = v a := by
  exact congrArg (fun z => z.2 a) ((coefficientAxisSplitEquiv K I n P).apply_symm_apply (u, v))

theorem coefficientAxisSplitEquiv_measurePreserving [Fintype K] [∀ j, Fintype (I j)]
    (hw : ∀ j i d, 0 < w j i d) (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    MeasurePreserving (coefficientAxisSplitEquiv K I n P)
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j)))
      ((Measure.pi (fun a : {a // P a} => coefficientAxisLaw c w p a.val)).prod
        (Measure.pi (fun a : {a // ¬P a} => coefficientAxisLaw c w p a.val))) := by
  let : ∀ a, IsProbabilityMeasure (coefficientAxisLaw c w p a) := coefficientAxisLaw_probability c w p hw
  exact (measurePreserving_piEquivPiSubtypeProd (coefficientAxisLaw c w p) P).comp
    (coefficientAxisEquiv_measurePreserving c w p hw)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

theorem coefficientJetAxisMap_measurable {K : Type*} [Fintype K] {O : Fin m → Type*}
    [∀ j, Fintype (O j)]
    (A : ∀ j, Matrix (O j) (BoundedCoefficientExponent K (j.val+1)) ℤ)
    (a : LayerSamplerAxis I n) : Measurable (coefficientJetAxisMap A a) := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl i =>
    exact (matrixSupCLM ((A j).map (Int.cast : ℤ → ℝ))).continuous.measurable
  | inr i =>
    change Measurable (fun c : BoundedCoefficientExponent K (j.val+1) → ℤ => A j *ᵥ c)
    exact measurable_of_countable _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.JetAxisCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (O I : Fin m → Type*) (n : Fin m → ℕ)

theorem canonicalCoefficientJetArrays_axis {α K : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (x : CoefficientSamplerArrays (K := K) I n) (a : LayerSamplerAxis I n) :
    coefficientJetAxisEquiv O I n (canonicalCoefficientJetArrays root A rows x) a =
      coefficientJetAxisMap (fun j => boundedCoefficientJetMatrix root A (j.val + 1) (rows j)) a
        (coefficientAxisEquiv K I n x a) := by
  rcases a with ⟨j, i | i⟩ <;> rfl

end Erdos3.VectorPolynomial

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ControlledJointGrid
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_real_integral_count {X : Type*} [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : PMF X) :
    (∫ x, (p x).toReal ∂Measure.count) = 1 := by
  rw [integral_countable (pmf_real_integrable p)]
  simpa only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    using pmf_real_mass p

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem realDensityMeasure_integral_complex {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (φ : X → ℂ) :
    (∫ x, φ x ∂realDensityMeasure μ f) = ∫ x, (f x : ℂ) * φ x ∂μ := by
  unfold realDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _), Complex.real_smul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialAffineLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L^h < K → (principalSamplingGapRatio γ*L)^h ≤ K)
variable (hεL : 8*(probabilityProfileLipschitz : ℝ) ≤ ε*L)
variable (ha : L^h < K) (henormous : L^(s+1) < K)
variable (hconst : 8*(probabilityProfileLipschitz : ℝ) ≤ ρ*K)
variable (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
variable (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (L : ℝ)^h)

local notation "centers" => coefficientProfileCenter P γ
local notation "widths" => coefficientProfileWidth P j₀ ρ γ ε
local notation "scales" => fun j => (K : ℝ)/monomialScale T (e j)
local notation "laws" => integerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
  ρ γ ε hρ hγ hε hgap hεL

include ha henormous hj₀ he₀ hprincipal in
omit [Fintype J] in
theorem integerPolynomialCoordinatePMF_normalized
    (hwidth : ∀ j, 8*(probabilityProfileLipschitz : ℝ) ≤ widths j * ((K : ℝ)/monomialScale T (e j)))
    (j : J) :
    laws j = normalizedIntegerPMF ((K : ℝ)/monomialScale T (e j)) (centers j) (widths j)
      (div_pos (by exact_mod_cast hK) (monomialScale_pos T hT (e j)))
      (coefficientProfileWidth_pos P j₀ hρ hγ hε j) (hwidth j) := by
  classical
  by_cases hj : j = j₀
  · subst j
    have hc : 8*(probabilityProfileLipschitz : ℝ) ≤ ρ*K := by
      simpa only [coefficientProfileWidth, ↓reduceIte, he₀, monomialScale_zero, div_one] using hwidth j₀
    simp only [integerPolynomialCoordinatePMF, ↓reduceIte, coefficientProfileCenter, hj₀,
      coefficientProfileWidth, he₀, monomialScale_zero, div_one]
    exact constantIntegerPMF_large _ _ _ _ hc
  · by_cases hp : j ∈ P
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte,
        integerAxisPrincipalPMF, ha, ↓reduceDIte, coefficientProfileCenter,
        coefficientProfileWidth, hprincipal j hp, principalIntegerPMF]
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte, integerAxisTailPMF,
        henormous, ↓reduceDIte, coefficientProfileCenter, coefficientProfileWidth]
      unfold normalizedIntegerPMF
      have hw : (ε/monomialScale T (e j))*(K : ℝ) = ε*((K : ℝ)/monomialScale T (e j)) := by ring
      simp only [zero_mul, hw]

include ha henormous hj₀ he₀ hprincipal in
theorem integerPolynomial_affinePMF
    (hwidth : ∀ j, 8*(probabilityProfileLipschitz : ℝ) ≤ widths j * ((K : ℝ)/monomialScale T (e j)))
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → affineProductProfile centers widths x = 0)
    (hZ : 0 < coefficientWeightSum (affineProductProfile centers widths) scales) :
    independentProductPMF laws =
      coefficientPMF (affineProductProfile centers widths)
        (affineProductProfile_nonneg centers widths (coefficientProfileWidth_pos P j₀ hρ hγ hε))
        scales (fun j => div_pos (by exact_mod_cast hK) (monomialScale_pos T hT (e j))) hsupport hZ := by
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [independentProductPMF_toReal, affineCoefficientPMF_apply centers widths scales
    (coefficientProfileWidth_pos P j₀ hρ hγ hε)
    (fun j => div_pos (by exact_mod_cast hK) (monomialScale_pos T hT (e j))) hsupport hZ]
  apply Finset.prod_congr rfl
  intro j _
  rw [integerPolynomialCoordinatePMF_normalized P j₀ h K L s hh hK hL T hT hTL e he
    ρ γ ε hρ hγ hε hgap hεL ha henormous hj₀ he₀ hprincipal hwidth j]
  rfl

include ha henormous hj₀ he₀ hprincipal in
theorem integerPolynomial_affineMeasure
    (hwidth : ∀ j, 8*(probabilityProfileLipschitz : ℝ) ≤ widths j * ((K : ℝ)/monomialScale T (e j)))
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → affineProductProfile centers widths x = 0)
    (hZ : 0 < coefficientWeightSum (affineProductProfile centers widths) scales) :
    Measure.pi (fun j => (laws j).toMeasure) =
      (coefficientPMF (affineProductProfile centers widths)
        (affineProductProfile_nonneg centers widths (coefficientProfileWidth_pos P j₀ hρ hγ hε))
        scales (fun j => div_pos (by exact_mod_cast hK) (monomialScale_pos T hT (e j))) hsupport hZ).toMeasure := by
  rw [← integerPolynomial_affinePMF P j₀ h K L s hh hK hL T hT hTL e he
    ρ γ ε hρ hγ hε hgap hεL ha henormous hj₀ he₀ hprincipal hwidth hsupport hZ]
  exact (Measure.toPMF_toMeasure _).symm

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

theorem partitionedPrincipalInput_value (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z) (z : Z → ℤ) {L : PrincipalTupleIndex B h → ℕ}
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L)
    (k : SamplerTupleIndex G B h) (a : Option α) :
    Sum.elim (Sum.elim z (principalTupleIntegers u)) (principalTupleIntegers v)
        (partitionedPrincipalInput P extra k a) =
      Sum.elim z (principalTupleIntegers (principalAxisJoin P u v)) (canonicalTupleInput extra k a) := by
  rcases k with g | ⟨d, b, r⟩
  · rfl
  · by_cases hp : P d <;>
      simp [partitionedPrincipalInput, canonicalTupleInput, principalTupleIntegers, principalAxisJoin, hp]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

theorem allocatedCoefficientAxisLaw_probability (a : LayerSamplerAxis I n) :
    IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a) :=
  coefficientAxisLaw_probability _ _ _ (allocatedLayerWidths_pos B U basis hR hσ S) a

theorem allocatedFrozenCoefficientSource_probability :
    IsProbabilityMeasure (allocatedFrozenCoefficientSource B U basis hR hσ S) := by
  let : ∀ a, IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a) :=
    allocatedCoefficientAxisLaw_probability B U basis hR hσ S
  exact Measure.pi.instIsProbabilityMeasure _

theorem allocatedLongCoefficientSource_probability :
    IsProbabilityMeasure (allocatedLongCoefficientSource B U basis hR hσ S) := by
  let : ∀ a, IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a) :=
    allocatedCoefficientAxisLaw_probability B U basis hR hσ S
  exact Measure.pi.instIsProbabilityMeasure _

theorem allocatedCoefficientSplit_measurePreserving :
    MeasurePreserving (allocatedCoefficientSplit B U basis S)
      (allocatedCoefficientSource B U basis hR hσ S)
      ((allocatedFrozenCoefficientSource B U basis hR hσ S).prod
        (allocatedLongCoefficientSource B U basis hR hσ S)) :=
  coefficientAxisSplitEquiv_measurePreserving _ _ _
    (allocatedLayerWidths_pos B U basis hR hσ S) grid

theorem allocatedCoefficientReconstruct_measurePreserving :
    MeasurePreserving (allocatedCoefficientSplit B U basis S).symm
      ((allocatedFrozenCoefficientSource B U basis hR hσ S).prod
        (allocatedLongCoefficientSource B U basis hR hσ S))
      (allocatedCoefficientSource B U basis hR hσ S) :=
  (allocatedCoefficientSplit_measurePreserving B U basis hR hσ S).symm
    (allocatedCoefficientSplit B U basis S)

theorem allocatedCoefficientReconstruct_long
    (u : AllocatedFrozenCoefficients B U basis S) (v : AllocatedLongCoefficients B U basis S)
    (a : {a // ¬grid a}) :
    coefficientAxisEquiv vars I n ((allocatedCoefficientSplit B U basis S).symm (u, v)) a.val = v a :=
  coefficientAxisSplitEquiv_symm_right grid u v a

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

theorem allocatedEnormous_coefficient_law :
    allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inr i⟩ =
      (allocatedEnormousProfilePMF B U basis hR hσ S j i hσ1 henormous).toMeasure := by
  exact integerPolynomial_affineMeasure
    (P := layerIntegerPrincipalSlots B j i) (j₀ := constantCoefficientSlot _ _)
    (h := j.val+1) (K := basisAxisScale (basis j) i) (L := S.value) (s := layerTailDegree m)
    (hh := Nat.zero_lt_succ _) (hK := basisAxisScale_pos (basis j) i) (hL := S.positive)
    (T := layerSamplerBox B U basis S)
    (hT := fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
    (hTL := layerSamplerBox_le B U basis S) (e := Subtype.val)
    (he := fun d => d.property.trans (layerDegree_le_tailDegree j))
    (ρ := R j/4) (γ := principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (ε := tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))
    (hρ := div_pos (hR j) (by norm_num)) (hγ := principalProfileSize_pos (hR j) _)
    (hε := tailProfileSize_pos (hR j) (hσ j) _)
    (hgap := S.gap j i) (hεL := S.width j)
    (ha := allocatedEnormous_active B U basis S j i henormous) (henormous := henormous)
    (hj₀ := layerIntegerPrincipalSlots_not_constant B j i) (he₀ := rfl)
    (hprincipal := allocatedEnormous_principalScale B U basis S j i henormous)
    (hwidth := allocatedEnormous_profile_width_large B U basis hR hσ S j i hσ1 henormous)
    (hsupport := allocatedIntegerProfile_support B hR hσ j i hσ1)
    (hZ := allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous)

theorem allocatedEnormous_image_law {O : Type*} [Fintype O]
    (A : Matrix O (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) ℤ) :
    (allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inr i⟩).map (fun a => A *ᵥ a) =
      (coefficientImagePMF A (affineProductProfile (allocatedIntegerProfileCenters B R j i)
        (allocatedIntegerProfileWidths B R σ j i))
        (affineProductProfile_nonneg _ _ (allocatedIntegerProfileWidths_pos B hR hσ j i))
        (allocatedIntegerProfileScales B U basis S j i) (allocatedIntegerProfileScales_pos B U basis S j i)
        (allocatedIntegerProfile_support B hR hσ j i hσ1)
        (allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous)).toMeasure := by
  rw [allocatedEnormous_coefficient_law B U basis hR hσ S j i hσ1 henormous]
  have hlaw := PMF.toMeasure_map
    (fun a : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℤ => A *ᵥ a)
    (allocatedEnormousProfilePMF B U basis hR hσ S j i hσ1 henormous) (measurable_of_countable _)
  exact hlaw

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

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

theorem allocatedIntegerKernelPMF_law [∀ j, Fintype (O j)]
    (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
    (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i) :
    (allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inr i⟩).map
      (fun a => allocatedPartitionedJetMatrix B U basis S x u v rows j *ᵥ a) =
      (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i hσ1 henormous).toMeasure :=
  allocatedEnormous_image_law B U basis hR hσ S j i hσ1 henormous
    (allocatedPartitionedJetMatrix B U basis S x u v rows j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedLongJetMixture
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

omit [Fintype α] [∀ j, DecidableEq (O j)] in
theorem allocatedLongJetMap_measurable : Measurable (allocatedLongJetMap B U basis S x u v rows) :=
  measurable_pi_iff.mpr (fun a =>
    (coefficientJetAxisMap_measurable (allocatedPartitionedJetMatrix B U basis S x u v rows) a.val).comp
      (measurable_pi_apply a))

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

theorem allocatedLongJetFactor_law (a : {a // ¬grid a}) :
    (allocatedCoefficientAxisLaw B U basis hR hσ S a.val).map
      (coefficientJetAxisMap (allocatedPartitionedJetMatrix B U basis S x u v rows) a.val) =
      realDensityMeasure (coefficientJetAxisReference O a.val)
        (allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a) := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    exact allocatedContinuousKernel_image_law_s2 B U basis hR hσ S j i x u
      (rows j) (s j) (hA j) (hσ1 j) v
  | inr i =>
    change (allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inr i⟩).map
      (fun c => allocatedPartitionedJetMatrix B U basis S x u v rows j *ᵥ c) =
      realDensityMeasure Measure.count (fun z =>
        (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) (Nat.lt_of_not_ge ha) z).toReal)
    rw [← pmf_realDensity_count]
    exact allocatedIntegerKernelPMF_law B U basis hR hσ S x u v rows j i (hσ1 j) (Nat.lt_of_not_ge ha)

theorem allocatedLongJetFactor_measurable (a : {a // ¬grid a}) :
    Measurable (allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a) := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    change Measurable (allocatedContinuousKernelDensity B U basis S j i x u
      (rows j) (s j) (hA j) (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v))
    exact (allocatedContinuousKernelDensity_measurable B U basis hR hσ S j i x u
      (rows j) (s j) (hA j) (hσ1 j)).of_uncurry_left
  | inr i =>
    change Measurable (fun z : O j → ℤ =>
      (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) (Nat.lt_of_not_ge ha) z).toReal)
    exact measurable_of_countable _

theorem allocatedLongJetFactor_probability_data (a : {a // ¬grid a}) :
    (∀ z, 0 ≤ allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a z) ∧
      Integrable (allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a)
        (coefficientJetAxisReference O a.val) ∧
      (∫ z, allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a z
        ∂coefficientJetAxisReference O a.val) = 1 := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    exact allocatedContinuousKernelDensity_probability_data B U basis hR hσ S j i x u
      (rows j) (s j) (hA j) (hσ1 j)
      (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
  | inr i =>
    let p := allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) (Nat.lt_of_not_ge ha)
    change (∀ z, 0 ≤ (p z).toReal) ∧ Integrable (fun z => (p z).toReal) Measure.count ∧
      (∫ z, (p z).toReal ∂Measure.count) = 1
    exact ⟨fun _ => ENNReal.toReal_nonneg, pmf_real_integrable p, pmf_real_integral_count p⟩

theorem allocatedLongJetDensity_measurable :
    Measurable (allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1) :=
  Finset.measurable_prod _ (fun a _ =>
    (allocatedLongJetFactor_measurable B U basis hR hσ S x u v rows s hA hσ1 a).comp (measurable_pi_apply a))

theorem allocatedLongJetDensity_probability_data :
    (∀ z, 0 ≤ allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) ∧
      Integrable (allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1)
        (allocatedLongJetReference B U basis S O) ∧
      (∫ z, allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z
        ∂allocatedLongJetReference B U basis S O) = 1 := by
  have hp := allocatedLongJetFactor_probability_data B U basis hR hσ S x u v rows s hA hσ1
  refine ⟨fun z => Finset.prod_nonneg (fun a _ => (hp a).1 (z a)),
    Integrable.fintype_prod_dep (fun a => (hp a).2.1), ?_⟩
  change (∫ z, (∏ a, allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a (z a))
    ∂Measure.pi (fun a : {a // ¬grid a} => coefficientJetAxisReference O a.val)) = 1
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_eq_one (fun a _ => (hp a).2.2)

theorem allocatedLongJetDensity_law :
    (allocatedLongCoefficientSource B U basis hR hσ S).map
      (allocatedLongJetMap B U basis S x u v rows) =
      realDensityMeasure (allocatedLongJetReference B U basis S O)
        (allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1) := by
  let : ∀ a : {a // ¬grid a}, IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a.val) :=
    fun a => allocatedCoefficientAxisLaw_probability B U basis hR hσ S a.val
  unfold allocatedLongCoefficientSource allocatedLongJetMap
  rw [Measure.pi_map_pi (fun a =>
    (coefficientJetAxisMap_measurable (allocatedPartitionedJetMatrix B U basis S x u v rows) a.val).aemeasurable)]
  simp_rw [allocatedLongJetFactor_law B U basis hR hσ S x u v rows s hA hσ1]
  exact realDensityMeasure_pi (fun a : {a // ¬grid a} => coefficientJetAxisReference O a.val) _
    (fun a => (allocatedLongJetFactor_probability_data B U basis hR hσ S x u v rows s hA hσ1 a).2.1)
    (fun a => (allocatedLongJetFactor_probability_data B U basis hR hσ S x u v rows s hA hσ1 a).1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

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
variable (rows : ∀ j, O j → Finset α) (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "source" => allocatedLongCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S O

theorem allocatedLongJet_test_integral
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (φ : AllocatedLongJetRows B U basis S O → ℂ) (hφ : Measurable φ) :
    (∫ c, φ (allocatedLongJetMap B U basis S x u v rows c) ∂source) =
      ∫ z, (allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z : ℂ) * φ z ∂reference := by
  rw [← integral_map (allocatedLongJetMap_measurable B U basis S x u v rows).aemeasurable hφ.aestronglyMeasurable,
    allocatedLongJetDensity_law B U basis hR hσ S x u v rows s hA hσ1,
    realDensityMeasure_integral_complex _ _
      (allocatedLongJetDensity_measurable B U basis hR hσ S x u v rows s hA hσ1)
      (allocatedLongJetDensity_probability_data B U basis hR hσ S x u v rows s hA hσ1).1]

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

theorem allocatedLongJet_variable_test_mean
    (w : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (φ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides → AllocatedLongJetRows B U basis S O → ℂ)
    (hφ : ∀ v, Measurable (φ v)) {C : ℝ} (hbound : ∀ v z, ‖φ v z‖ ≤ C) :
    (∫ c, w.complexMean (fun v => φ v (allocatedLongJetMap B U basis S x u v rows c)) ∂source) =
      ∫ z, w.complexMean (fun v =>
        (allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z : ℂ) * φ v z) ∂reference := by
  let : IsProbabilityMeasure source := allocatedLongCoefficientSource_probability B U basis hR hσ S
  have hi (v) : Integrable (fun c => φ v (allocatedLongJetMap B U basis S x u v rows c)) source :=
    (integrable_const C).mono'
      ((hφ v).comp (allocatedLongJetMap_measurable B U basis S x u v rows)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun c => hbound v _))
  rw [w.integral_complexMean _ _ hi]
  simp_rw [allocatedLongJet_test_integral B U basis hR hσ S x u rows s hA hσ1 _ _ (hφ _)]
  symm
  apply w.integral_complexMean
  intro v
  exact (allocatedLongJetDensity_probability_data B U basis hR hσ S x u v rows s hA hσ1).2.1.ofReal.mul_bdd
    (hφ v).aestronglyMeasurable (Filter.Eventually.of_forall (hbound v))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongImage
namespace OAI

section

namespace Erdos3

theorem translatedIntegerMappedJetMatrix_zero {Z X K α O N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℤ)
    (rows : O → Finset α) (x : X → ℤ) :
    translatedIntegerMappedJetMatrix e input z rows x (fun _ => 0) =
      integerMappedJetMatrix e input z rows x := by
  simp only [translatedIntegerMappedJetMatrix, zero_add, integerMappedJetMatrix]

theorem translatedIntegerMappedJetMatrix_eq_boundedCoefficient {Z X K α O : Type*}
    [DecidableEq α] [Fintype K] (h : ℕ) (input : K → Option α → Z ⊕ X)
    (z : Z → ℤ) (rows : O → Finset α) (x : X → ℤ) (c : K → ℤ) :
    translatedIntegerMappedJetMatrix (fun e : VectorPolynomial.BoundedCoefficientExponent K h => e.val)
      input z rows x c =
      boundedCoefficientJetMatrix (fun k => c k + Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i))) h rows := by
  have hv : (fun t k => c k + integerMappedCubeTuple input z x t k) =
      integerAffineCube (fun k => c k + Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i))) := by
    funext t k
    simp only [integerMappedCubeTuple, integerAffineCube, add_assoc]
  change integerJetMatrix
      (fun e : VectorPolynomial.BoundedCoefficientExponent K h => MvPolynomial.monomial e.val 1)
      (fun t k => c k + integerMappedCubeTuple input z x t k) rows =
    integerJetMatrix
      (fun e : VectorPolynomial.BoundedCoefficientExponent K h => MvPolynomial.monomial e.val 1)
      (integerAffineCube (fun k => c k + Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i)))) rows
  rw [hv]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

omit [DecidableEq α] in
theorem allocatedPhysicalCube_mapped_root (c : LayerSamplerVariables G I n B → ℤ) :
    (fun k => c k + Sum.elim (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (principalTupleIntegers v) ((partitionedPrincipalInput grid (fun g a => (g, a))) k none)) =
      allocatedPhysicalCubeRoot B U b S c x (principalAxisJoin grid u v) := by
  funext k
  rw [partitionedPrincipalInput_value]
  cases k <;> rfl

omit [DecidableEq α] in
theorem allocatedPhysicalCube_mapped_directions :
    (fun i k => Sum.elim (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (principalTupleIntegers v) ((partitionedPrincipalInput grid (fun g a => (g, a))) k (some i))) = (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) := by
  funext i k
  rw [partitionedPrincipalInput_value]
  cases k <;> rfl

theorem allocatedTranslatedPartitionedJetMatrix_eq_physical
    (c : LayerSamplerVariables G I n B → ℤ) (j : Fin m) :
    allocatedTranslatedPartitionedJetMatrix B U b S x u v rows c j =
      boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S c x (principalAxisJoin grid u v)) (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) (j.val + 1) (rows j) := by
  unfold allocatedTranslatedPartitionedJetMatrix
  rw [translatedIntegerMappedJetMatrix_eq_boundedCoefficient,
    allocatedPhysicalCube_mapped_root, allocatedPhysicalCube_mapped_directions]

theorem allocatedPartitionedJetMatrix_eq_physical (j : Fin m) :
    allocatedPartitionedJetMatrix B U b S x u v rows j =
      boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) (j.val + 1) (rows j) := by
  rw [← allocatedTranslatedPartitionedJetMatrix_eq_physical B U b S x u v rows (fun _ => 0) j]
  exact (translatedIntegerMappedJetMatrix_zero _ (partitionedPrincipalInput grid (fun g a => (g, a))) (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (rows j) (principalTupleIntegers v)).symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "split" => allocatedCoefficientSplit B U b S
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "longSource" => allocatedLongCoefficientSource B U b hR hσ S

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "joined" => principalAxisJoin grid u v
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x joined
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x joined

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedPhysicalLongJetMap_reconstruct
    (a₀ : AllocatedFrozenCoefficients B U b S) (a₁ : AllocatedLongCoefficients B U b S) :
    allocatedPhysicalLongJetMap B U b S x u v rows ((split).symm (a₀, a₁)) =
      allocatedLongJetMap B U b S x u v rows a₁ := by
  have hmatrix : (fun j => boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)) =
      allocatedPartitionedJetMatrix B U b S x u v rows :=
    funext (fun j => (allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j).symm)
  funext i
  change coefficientJetAxisEquiv O I n (canonicalCoefficientJetArrays root dirs rows _) i.val = _
  rw [canonicalCoefficientJetArrays_axis, hmatrix, allocatedCoefficientReconstruct_long]
  rfl

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedPhysicalLongJetMap_split
    (a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    allocatedPhysicalLongJetMap B U b S x u v rows a =
      allocatedLongJetMap B U b S x u v rows (split a).2 := by
  simpa only [Prod.mk.eta, MeasurableEquiv.symm_apply_apply] using
    allocatedPhysicalLongJetMap_reconstruct B U b S x u v rows (split a).1 (split a).2

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

theorem allocatedPhysicalLongJet_variable_test_mean_s2_oai
    (w : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (φ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides →
      AllocatedFrozenCoefficients B U b S → AllocatedLongJetRows B U b S O → ℂ)
    (hφ : ∀ v, Measurable (fun p : AllocatedFrozenCoefficients B U b S × AllocatedLongJetRows B U b S O =>
      φ v p.1 p.2)) {C : ℝ} (hbound : ∀ v a z, ‖φ v a z‖ ≤ C) :
    (∫ a, w.complexMean (fun v => φ v (split a).1
      (allocatedPhysicalLongJetMap B U b S x u v rows a)) ∂source) =
      ∫ a₀, ∫ z, w.complexMean (fun v =>
        (allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z : ℂ) * φ v a₀ z)
        ∂allocatedLongJetReference B U b S O ∂frozenSource := by
  classical
  let : IsProbabilityMeasure frozenSource := allocatedFrozenCoefficientSource_probability B U b hR hσ S
  let : IsProbabilityMeasure longSource := allocatedLongCoefficientSource_probability B U b hR hσ S
  have hi : Integrable (fun a : AllocatedFrozenCoefficients B U b S × AllocatedLongCoefficients B U b S =>
      w.complexMean (fun v => φ v a.1 (allocatedLongJetMap B U b S x u v rows a.2)))
      ((frozenSource).prod longSource) := by
    apply w.complexMean_integrable
    intro v
    exact (integrable_const C).mono'
      ((hφ v).comp (measurable_fst.prodMk
        ((allocatedLongJetMap_measurable B U b S x u v rows).comp measurable_snd))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun a => hbound v a.1 _))
  calc
    _ = ∫ a, w.complexMean (fun v => φ v (split ((split).symm a)).1
        (allocatedPhysicalLongJetMap B U b S x u v rows ((split).symm a))) ∂((frozenSource).prod longSource) :=
      (allocatedCoefficientReconstruct_measurePreserving B U b hR hσ S).integral_comp' _ |>.symm
    _ = ∫ a₀, ∫ a₁, w.complexMean (fun v => φ v a₀
        (allocatedLongJetMap B U b S x u v rows a₁)) ∂longSource ∂frozenSource := by
      simp only [allocatedPhysicalLongJetMap_split, MeasurableEquiv.apply_symm_apply]
      exact integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a₀
      exact allocatedLongJet_variable_test_mean B U b hR hσ S x u rows s hA hσ1 w
        (fun v => φ v a₀) (fun v => (hφ v).comp (measurable_const.prodMk measurable_id))
        (fun v z => hbound v a₀ z)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedPhysicalLongJet_variable_test_mean_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedPhysicalLongJet_variable_test_mean_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
