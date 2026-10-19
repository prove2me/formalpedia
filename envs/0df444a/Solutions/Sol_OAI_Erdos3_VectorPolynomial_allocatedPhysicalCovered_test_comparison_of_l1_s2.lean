-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedPhysicalCovered_test_comparison_of_l1_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:31:46.98937+00:00
-- url     : https://prove2.me/submissions/be4aae03-3350-424a-bf31-43b2c9723879

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedPhysicalMixedDeck_test_mean_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem mixedArrayRegroup_apply {I Z J : Type*} (x : (I → J → ℝ) × (Z → J → ℤ)) (j : J) :
    mixedArrayRegroup I Z J x j = (fun i => x.1 i j, fun z => x.2 z j) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem orthonormalMixedChart_sum_zsmul (o : OrthonormalBasis I ℝ W)
    {S : Type*} (s : Finset S) (a : S → ℤ)
    (x : S → (I → ℝ) × (Fin n → ℤ)) :
    orthonormalMixedChart o (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • orthonormalMixedChart o (x i) := by
  change orthonormalMixedChartHom W o _ = _
  simp only [map_sum, map_zsmul, orthonormalMixedChartHom, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedArrayIntegerImage
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

variable {D I J O Z : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}

omit [Fintype I] in
theorem mixedArrayIntegerImage_regroup (A : Matrix O J ℤ)
    (x : (I → J → ℝ) × (Z → J → ℤ)) (r : O) :
    mixedArrayRegroup I Z O (mixedArrayIntegerImage A x) r =
      ∑ j, A r j • mixedArrayRegroup I Z J x j := by
  apply Prod.ext
  · funext i
    simp only [mixedArrayIntegerImage, mixedArrayRegroup_apply, Prod.fst_sum,
      Finset.sum_apply]
    change (∑ j, (A r j : ℝ) * x.1 i j) = ∑ j, A r j • x.1 i j
    exact Finset.sum_congr rfl (fun j _ => Int.cast_smul_eq_zsmul ℝ (A r j) (x.1 i j))
  · funext z
    simp only [mixedArrayIntegerImage, mixedArrayRegroup_apply, Prod.snd_sum,
      Finset.sum_apply]
    change (∑ j, A r j * x.2 z j) = ∑ j, A r j • x.2 z j
    simp only [smul_eq_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientDeckImageCongruence
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

theorem coefficientDeckKernel_jets (d : ℕ) (hd : 0 < d)
    (r : CoefficientDeckResidues (K := K) B d) (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root D rows (coefficientDeckKernelEquiv U bW d hd r).val j t =
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (coefficientDeckJetMap root D rows d r j t)).val := by
  rw [euclideanCoefficientJetMap_apply]
  simp_rw [coefficientDeckKernelEquiv_coordinate]
  let f := ((quotientIntegerCover
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup d).ker.subtype).comp
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd).toAddMonoidHom
  change (∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e • f (r j e)) =
    f (∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e • r j e)
  simp only [map_sum, map_zsmul]

variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem canonicalCoefficientDeckSample_jets (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d)
    (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root D rows (canonicalCoefficientDeckSample U bW b hb o d hd x r) j t =
      euclideanCoefficientJetMap U root D rows (canonicalCoefficientCoverLift U b hb o d x) j t +
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (coefficientDeckJetMap root D rows d r j t)).val := by
  simp only [canonicalCoefficientDeckSample, map_add, Pi.add_apply,
    coefficientDeckKernel_jets]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredMixedArrayImage
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

theorem normalizedLatticeRepresentative_sum_zsmul {S : Type*} (s : Finset S)
    (a : S → ℤ) (x : S → W × (Fin n → ℤ)) :
    normalizedLatticeRepresentative W b hb (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • normalizedLatticeRepresentative W b hb (x i) := by
  change normalizedLatticeRepresentativeHom W b hb _ = _
  simp only [map_sum, map_zsmul, normalizedLatticeRepresentativeHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]

theorem normalizedCoverLift_sum_zsmul (d : ℕ) {S : Type*} (s : Finset S)
    (a : S → ℤ) (x : S → W × (Fin n → ℤ)) :
    normalizedCoverLift W b hb d (∑ i ∈ s, a i • x i) =
      ∑ i ∈ s, a i • normalizedCoverLift W b hb d (x i) := by
  have he (i) : (d : ℝ)⁻¹ • (a i • normalizedLatticeRepresentative W b hb (x i)) =
      a i • ((d : ℝ)⁻¹ • normalizedLatticeRepresentative W b hb (x i)) := smul_comm _ _ _
  simp only [normalizedCoverLift, normalizedLatticeRepresentative_sum_zsmul,
    Finset.smul_sum, he]
  change QuotientAddGroup.mk' _ (∑ i ∈ s, a i • ((d : ℝ)⁻¹ •
    normalizedLatticeRepresentative W b hb (x i))) = _
  simp only [map_sum, map_zsmul]
  rfl

namespace VectorPolynomial

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable {ns : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bs : ∀ j, Basis (Fin (ns j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hbs : ∀ j, span ℤ (Set.range (bs j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

theorem canonicalCoefficientCoverLift_jets (d : ℕ)
    (x : CoefficientSamplerArrays (K := K) I ns) (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root A rows (canonicalCoefficientCoverLift U bs hbs o d x) j t =
      normalizedCoverLift (euclideanSubspace (U j)) (bs j) (hbs j) d
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _
          (canonicalCoefficientJetArrays root A rows x j) t)) := by
  rw [euclideanCoefficientJetMap_apply]
  simp only [canonicalCoefficientCoverLift, AddEquiv.apply_symm_apply]
  rw [canonicalCoefficientJetArrays, mixedArrayIntegerImage_regroup,
    orthonormalMixedChart_sum_zsmul, normalizedCoverLift_sum_zsmul]

theorem canonicalCoefficientDeckSample_mixed_jets
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (bW : ∀ j, Basis (B j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) (hd : 0 < d) (x : CoefficientSamplerArrays (K := K) I ns)
    (r : CoefficientDeckResidues (K := K) B d) (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root A rows
        (canonicalCoefficientDeckSample U bW bs hbs o d hd x r) j t =
      normalizedCoverLift (euclideanSubspace (U j)) (bs j) (hbs j) d
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _
          (canonicalCoefficientJetArrays root A rows x j) t)) +
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (coefficientDeckJetMap root A rows d r j t)).val := by
  rw [canonicalCoefficientDeckSample_jets, canonicalCoefficientCoverLift_jets]

end VectorPolynomial

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

theorem integrable_snd_probability {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) [IsProbabilityMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (f : X → ℝ) (hf : Integrable f ν) :
    Integrable (fun x : Z × X => f x.2) (μ.prod ν) := by
  simpa only [one_mul] using
    (integrable_const (1 : ℝ) : Integrable (fun _ : Z => (1 : ℝ)) μ).mul_prod hf

theorem integral_snd_probability {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) [IsProbabilityMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (f : X → ℝ) (hf : Integrable f ν) :
    (∫ x : Z × X, f x.2 ∂μ.prod ν) = ∫ x, f x ∂ν := by
  rw [integral_prod _ (integrable_snd_probability μ ν f hf)]
  simp

end Erdos3

end

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

theorem density_bounded_complex_test_error {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (φ : X → ℂ) (hφ : Measurable φ) {B : ℝ} (hb : ∀ x, ‖φ x‖ ≤ B) :
    ‖(∫ x, (f x : ℂ) * φ x ∂μ) - ∫ x, (g x : ℂ) * φ x ∂μ‖ ≤
      B * ∫ x, |f x - g x| ∂μ := by
  have hfi : Integrable (fun x => (f x : ℂ) * φ x) μ :=
    hf.ofReal.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hgi : Integrable (fun x => (g x : ℂ) * φ x) μ :=
    hg.ofReal.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  rw [← integral_sub hfi hgi]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    _ ≤ ∫ x, B * |f x - g x| ∂μ := by
      apply integral_mono (hfi.sub hgi).norm ((hf.sub hg).abs.const_mul B)
      intro x
      change ‖(f x : ℂ) * φ x - (g x : ℂ) * φ x‖ ≤ B * |f x - g x|
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simpa only [mul_comm B] using mul_le_mul_of_nonneg_left (hb x) (abs_nonneg (f x - g x))
    _ = _ := integral_const_mul _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoveredChart
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

theorem normalizedCoveredChart_continuous :
    Continuous (normalizedCoveredChart W b hb bW d) := by
  have hk : Continuous (fun r : R → ZMod d =>
      (coverKernelBasisEquiv (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
        bW d (Nat.pos_of_ne_zero (NeZero.ne d)) r).val) := continuous_of_discreteTopology
  exact ((normalizedCoverLift_continuous W b hb d).comp continuous_fst).add
    (hk.comp continuous_snd)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoveredJetChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J B : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem coveredJetChart_continuous : Continuous (coveredJetChart (O := O) U b hb bW d) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro t
  exact (normalizedCoveredChart_continuous _ (b j) (hb j) (bW j) d).comp
    ((continuous_apply t).comp (continuous_apply j))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CoveredJetSampler
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical Matrix

namespace VectorPolynomial

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem mixedCoveredJetCoordinates_measurable (d : ℕ) :
    Measurable (mixedCoveredJetCoordinates (O := O) (B := B) (n := n) U o d) := by
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro t
  exact ((orthonormalMixedChart (o j)).measurable.comp
    (((measurable_pi_apply t).comp (mixedArrayRegroup _ _ _).measurable).comp
      ((measurable_pi_apply j).comp measurable_fst))).prodMk
    ((measurable_pi_apply t).comp ((measurable_pi_apply j).comp measurable_snd))

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

variable [∀ j, Fintype (B j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem canonicalCoefficientDeckSample_chart (d : ℕ) [NeZero d]
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d) :
    euclideanCoefficientJetMap U root A rows
      (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) x r) =
    coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d
      (canonicalCoefficientJetArrays root A rows x, coefficientDeckJetMap root A rows d r)) := by
  funext j t
  exact canonicalCoefficientDeckSample_mixed_jets U b hb o root A rows bW d
    (Nat.pos_of_ne_zero (NeZero.ne d)) x r j t

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedCoefficientAxisLaw_probability (a : LayerSamplerAxis I n) :
    IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a) :=
  coefficientAxisLaw_probability _ _ _ (allocatedLayerWidths_pos B U basis hR hσ S) a

theorem allocatedFrozenCoefficientSource_probability :
    IsProbabilityMeasure (allocatedFrozenCoefficientSource B U basis hR hσ S) := by
  let : ∀ a, IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a) :=
    allocatedCoefficientAxisLaw_probability B U basis hR hσ S
  exact Measure.pi.instIsProbabilityMeasure _

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

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

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

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFrozenGridLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v w : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

theorem allocatedFrozenJetMap_measurable [∀ j, Fintype (O j)] :
    Measurable (allocatedFrozenJetMap B U b S x u v rows) :=
  measurable_pi_iff.mpr (fun i =>
    (coefficientJetAxisMap_measurable (allocatedPartitionedJetMatrix B U b S x u v rows) i.val).comp
      (measurable_pi_apply i))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoveredFixedTest
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem finitePMF_integral_measurable {X T : Type*} [MeasurableSpace X]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (p : PMF T) (f : X → T → ℂ) (hf : ∀ t, Measurable (fun x => f x t)) :
    Measurable (fun x => ∫ t, f x t ∂p.toMeasure) := by
  simp only [PMF.integral_eq_sum, Complex.real_smul]
  exact Finset.measurable_sum _ (fun t _ => (hf t).const_mul ((p t).toReal : ℂ))

theorem finitePMF_integral_norm_le {T : Type*} [MeasurableSpace T]
    (p : PMF T) (f : T → ℂ) {C : ℝ} (hf : ∀ t, ‖f t‖ ≤ C) :
    ‖∫ t, f t ∂p.toMeasure‖ ≤ C := by
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (ae_of_all p.toMeasure hf)

end Erdos3

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
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v w : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "axis" => coefficientJetAxisEquiv O I n
local notation "join" => MeasurableEquiv.piEquivPiSubtypeProd (CoefficientJetAxisRow O) grid

theorem allocatedMixedJetReconstruct_measurable [∀ j, Fintype (O j)] :
    Measurable (fun p : AllocatedFrozenCoefficients B U b S × AllocatedLongJetRows B U b S O =>
      allocatedMixedJetReconstruct B U b S x u w rows p.1 p.2) :=
  (axis).symm.measurable.comp ((join).symm.measurable.comp
    (((allocatedFrozenJetMap_measurable B U b S x u w rows).comp measurable_fst).prodMk measurable_snd))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

variable (φ : (AllocatedFrozenCoefficients B U b S ×
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))) × (∀ j, O j → Q j → ZMod d) → ℂ)

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedDeckMixedTest_measurable (hφ : Measurable φ) :
    Measurable (fun p : AllocatedFrozenCoefficients B U b S ×
      (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) =>
        allocatedDeckMixedTest B U b S x u v₀ rows Q d φ p.1 p.2) :=
  finitePMF_integral_measurable deck _ (fun _ => hφ.comp (measurable_id.prodMk measurable_const))

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedDeckMixedTest_norm_le {C : ℝ} (hφ : ∀ p, ‖φ p‖ ≤ C)
    (a₀ : AllocatedFrozenCoefficients B U b S)
    (t : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    ‖allocatedDeckMixedTest B U b S x u v₀ rows Q d φ a₀ t‖ ≤ C :=
  finitePMF_integral_norm_le deck _ (fun _ => hφ _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "split" => allocatedCoefficientSplit B U b S
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "pullback" => (fun p : (AllocatedFrozenCoefficients B U b S ×
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))) × (∀ j, O j → Q j → ZMod d) =>
  F (Prod.fst (Prod.fst p), coveredJetChart U b hb bW d
    (mixedCoveredJetCoordinates U o d (Prod.snd (Prod.fst p), Prod.snd p))))

omit [Fintype α] [DecidableEq α] [∀ j, DecidableEq (O j)] in
theorem allocatedCoveredPullback_measurable (hF : Measurable F) : Measurable pullback := by
  have hchart := (coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
    (mixedCoveredJetCoordinates_measurable (O := O) (B := Q) (n := n) U o d)
  exact hF.comp ((measurable_fst.comp measurable_fst).prodMk
    (hchart.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))

omit [Fintype α] [∀ j, DecidableEq (O j)] in
theorem allocatedCoveredFixedTest_measurable (hF : Measurable F) :
    Measurable (fun p : AllocatedFrozenCoefficients B U b S × AllocatedLongJetRows B U b S O =>
      allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F p.1 p.2) :=
  (allocatedDeckMixedTest_measurable B U b S x u v₀ rows Q d pullback
    (allocatedCoveredPullback_measurable B U b S Q hb o bW d F hF)).comp
      (measurable_fst.prodMk (allocatedMixedJetReconstruct_measurable B U b S x u v₀ rows))

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedCoveredFixedTest_norm_le {C : ℝ} (hF : ∀ p, ‖F p‖ ≤ C)
    (a₀ : AllocatedFrozenCoefficients B U b S) (z : AllocatedLongJetRows B U b S O) :
    ‖allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F a₀ z‖ ≤ C :=
  allocatedDeckMixedTest_norm_le B U b S x u v₀ rows Q d pullback (fun _ => hF _) a₀ _

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

theorem allocatedPhysicalCovered_test_mean
    (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (M : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hresidue : ∀ v, weights.weight v ≠ 0 → principalResidueLabel M v = principalResidueLabel M v₀)
    (hF : Measurable F) {C : ℝ} (hbound : ∀ p, ‖F p‖ ≤ C) :
    (∫ p, weights.complexMean (fun v => F ((split p.1).1,
      euclideanCoefficientJetMap U (root v) (dirs v) rows
        (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
        ∂(source).prod (deck).toMeasure) =
      ∫ a₀, ∫ z,
        (weights.mean (fun v => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) : ℂ) *
          allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F a₀ z ∂reference ∂frozenSource := by
  have he := allocatedPhysicalMixedDeck_test_mean_s2 B U b hR hσ S x u v₀ rows Q d pullback
    s hA hσ1 weights M hperiod hresidue
    (allocatedCoveredPullback_measurable B U b S Q hb o bW d F hF) (fun p => hbound _)
  calc
    _ = ∫ p, weights.complexMean (fun v =>
        pullback (((split p.1).1, canonicalCoefficientJetArrays (root v) (dirs v) rows p.1),
          coefficientDeckJetMap (root v) (dirs v) rows d p.2)) ∂(source).prod (deck).toMeasure := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro p
      apply congrArg weights.complexMean
      funext v
      rw [canonicalCoefficientDeckSample_chart U o (root v) (dirs v) rows b hb bW d]
    _ = _ := he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RetainedDensityNestedTest
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem retained_density_nested_test_error {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) [IsProbabilityMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (f g : X → ℝ) (hf : Integrable f ν) (hg : Integrable g ν)
    (φ : Z × X → ℂ) (hφ : Measurable φ) {B : ℝ} (hb : ∀ p, ‖φ p‖ ≤ B) :
    ‖(∫ z, ∫ x, (f x : ℂ) * φ (z, x) ∂ν ∂μ) -
      ∫ z, ∫ x, (g x : ℂ) * φ (z, x) ∂ν ∂μ‖ ≤ B * ∫ x, |f x - g x| ∂ν := by
  have hfi := integrable_snd_probability μ ν f hf
  have hgi := integrable_snd_probability μ ν g hg
  have hF : Integrable (fun p : Z × X => (f p.2 : ℂ) * φ p) (μ.prod ν) :=
    hfi.ofReal.mul_bdd hφ.aestronglyMeasurable (ae_of_all _ hb)
  have hG : Integrable (fun p : Z × X => (g p.2 : ℂ) * φ p) (μ.prod ν) :=
    hgi.ofReal.mul_bdd hφ.aestronglyMeasurable (ae_of_all _ hb)
  rw [← integral_prod _ hF, ← integral_prod _ hG]
  have he := density_bounded_complex_test_error (μ.prod ν) (fun p => f p.2) (fun p => g p.2)
    hfi hgi φ hφ hb
  rwa [integral_snd_probability μ ν (fun x => |f x - g x|) (hf.sub hg).abs] at he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedCoveredComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S)))
variable (period : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
variable (hresidue : ∀ v, weights.weight v ≠ 0 → principalResidueLabel period v = principalResidueLabel period v₀)
variable (F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "density" => (fun v z => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z)
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "test" => allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F
local notation "actual" => (∫ p, weights.complexMean (fun v => F (Prod.fst ((allocatedCoefficientSplit B U b S) (Prod.fst p)),
  euclideanCoefficientJetMap U (root v) (dirs v) rows
    (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) (Prod.fst p) (Prod.snd p))))
    ∂(Measure.prod source (PMF.toMeasure deck)))

include hperiod hresidue

omit [DecidableEq G] in
theorem allocatedPhysicalCovered_test_comparison_of_l1_s2_oai
    (g : AllocatedLongJetRows B U b S O → ℝ) (hg : Integrable g reference)
    {ε : ℝ} (he : (∫ z, |weights.mean (fun v => density v z) - g z| ∂reference) ≤ ε)
    (hF : Measurable F) (hbound : ∀ p, ‖F p‖ ≤ 1) :
    ‖actual - ∫ a₀, ∫ z, (g z : ℂ) * test a₀ z ∂reference ∂frozenSource‖ ≤ ε := by
  let : IsProbabilityMeasure frozenSource := allocatedFrozenCoefficientSource_probability B U b hR hσ S
  have hf : Integrable (fun z => weights.mean (fun v => density v z)) reference :=
    integrable_finsetSum _ (fun v _ =>
      ((allocatedLongJetDensity_probability_data B U b hR hσ S x u v rows s hA hσ1).2.1).const_mul
        (weights.weight v))
  rw [allocatedPhysicalCovered_test_mean B U b hR hσ S x u v₀ rows Q hb o bW d F
    s hA hσ1 weights period hperiod hresidue hF hbound]
  have h := retained_density_nested_test_error frozenSource reference _ g hf hg
    (fun p => test p.1 p.2)
    (allocatedCoveredFixedTest_measurable B U b S x u v₀ rows Q hb o bW d F hF)
    (fun p => allocatedCoveredFixedTest_norm_le B U b S x u v₀ rows Q hb o bW d F hbound p.1 p.2)
  exact le_trans h (by simpa only [one_mul] using he)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedPhysicalCovered_test_comparison_of_l1_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.allocatedPhysicalCovered_test_comparison_of_l1_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
