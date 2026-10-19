-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedSlicedLongJet_ideal_transfer_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:36:42.270862+00:00
-- url     : https://prove2.me/submissions/83b159b3-fc57-4f50-8c3d-4c029cbb5c28

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedLongJet_residue_coefficient_l1_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialResidues
namespace OAI

section

namespace Erdos3

theorem integerPolynomial_eval_residue {X : Type*} (p : MvPolynomial X ℤ)
    (m : ℕ) (x : X → ℤ) :
    ((MvPolynomial.eval x p : ℤ) : ZMod m) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod m)) (integerResidueMap X m x) p := by
  have heq : integerResidueMap X m x = (fun i => (x i : ZMod m)) := rfl
  rw [heq]
  simpa only [MvPolynomial.eval₂_id, RingHom.comp_id, Int.coe_castRingHom] using
    MvPolynomial.hom_eval₂ p (RingHom.id ℤ) (Int.castRingHom (ZMod m)) x

theorem integerPolynomial_eval_congr {X : Type*} (p : MvPolynomial X ℤ)
    (m : ℕ) {x y : X → ℤ} (hxy : integerResidueMap X m x = integerResidueMap X m y) :
    ((MvPolynomial.eval x p : ℤ) : ZMod m) = ((MvPolynomial.eval y p : ℤ) : ZMod m) := by
  rw [integerPolynomial_eval_residue, integerPolynomial_eval_residue, hxy]

theorem integerBooleanCoefficient_residue {α : Type*} [DecidableEq α]
    (m : ℕ) (f : Finset α → ℤ) (s : Finset α) :
    ((booleanCoefficient f s : ℤ) : ZMod m) =
      booleanCoefficient (fun t => (f t : ZMod m)) s :=
  booleanCoefficient_map (Int.castRingHom (ZMod m)) f s

theorem integerBooleanCoefficient_congr {α : Type*} [DecidableEq α]
    (m : ℕ) (f g : Finset α → ℤ) (s : Finset α)
    (hfg : ∀ t ∈ s.powerset, (f t : ZMod m) = (g t : ZMod m)) :
    ((booleanCoefficient f s : ℤ) : ZMod m) = ((booleanCoefficient g s : ℤ) : ZMod m) := by
  rw [integerBooleanCoefficient_residue, integerBooleanCoefficient_residue]
  unfold booleanCoefficient
  apply Finset.sum_congr rfl
  intro t ht
  dsimp only
  rw [hfg t ht]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineResidues
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem integerJetMatrix_residue_eq {α K O J : Type*} [DecidableEq α]
    (basis : J → MvPolynomial K ℤ) (vertices vertices' : Finset α → K → ℤ)
    (rows : O → Finset α) (m : ℕ)
    (hvertices : ∀ o t, t ∈ (rows o).powerset →
      integerResidueMap K m (vertices t) = integerResidueMap K m (vertices' t)) :
    integerResidueMatrix (integerJetMatrix basis vertices rows) m =
      integerResidueMatrix (integerJetMatrix basis vertices' rows) m := by
  ext o j
  apply integerBooleanCoefficient_congr
  intro t ht
  exact integerPolynomial_eval_congr (basis j) m (hvertices o t ht)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerAffineCube_residue_eq {α K : Type*}
    (root root' : K → ℤ) (D D' : Matrix α K ℤ) (m : ℕ)
    (hroot : integerResidueMap K m root = integerResidueMap K m root')
    (hD : integerResidueMatrix D m = integerResidueMatrix D' m) (t : Finset α) :
    integerResidueMap K m (integerAffineCube root D t) =
      integerResidueMap K m (integerAffineCube root' D' t) := by
  funext k
  change ((root k + ∑ r ∈ t, D r k : ℤ) : ZMod m) =
    ((root' k + ∑ r ∈ t, D' r k : ℤ) : ZMod m)
  push_cast
  have hk : (root k : ZMod m) = (root' k : ZMod m) := congrFun hroot k
  rw [hk]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  exact congrFun (congrFun hD r) k

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3

theorem scalarCubeResidueWeights_support (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I+1)*M ≤ L)
    (x : IntegerScalarCubeBox I L)
    (hx : (scalarCubeResidueWeights I L M hL m r hm hmM hsize).weight x ≠ 0) :
    ∀ i, ((x i : ℤ) : ZMod (m i)) = r i := by
  classical
  apply (mem_scalarCubeResidueSet L m r x).mp
  by_contra hnot
  apply hx
  simp only [scalarCubeResidueWeights, FiniteProbabilityWeights.condition, hnot, ite_false, zero_div]

theorem scalarCubeResiduePi_support {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (r : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I+1)*M j ≤ L j)
    (x : ∀ j, IntegerScalarCubeBox I (L j))
    (hx : (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).weight x ≠ 0) :
    ∀ j i, ((x j i : ℤ) : ZMod (m j i)) = r j i := by
  intro j
  apply scalarCubeResidueWeights_support I (L j) (M j) (hL j) (m j) (r j) (hm j) (hmM j) (hsize j) (x j)
  intro hz
  apply hx
  exact Finset.prod_eq_zero (Finset.mem_univ j) hz

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeProductSupport
namespace OAI


namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem principalTupleFlatten_apply {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) (α : Type*) [Fintype α]
    (x : PrincipalTupleIndex B h → Option α → ℝ) (z : JointBlockParameter B h α) :
    principalTupleFlatten B h α x z = x ⟨z.1, z.2.1, z.2.2.1⟩ z.2.2.2 := rfl

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowReindex
namespace OAI


namespace Erdos3

theorem monomialCoefficientMatrix_residue_eq {α K I N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (vertices vertices' : Finset α → K → ℤ) (rows : I → Finset α) (m : ℕ)
    (hv : ∀ t, integerResidueMap K m (vertices t) = integerResidueMap K m (vertices' t)) :
    integerResidueMatrix (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) vertices rows) m =
      integerResidueMatrix (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) vertices' rows) m :=
  integerJetMatrix_residue_eq _ _ _ _ _ (fun _ t _ => hv t)


open MeasureTheory
open scoped BigOperators NNReal

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalResidueMixture
namespace OAI

section

namespace Erdos3

theorem integerMappedCubeTuple_residue {Z X K α : Type*}
    (input : K → Option α → Z ⊕ X) (z : Z → ℤ) (x y : X → ℤ) (m : ℕ)
    (hxy : integerResidueMap X m x = integerResidueMap X m y) (t : Finset α) :
    integerResidueMap K m (integerMappedCubeTuple input z x t) =
      integerResidueMap K m (integerMappedCubeTuple input z y t) := by
  apply integerAffineCube_residue_eq
  · funext k
    change ((Sum.elim z x (input k none) : ℤ) : ZMod m) =
      ((Sum.elim z y (input k none) : ℤ) : ZMod m)
    cases input k none with
    | inl j => rfl
    | inr j => exact congrFun hxy j
  · funext i k
    change ((Sum.elim z x (input k (some i)) : ℤ) : ZMod m) =
      ((Sum.elim z y (input k (some i)) : ℤ) : ZMod m)
    cases input k (some i) with
    | inl j => rfl
    | inr j => exact congrFun hxy j

theorem integerMappedJetMatrix_residue {Z X K α I N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℤ)
    (rows : I → Finset α) (x y : X → ℤ) (m : ℕ)
    (hxy : integerResidueMap X m x = integerResidueMap X m y) :
    integerResidueMatrix (integerMappedJetMatrix e input z rows x) m =
      integerResidueMatrix (integerMappedJetMatrix e input z rows y) m :=
  monomialCoefficientMatrix_residue_eq e _ _ rows m (integerMappedCubeTuple_residue input z x y m hxy)

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionTupleSliceSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace FiniteProbabilityWeights

theorem condition_weight_pos_iff {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < p.mass S) (x : Ω) :
    0 < (p.condition S hS).weight x ↔ x ∈ S ∧ 0 < p.weight x := by
  change 0 < (if x ∈ S then p.weight x else 0) / p.mass S ↔ _
  rw [lt_div_iff₀ hS, zero_mul]
  by_cases hx : x ∈ S <;> simp [hx]

theorem pi_weight_pos_component {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (x : ∀ j, Ω j) (hx : 0 < (pi p).weight x) (j : J) : 0 < (p j).weight (x j) := by
  apply lt_of_le_of_ne ((p j).nonneg (x j))
  intro he
  have hz : (pi p).weight x = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ j) he.symm
  linarith

end FiniteProbabilityWeights

theorem scalarCubeResidueWeights_cube_support (I : Type*) [Fintype I] [DecidableEq I]
    (H M : ℕ) (hH : 0 < H) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ H) (z : IntegerScalarCubeBox I H)
    (hz : 0 < (scalarCubeResidueWeights I H M hH m r hm hmM hsize).weight z) :
    IntegerScalarCube H (fun i => (z i : ℤ)) := by
  have h1 := (FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ z).mp hz
  have h2 := (FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ z).mp h1.2
  exact (mem_integerScalarCubeSet H z).mp h2.1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ContainedProgressionCubeMap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem containedProgressionCubeMap_value (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) (hz : IntegerScalarCube H (fun i => (z i : ℤ)))
    (i : Option I) :
    (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ) =
      (if i = none then c else 0) + (step : ℤ) * (z i : ℤ) := by
  rw [containedProgressionCubeMap, dif_pos hz]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteGoodSupport
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem mean_congr_on_support {f g : X → ℝ}
    (h : ∀ x, p.weight x ≠ 0 → f x = g x) : p.mean f = p.mean g :=
  le_antisymm (p.mean_mono_on_support (fun x hx => (h x hx).le))
    (p.mean_mono_on_support (fun x hx => (h x hx).ge))

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ContainedProgressionCubeLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

omit [DecidableEq D] [∀ d, DecidableEq (B d)] in
theorem containedProgressionTupleMap_normalized [DecidableEq D] [∀ d, DecidableEq (B d)]
    (v : PrincipalIntegerTuples B h α H)
    (hv : ∀ j, IntegerScalarCube (H j) (fun i => (v j i : ℤ))) :
    principalTupleNormalized L (containedProgressionTupleMap B h L H step c hL hsubset v) =
      principalTupleFlatten B h α
        (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j) := by
  funext a
  simp only [principalTupleNormalized, principalTupleIntegers, containedProgressionTupleMap,
    containedProgressionCubeMap_value _ _ _ _ _ _ _ _ (hv _), principalTupleFlatten_apply,
    Int.cast_add, Int.cast_mul, Int.cast_natCast, apply_ite, Int.cast_zero]

theorem containedProgressionTupleLaw_mean
    (p : FiniteProbabilityWeights (PrincipalIntegerTuples B h α H))
    (hp : ∀ v, p.weight v ≠ 0 → ∀ j, IntegerScalarCube (H j) (fun i => (v j i : ℤ)))
    (f : (JointBlockParameter B h α → ℝ) → ℝ) :
    (p.fiberLaw (containedProgressionTupleMap B h L H step c hL hsubset)).mean
        (fun v => f (principalTupleNormalized L v)) =
      p.mean (fun v => f (principalTupleFlatten B h α
        (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j))) := by
  rw [p.fiberLaw_mean]
  apply p.mean_congr_on_support
  intro v hv
  rw [containedProgressionTupleMap_normalized B h L H step c hL hsubset v (hp v hv)]

end Erdos3

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteFiberLawSupport
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

theorem fiberLaw_support {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) (P : Y → Prop)
    (hP : ∀ x, p.weight x ≠ 0 → P (F x))
    (y : Y) (hy : (p.fiberLaw F).weight y ≠ 0) : P y := by
  classical
  by_contra hn
  apply hy
  change p.mean (fun x => if F x = y then (1 : ℝ) else 0) = 0
  calc
    _ = p.mean (fun _ => 0) := by
      apply p.mean_congr_on_support
      intro x hx
      apply if_neg
      intro he
      exact hn (he ▸ hP x hx)
    _ = 0 := p.mean_const 0

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ContainedFullIntervalResidueIdentity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (modulus : ℕ) (hm : 0 < modulus)
variable (r : PrincipalTupleIndex B h → Option α → ZMod modulus)
variable (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)

local notation "weights" => principalResidueWeights B h H hH modulus hm r hsize
local notation "tupleMap" => containedProgressionTupleMap B h L H step c hL hsubset

theorem principalResidueWeights_cube_support
    (v : PrincipalIntegerTuples B h α H) (hv : (weights).weight v ≠ 0)
    (j : PrincipalTupleIndex B h) : IntegerScalarCube (H j) (fun i => (v j i : ℤ)) := by
  apply scalarCubeResidueWeights_cube_support α (H j) modulus (hH j)
    (fun _ => modulus) (r j) (fun _ => hm) (fun _ => le_rfl) (hsize j)
  exact FiniteProbabilityWeights.pi_weight_pos_component _ v
    (lt_of_le_of_ne ((weights).nonneg v) (Ne.symm hv)) j

theorem containedProgressionResidueLaw_mean (f : (JointBlockParameter B h α → ℝ) → ℝ) :
    (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).mean
        (fun v => f (principalTupleNormalized L v)) =
      (weights).mean (fun v => f (principalTupleFlatten B h α
        (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j))) := by
  exact containedProgressionTupleLaw_mean B h L H step c hL hsubset weights
    (principalResidueWeights_cube_support B h H hH modulus hm r hsize) f

theorem containedProgressionResidueLaw_support
    (v : PrincipalIntegerTuples B h α L)
    (hv : (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).weight v ≠ 0) :
    ∀ j i, ((v j i : ℤ) : ZMod modulus) =
      (if i = none then (c j : ZMod modulus) else 0) + (step j : ZMod modulus) * r j i := by
  apply (weights).fiberLaw_support tupleMap
    (fun v => ∀ j i, ((v j i : ℤ) : ZMod modulus) =
      (if i = none then (c j : ZMod modulus) else 0) + (step j : ZMod modulus) * r j i) _ v hv
  intro z hz j i
  have hc := principalResidueWeights_cube_support B h H hH modulus hm r hsize z hz j
  have hr := scalarCubeResiduePi_support H (fun _ => modulus) hH
    (fun _ _ => modulus) r (fun _ _ => hm) (fun _ _ => le_rfl) hsize z hz j i
  change ((containedProgressionCubeMap α (L j) (H j) (step j) (c j) (hL j) (hsubset j) (z j) i : ℤ) : ZMod modulus) = _
  rw [containedProgressionCubeMap_value _ _ _ _ _ _ _ _ hc]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, apply_ite, Int.cast_zero, hr]

theorem containedProgressionResidueLaw_matrix {Z K I N : Type*}
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (z : Z → ℤ) (rows : I → Finset α)
    (v v₀ : PrincipalIntegerTuples B h α L)
    (hv : (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).weight v ≠ 0)
    (hv₀ : (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).weight v₀ ≠ 0) :
    integerResidueMatrix (integerMappedJetMatrix e input z rows (principalTupleIntegers v)) modulus =
      integerResidueMatrix (integerMappedJetMatrix e input z rows (principalTupleIntegers v₀)) modulus := by
  apply integerMappedJetMatrix_residue
  funext a
  change ((v ⟨a.1,a.2.1,a.2.2.1⟩ a.2.2.2 : ℤ) : ZMod modulus) =
    ((v₀ ⟨a.1,a.2.1,a.2.2.1⟩ a.2.2.2 : ℤ) : ZMod modulus)
  rw [containedProgressionResidueLaw_support B h L H step c hL hH hsubset modulus hm r hsize v hv,
    containedProgressionResidueLaw_support B h L H step c hL hH hsubset modulus hm r hsize v₀ hv₀]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityComparisonComposition
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem density_l1_triangle_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g h : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, |f x - h x| ∂μ) ≤ (∫ x, |f x - g x| ∂μ) + ∫ x, |g x - h x| ∂μ := by
  rw [← integral_add (f := fun x => |f x - g x|) (g := fun x => |g x - h x|)
    (hf.sub hg).abs (hg.sub hh).abs]
  exact integral_mono (hf.sub hh).abs ((hf.sub hg).abs.add (hg.sub hh).abs)
    (fun x => abs_sub_le (f x) (g x) (h x))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem density_l1_triangle_bound_reverse {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g h : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ)
    {A B : ℝ} (hfg : (∫ x, |f x - g x| ∂μ) ≤ A)
    (hhg : (∫ x, |h x - g x| ∂μ) ≤ B) :
    (∫ x, |f x - h x| ∂μ) ≤ A + B := by
  apply (density_l1_triangle_le μ f g h hf hg hh).trans
  apply add_le_add hfg
  simpa only [abs_sub_comm] using hhg

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedOriginalLongComparison
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
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => layerSamplerDegree I n (Subtype.val a))
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides
local notation "tupleIndex" => PrincipalTupleIndex activeB activeDegree
local notation "positiveLengths" => (fun j : tupleIndex => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

theorem allocatedSlicedLongJet_coefficient_l1 {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
    (modulus : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
    (u : PrincipalAxisTuples (α := α) grid sides)
    (H step : tupleIndex → ℕ) (c : tupleIndex → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (lengths j : ℤ))
    (hm : 0 < modulus) (r : tupleIndex → Option α → ZMod modulus)
    (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize).weight v₀ ≠ 0) :
    let C := Real.exp (allocatedDensityLog (G := G) B α O P)
    let CM : ℝ := layerKernelIndexBound m M
    let T := Real.exp (allocatedJetSupportLog (G := G) B α O P)
    let law := containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize
    let residue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    let proxy := fun z => (principalResidueWeights activeB activeDegree H hH modulus hm r hsize).mean
      (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
        (principalTupleFlatten activeB activeDegree α
          (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / lengths j)) z)
    Integrable (allocatedLongProfileDensity B U basis S x rows modulus residue proxy)
      (allocatedLongJetReference B U basis S O) ∧
    (∫ z, |law.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) -
        allocatedLongProfileDensity B U basis S x rows modulus residue proxy z|
      ∂allocatedLongJetReference B U basis S O) ≤
      (2*T+1)^Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * ε * (1 + CM * C + ε)^Fintype.card {a // ¬grid a}) := by
  intro C CM T law residue proxy
  have hr (v) (hv : law.weight v ≠ 0) (j : Fin m) :
      integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j := by
    exact containedProgressionResidueLaw_matrix activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize (allocatedNonkernelExponent B j)
      (partitionedPrincipalInput grid (fun g a => (g,a)))
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
      (rows j) v v₀ hv hv₀
  have he := allocatedLongJet_residue_coefficient_l1_s2 B U basis hR hσ S x rows
    hM selection hx hq hinj hrows hσ1 hP he hε hMP hRP hRi hσi hcount hεe hlarge
    modulus hperiod s hA hi u law residue hr
  have hp : (fun z => law.mean (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
      (principalTupleNormalized lengths v) z)) = proxy := by
    funext z
    exact containedProgressionResidueLaw_mean activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize (fun y => allocatedNormalizedLongJetDensity B U basis S x u rows s hA y z)
  dsimp only at he
  rw [hp] at he
  exact he

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
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => layerSamplerDegree I n (Subtype.val a))
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides
local notation "tupleIndex" => PrincipalTupleIndex activeB activeDegree
local notation "positiveLengths" => (fun j : tupleIndex => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

theorem allocatedSlicedLongJet_ideal_transfer_s2_oai {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
    (modulus : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
    (u : PrincipalAxisTuples (α := α) grid sides)
    (H step : tupleIndex → ℕ) (c : tupleIndex → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (lengths j : ℤ))
    (hm : 0 < modulus) (r : tupleIndex → Option α → ZMod modulus)
    (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize).weight v₀ ≠ 0)
    (g : AllocatedLongJetRows B U basis S O → ℝ)
    (hg : Integrable g (allocatedLongJetReference B U basis S O)) {Eref : ℝ} :
    let C := Real.exp (allocatedDensityLog (G := G) B α O P)
    let CM : ℝ := layerKernelIndexBound m M
    let T := Real.exp (allocatedJetSupportLog (G := G) B α O P)
    let law := containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset modulus hm r hsize
    let residue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    let proxy := fun z => (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α
      (H j) modulus (hH j) (fun _ => modulus) (r j) (fun _ => hm) (fun _ => le_rfl) (hsize j))).mean
      (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
        (principalTupleFlatten activeB activeDegree α
          (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / lengths j)) z)
    (∫ z, |g z - allocatedLongProfileDensity B U basis S x rows modulus residue proxy z|
      ∂allocatedLongJetReference B U basis S O) ≤ Eref →
    (∫ z, |law.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) - g z|
      ∂allocatedLongJetReference B U basis S O) ≤
      (2*T+1)^Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * ε * (1 + CM * C + ε)^Fintype.card {a // ¬grid a}) + Eref := by
  intro C CM T law residue proxy href
  have hcoef := allocatedSlicedLongJet_coefficient_l1 B U basis hR hσ S x rows
    hM selection hx hq hinj hrows hσ1 hP he hε hMP hRP hRi hσi hcount hεe hlarge
    modulus hperiod s hA hi u H step c hH hsubset hm r hsize v₀ hv₀
  have hfi : Integrable (fun z => law.mean
      (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z))
      (allocatedLongJetReference B U basis S O) :=
    law.mean_integrable _ _ (fun v =>
      (allocatedLongJetDensity_probability_data B U basis hR hσ S x u v rows s hA hσ1).2.1)
  exact density_l1_triangle_bound_reverse (allocatedLongJetReference B U basis S O)
    _ _ _ hfi hcoef.1 hg hcoef.2 href

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedSlicedLongJet_ideal_transfer_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedSlicedLongJet_ideal_transfer_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
