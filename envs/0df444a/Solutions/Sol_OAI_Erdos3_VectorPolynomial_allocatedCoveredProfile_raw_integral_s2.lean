-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedCoveredProfile_raw_integral_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:26:39.190871+00:00
-- url     : https://prove2.me/submissions/0a7afa7e-91ee-49db-aaca-56194e42fdec

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B196

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ENNReal

theorem pi_count_measure {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] [∀ i, Countable (X i)] :
    Measure.pi (fun i => (Measure.count : Measure (X i))) =
      (Measure.count : Measure (∀ i, X i)) := by
  apply Measure.ext_of_singleton
  intro x
  simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SigmaFiniteProductMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem sigmaFiniteProductMeasure_flatten {D : Type*} [Fintype D] {I : D → Type*}
    [∀ d, Fintype (I d)] {X : (Σ d, I d) → Type*}
    [∀ s, MeasurableSpace (X s)] (μ : ∀ s, Measure (X s)) [∀ s, SigmaFinite (μ s)] :
    (Measure.pi (fun d => Measure.pi (fun i => μ ⟨d, i⟩))).map
      (fun x (s : Σ d, I d) => x s.1 s.2) = Measure.pi μ := by
  have hm : Measurable (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) :=
    measurable_pi_iff.mpr (fun s => (measurable_pi_apply s.2).comp (measurable_pi_apply s.1))
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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientDeckDensityLawCongruence
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

theorem pmf_realDensity_uniform {X : Type*} [Fintype X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : PMF X) :
    p.toMeasure = realDensityMeasure (PMF.uniformOfFintype X).toMeasure
      (fun x => (Fintype.card X : ℝ) * (p x).toReal) := by
  apply Measure.ext_of_singleton
  intro x
  rw [realDensityMeasure, withDensity_apply _ (measurableSet_singleton x), lintegral_singleton]
  rw [p.toMeasure_apply_singleton x (measurableSet_singleton x),
    (PMF.uniformOfFintype X).toMeasure_apply_singleton x (measurableSet_singleton x)]
  simp only [PMF.uniformOfFintype_apply,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_toReal (p.apply_ne_top x)]
  have hc : (Fintype.card X : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_right_comm, ENNReal.mul_inv_cancel hc (by simp), one_mul]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

theorem coefficientDeckJetDensity_nonneg (d : ℕ) [NeZero d]
    (r : ∀ j, O j → B j → ZMod d) : 0 ≤ coefficientDeckJetDensity root A rows d r :=
  mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg

theorem coefficientDeckJetDensity_le_card (d : ℕ) [NeZero d]
    (r : ∀ j, O j → B j → ZMod d) :
    coefficientDeckJetDensity root A rows d r ≤ Fintype.card (∀ j, O j → B j → ZMod d) := by
  let p := (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
    (coefficientDeckJetMap root A rows d)
  have hp : (p r).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one r)
  exact (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)).trans_eq (mul_one _)

theorem coefficientDeckJetDensity_law (d : ℕ) [NeZero d] :
    ((PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
      (coefficientDeckJetMap root A rows d)).toMeasure =
    realDensityMeasure (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure
      (coefficientDeckJetDensity root A rows d) :=
  pmf_realDensity_uniform _

theorem coefficientDeckJetDensity_probability (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (realDensityMeasure
      (PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure
      (coefficientDeckJetDensity root A rows d)) := by
  rw [← coefficientDeckJetDensity_law]
  infer_instance

end Erdos3.VectorPolynomial

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

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientJetDensityFactors
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

variable {I Z O J : Type*} [Fintype I] [Fintype Z]
variable [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
variable (A : Matrix O J ℤ) (s : O ↪ J) (hA : (A.submatrix id s).det ≠ 0)

omit [Fintype O] [DecidableEq O] [DecidableEq J] in
theorem integerMatrixImagePMF_law (p : J → PMF ℤ) :
    (Measure.pi (fun j => (p j).toMeasure)).map (fun z => A *ᵥ z) =
      (integerMatrixImagePMF A p).toMeasure := by
  rw [integerMatrixImagePMF, ← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  congr 1
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

theorem allocatedCoefficientAxisLaw_probability (a : LayerSamplerAxis I n) :
    IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a) :=
  coefficientAxisLaw_probability _ _ _ (allocatedLayerWidths_pos B U basis hR hσ S) a

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

theorem finitePMF_integral_comp {T Y : Type*} [Fintype T] [Fintype Y]
    [MeasurableSpace T] [MeasurableSingletonClass T]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p : PMF T) (f : T → Y) (φ : Y → ℂ) :
    (∫ t, φ (f t) ∂p.toMeasure) = ∫ y, φ y ∂(p.map f).toMeasure := by
  rw [← PMF.toMeasure_map f p (measurable_of_finite f)]
  exact (integral_map (measurable_of_finite f).aemeasurable
    (measurable_of_finite φ).aestronglyMeasurable).symm

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]

theorem coefficientDeckJetDensity_integral
    (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (d : ℕ) [NeZero d] (φ : (∀ j, O j → B j → ZMod d) → ℂ) :
    (∫ r, φ (coefficientDeckJetMap root A rows d r)
      ∂(PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure) =
    ∫ r, (coefficientDeckJetDensity root A rows d r : ℂ) * φ r
      ∂(PMF.uniformOfFintype (∀ j, O j → B j → ZMod d)).toMeasure := by
  rw [finitePMF_integral_comp _ (coefficientDeckJetMap root A rows d) φ,
    coefficientDeckJetDensity_law root A rows d,
    realDensityMeasure_integral_complex _ _ (measurable_of_finite _)
      (coefficientDeckJetDensity_nonneg root A rows d)]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFrozenJetDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedGridJetFactor_mem_Icc (a : {a // grid a}) (z : CoefficientJetAxisRow O a.val) :
    allocatedGridJetFactor B U b hR hσ S x u v rows a z ∈ Set.Icc (0 : ℝ) 1 := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · refine ⟨ENNReal.toReal_nonneg, ?_⟩
    exact (ENNReal.toReal_mono ENNReal.one_ne_top ((integerMatrixImagePMF
      (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j))
      (allocatedLayerIntegerPMFs B U b hR hσ S j i)).coe_le_one z)).trans_eq ENNReal.toReal_one

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedGridJetDensity_mem_Icc (z : AllocatedFrozenJetRows B U b S O) :
    allocatedGridJetDensity B U b hR hσ S x u v rows z ∈ Set.Icc (0 : ℝ) 1 := by
  have h := allocatedGridJetFactor_mem_Icc B U b hR hσ S x u v rows
  exact ⟨Finset.prod_nonneg (fun a _ => (h a (z a)).1),
    Finset.prod_le_one (fun a _ => (h a (z a)).1) (fun a _ => (h a (z a)).2)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

theorem allocatedGridJetFactor_probability_data
    (a : {a // allocatedGridAxis (I := I) U b S.value a}) :
    Integrable (allocatedGridJetFactor B U b hR hσ S x u v rows a)
      (coefficientJetAxisReference O a.val) ∧
    (∫ z, allocatedGridJetFactor B U b hR hσ S x u v rows a z
      ∂coefficientJetAxisReference O a.val) = 1 := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · change Integrable _ (Measure.count : Measure (O j → ℤ)) ∧
      (∫ z : O j → ℤ, _ ∂Measure.count) = 1
    exact ⟨pmf_real_integrable _, pmf_real_integral_count _⟩

theorem allocatedGridJetFactor_law
    (a : {a // allocatedGridAxis (I := I) U b S.value a}) :
    (allocatedCoefficientAxisLaw B U b hR hσ S a.val).map
      (coefficientJetAxisMap (allocatedPartitionedJetMatrix B U b S x u v rows) a.val) =
      realDensityMeasure (coefficientJetAxisReference O a.val)
        (allocatedGridJetFactor B U b hR hσ S x u v rows a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · change (Measure.pi (fun e => (allocatedLayerIntegerPMFs B U b hR hσ S j i e).toMeasure)).map
        (fun c => allocatedPartitionedJetMatrix B U b S x u v rows j *ᵥ c) =
      realDensityMeasure Measure.count (fun z =>
        (integerMatrixImagePMF _ (allocatedLayerIntegerPMFs B U b hR hσ S j i) z).toReal)
    rw [← pmf_realDensity_count, allocatedPartitionedJetMatrix_eq_physical]
    exact integerMatrixImagePMF_law _ _

theorem allocatedGridJetDensity_probability_data :
    Integrable (allocatedGridJetDensity B U b hR hσ S x u v rows)
      (allocatedFrozenJetReference B U b S O) ∧
    (∫ z, allocatedGridJetDensity B U b hR hσ S x u v rows z
      ∂allocatedFrozenJetReference B U b S O) = 1 := by
  have hp := allocatedGridJetFactor_probability_data B U b S O hR hσ x u v rows
  refine ⟨Integrable.fintype_prod_dep (fun a => (hp a).1), ?_⟩
  change (∫ z, (∏ a, allocatedGridJetFactor B U b hR hσ S x u v rows a (z a))
    ∂Measure.pi (fun a : {a // allocatedGridAxis (I := I) U b S.value a} =>
      coefficientJetAxisReference O a.val)) = 1
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_eq_one (fun a _ => (hp a).2)

theorem allocatedGridJetDensity_law :
    (allocatedFrozenCoefficientSource B U b hR hσ S).map
      (allocatedFrozenJetMap B U b S x u v rows) =
      realDensityMeasure (allocatedFrozenJetReference B U b S O)
        (allocatedGridJetDensity B U b hR hσ S x u v rows) := by
  let : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      IsProbabilityMeasure (allocatedCoefficientAxisLaw B U b hR hσ S a.val) :=
    fun a => allocatedCoefficientAxisLaw_probability B U b hR hσ S a.val
  unfold allocatedFrozenCoefficientSource allocatedFrozenJetMap
  rw [Measure.pi_map_pi (fun a =>
    (coefficientJetAxisMap_measurable (allocatedPartitionedJetMatrix B U b S x u v rows) a.val).aemeasurable)]
  simp_rw [allocatedGridJetFactor_law B U b S O hR hσ x u v rows]
  exact realDensityMeasure_pi _ _
    (fun a => (allocatedGridJetFactor_probability_data B U b S O hR hσ x u v rows a).1)
    (fun a z => (allocatedGridJetFactor_mem_Icc B U b hR hσ S x u v rows a z).1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JetAxisReference
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} (O I : Fin m → Type*) (n : Fin m → ℕ)
variable [∀ j, Fintype (O j)] [∀ j, Fintype (I j)]

theorem coefficientJetAxisEquiv_measurePreserving :
    MeasurePreserving (coefficientJetAxisEquiv O I n)
      (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j)))
      (Measure.pi (coefficientJetAxisReference O)) := by
  let laws := coefficientJetAxisReference (I := I) (n := n) O
  have hinner (j : Fin m) : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun a : I j ⊕ Fin (n j) => CoefficientJetAxisRow O ⟨j, a⟩)).symm
      (mixedArrayReference (I j) (Fin (n j)) (O j))
      (Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)) := by
    have hc : (Measure.pi (fun _ : Fin (n j) => (Measure.count : Measure (O j → ℤ)))) =
        Measure.count := pi_count_measure
    have h := measurePreserving_sumPiEquivProdPi_symm
      (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)
    change MeasurePreserving _
      ((Measure.pi (fun _ : I j => (volume : Measure (O j → ℝ)))).prod
        (Measure.pi (fun _ : Fin (n j) => (Measure.count : Measure (O j → ℤ))))) _ at h
    rw [hc] at h
    change MeasurePreserving _
      ((volume : Measure (I j → O j → ℝ)).prod
        (Measure.count : Measure (Fin (n j) → O j → ℤ))) _
    rw [volume_pi]
    exact h
  have houter := measurePreserving_pi
    (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))
    (fun j => Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)) hinner
  have hflat : MeasurePreserving
      (MeasurableEquiv.piCurry
        (fun j (a : I j ⊕ Fin (n j)) => CoefficientJetAxisRow O ⟨j, a⟩)).symm
      (Measure.pi (fun j => Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)))
      (Measure.pi laws) :=
    ⟨(MeasurableEquiv.piCurry
      (fun j (a : I j ⊕ Fin (n j)) => CoefficientJetAxisRow O ⟨j, a⟩)).symm.measurable,
      sigmaFiniteProductMeasure_flatten laws⟩
  exact hflat.comp houter

theorem coefficientJetAxisSplit_measurePreserving
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    MeasurePreserving (coefficientJetAxisSplit O I n P)
      (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j)))
      ((Measure.pi (fun a : {a // P a} => coefficientJetAxisReference O a.val)).prod
        (Measure.pi (fun a : {a // ¬P a} => coefficientJetAxisReference O a.val))) :=
  (measurePreserving_piEquivPiSubtypeProd (coefficientJetAxisReference O) P).comp
    (coefficientJetAxisEquiv_measurePreserving O I n)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoveredSiteExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

theorem allocatedGridJetDensity_measurable :
    Measurable (allocatedGridJetDensity B U b hR hσ S x u v rows) := by
  have hr (a : {a // grid a}) : Measurable (allocatedGridJetFactor B U b hR hσ S x u v rows a) := by
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · change Measurable (fun z : O j → ℤ =>
        (integerMatrixImagePMF (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j))
          (allocatedLayerIntegerPMFs B U b hR hσ S j i) z).toReal)
      exact measurable_of_countable _
  exact Finset.measurable_prod _ (fun a _ => (hr a).comp (measurable_pi_apply a))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedGridlessProfileBound
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

local notation "gridRef" => allocatedFrozenJetReference B U b S O
local notation "longRef" => allocatedLongJetReference B U b S O
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := Q) (n := n) d

theorem allocatedGridlessWeightedKernel_mass_data
    (g : AllocatedFrozenJetRows B U b S O → ℝ) (f : AllocatedLongJetRows B U b S O → ℝ)
    (hg : Integrable g gridRef) (hf : Integrable f longRef) :
    Integrable (allocatedGridlessWeightedKernel B U b S x u v rows (Q := Q) d g f) raw ∧
      (∫ z, |allocatedGridlessWeightedKernel B U b S x u v rows (Q := Q) d g f z| ∂raw) =
        (∫ z, |g z| ∂gridRef) * ∫ z, |f z| ∂longRef := by
  let μd := (PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure
  let fd : (∀ j, O j → Q j → ZMod d) → ℝ := coefficientDeckJetDensity root dirs rows d
  let e := MeasurableEquiv.prodCongr split (MeasurableEquiv.refl (∀ j, O j → Q j → ZMod d))
  let F (z : (AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O) ×
      (∀ j, O j → Q j → ZMod d)) : ℝ := g z.1.1 * f z.1.2 * fd z.2
  let : IsProbabilityMeasure (realDensityMeasure μd fd) := coefficientDeckJetDensity_probability _ _ rows d
  have hfd := boundedDensity_mass μd fd (measurable_of_finite _) (coefficientDeckJetDensity_nonneg _ _ rows d)
    (coefficientDeckJetDensity_le_card _ _ rows d)
  have hFi : Integrable F (((gridRef).prod longRef).prod μd) := (hg.mul_prod hf).mul_prod hfd.1
  have he : MeasurePreserving e raw (((gridRef).prod longRef).prod μd) :=
    (coefficientJetAxisSplit_measurePreserving O I n grid).prod (MeasurePreserving.id μd)
  refine ⟨(he.integrable_comp_emb e.measurableEmbedding).mpr hFi, ?_⟩
  change (∫ z, |F (e z)| ∂raw) = _
  rw [he.integral_comp e.measurableEmbedding (fun z => |F z|)]
  have habs : (fun z => |F z|) = (fun z => |g z.1.1| * |f z.1.2| * fd z.2) := by
    funext z
    dsimp only [F]
    rw [abs_mul, abs_mul, abs_of_nonneg (coefficientDeckJetDensity_nonneg root dirs rows d z.2)]
  rw [habs, integral_prod_mul (μ := (gridRef).prod longRef) (ν := μd)
    (fun z : AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O => |g z.1| * |f z.2|) fd,
    integral_prod_mul (μ := gridRef) (ν := longRef) (fun z => |g z|) (fun z => |f z|), hfd.2, mul_one]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSlicedRowIdealSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "gridRef" => allocatedFrozenJetReference B U b S O
local notation "longRef" => allocatedLongJetReference B U b S O
local notation "rawRef" => Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))
local notation "fg" => allocatedGridJetDensity B U b hR hσ S x u v rows

theorem allocatedFrozenProfile_mixed_integral
    (f : AllocatedLongJetRows B U b S O → ℝ) (hfm : Measurable f)
    (hf : Integrable f longRef)
    (φ : (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) → ℂ)
    (hφ : Measurable φ) {C : ℝ} (hbound : ∀ z, ‖φ z‖ ≤ C) :
    (∫ a, ∫ z, (f z : ℂ) * φ (allocatedMixedJetReconstruct B U b S x u v rows a z)
      ∂longRef ∂allocatedFrozenCoefficientSource B U b hR hσ S) =
    ∫ z, ((fg ((split z).1) * f ((split z).2) : ℝ) : ℂ) * φ z ∂rawRef := by
  let ψ := fun p : AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O =>
    (f p.2 : ℂ) * φ ((split).symm p)
  have hψ : Measurable ψ :=
    (Complex.measurable_ofReal.comp (hfm.comp measurable_snd)).mul
      (hφ.comp (split).symm.measurable)
  have hint : Measurable (fun g => ∫ z, ψ (g, z) ∂longRef) :=
    hψ.stronglyMeasurable.integral_prod_right'.measurable
  have hfg := (allocatedGridJetDensity_probability_data B U b S O hR hσ x u v rows).1
  have hprod : Integrable (fun p : AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O =>
      ((fg p.1 * f p.2 : ℝ) : ℂ) * φ ((split).symm p)) ((gridRef).prod longRef) :=
    (hfg.mul_prod hf).ofReal.mul_bdd (hφ.comp (split).symm.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound _))
  calc
    _ = ∫ g, (fg g : ℂ) * (∫ z, ψ (g, z) ∂longRef) ∂gridRef := by
      change (∫ a, (fun g => ∫ z, ψ (g, z) ∂longRef)
        (allocatedFrozenJetMap B U b S x u v rows a)
        ∂allocatedFrozenCoefficientSource B U b hR hσ S) = _
      rw [← integral_map (allocatedFrozenJetMap_measurable B U b S x u v rows).aemeasurable
        hint.aestronglyMeasurable, allocatedGridJetDensity_law B U b S O hR hσ x u v rows,
        realDensityMeasure_integral_complex gridRef fg
          (allocatedGridJetDensity_measurable B U b hR hσ S x u v rows)
          (fun z => (allocatedGridJetDensity_mem_Icc B U b hR hσ S x u v rows z).1)]
    _ = ∫ g, ∫ z, ((fg g * f z : ℝ) : ℂ) * φ ((split).symm (g, z)) ∂longRef ∂gridRef := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun g => by
        calc
          _ = ∫ z, (fg g : ℂ) * ψ (g, z) ∂longRef :=
            (integral_const_mul (fg g : ℂ) (fun z => ψ (g, z))).symm
          _ = _ := integral_congr_ae (Filter.Eventually.of_forall
            (fun z => by simp only [ψ, Complex.ofReal_mul, mul_assoc])))
    _ = ∫ p, ((fg p.1 * f p.2 : ℝ) : ℂ) * φ ((split).symm p) ∂(gridRef).prod longRef :=
      (integral_prod _ hprod).symm
    _ = _ := by
      have he := coefficientJetAxisSplit_measurePreserving O I n grid
      have hh := he.integral_comp (split).measurableEmbedding
        (fun p => ((fg p.1 * f p.2 : ℝ) : ℂ) * φ ((split).symm p))
      simpa only [allocatedFrozenJetReference, allocatedLongJetReference,
        MeasurableEquiv.symm_apply_apply] using hh.symm

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
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "longRef" => allocatedLongJetReference B U b S O
local notation "mixedRef" => Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := Q) (n := n) d
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "fg" => allocatedGridJetDensity B U b hR hσ S x u v₀ rows
local notation "fd" => coefficientDeckJetDensity (B := Q) root dirs rows d
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

omit [Fintype α] in
theorem allocatedCoveredDeck_density_test
    (F : EuclideanJetLayers U O → ℂ)
    (t : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    (∫ r, F (chart (t, coefficientDeckJetMap root dirs rows d r)) ∂(deck).toMeasure) =
      ∫ r, (fd r : ℂ) * F (chart (t, r))
        ∂(PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure := by
  have he := coefficientDeckJetDensity_integral
    (K := LayerSamplerVariables G I n B) (O := O) (B := Q)
    root dirs rows d (fun r => F (chart (t, r)))
  convert he using 1
  apply congrArg (fun p : PMF (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d) =>
    ∫ r, F (chart (t, coefficientDeckJetMap root dirs rows d r)) ∂p.toMeasure)
  exact congrArg (fun i : Fintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d) =>
    @PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d) i _)
      (Subsingleton.elim _ _)

omit [Fintype α] in
theorem allocatedCoveredProfile_raw_integral_s2_oai
    (f : AllocatedLongJetRows B U b S O → ℝ) (hfm : Measurable f)
    (hf : Integrable f longRef)
    (F : EuclideanJetLayers U O → ℂ) (hF : Measurable F)
    {C : ℝ} (hbound : ∀ z, ‖F z‖ ≤ C) :
    (∫ a, ∫ z, (f z : ℂ) *
      allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d (fun p => F p.2) a z
      ∂longRef ∂allocatedFrozenCoefficientSource B U b hR hσ S) =
    ∫ z, (allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f z : ℂ) *
      F (chart z) ∂raw := by
  let φ := fun t : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ) =>
    ∫ r, F (chart (t, coefficientDeckJetMap root dirs rows d r)) ∂(deck).toMeasure
  have hchart : Measurable chart :=
    (coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
      (mixedCoveredJetCoordinates_measurable (O := O) (B := Q) (n := n) U o d)
  have hφ : Measurable φ := finitePMF_integral_measurable deck _
    (fun r => hF.comp (hchart.comp (measurable_id.prodMk measurable_const)))
  have hφb : ∀ t, ‖φ t‖ ≤ C := fun t => finitePMF_integral_norm_le deck _ (fun r => hbound _)
  have hφeq (t) : φ t = ∫ r, (fd r : ℂ) * F (chart (t, r)) ∂(PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure := by
    exact allocatedCoveredDeck_density_test B U b S x u v₀ rows Q hb o bW d F t
  have hi := (allocatedGridlessWeightedKernel_mass_data B U b S x u v₀ rows (Q := Q) d fg f
    (allocatedGridJetDensity_probability_data B U b S O hR hσ x u v₀ rows).1 hf).1
  have hprod : Integrable (fun z : MixedCoveredJetSource I O Q n d =>
      (allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f z : ℂ) *
        F (chart z)) raw :=
    hi.ofReal.mul_bdd (hF.comp hchart).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => hbound _))
  calc
    _ = ∫ t, ((fg ((split t).1) * f ((split t).2) : ℝ) : ℂ) * φ t ∂mixedRef :=
      allocatedFrozenProfile_mixed_integral B U b S O hR hσ x u v₀ rows f hfm hf φ hφ hφb
    _ = ∫ t, ∫ r,
        (allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f (t, r) : ℂ) *
          F (chart (t, r)) ∂(PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure ∂mixedRef := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      change ((fg ((split t).1) * f ((split t).2) : ℝ) : ℂ) * φ t = _
      rw [hφeq t]
      rw [← integral_const_mul (((fg ((split t).1) * f ((split t).2) : ℝ) : ℂ))]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun r => by
        simp only [allocatedGridlessWeightedKernel, Complex.ofReal_mul, mul_assoc])
    _ = _ := (integral_prod _ hprod).symm

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedCoveredProfile_raw_integral_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.allocatedCoveredProfile_raw_integral_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
