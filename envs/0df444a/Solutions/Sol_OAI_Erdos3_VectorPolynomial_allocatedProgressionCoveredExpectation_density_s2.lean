-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedProgressionCoveredExpectation_density_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:36:12.665253+00:00
-- url     : https://prove2.me/submissions/2bf3f450-8711-499a-a2d3-cd5cd20a2e2c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem complexMean_ofReal_mul (f : X → ℝ) (z : ℂ) :
    p.complexMean (fun x => (f x : ℂ) * z) = (p.mean f : ℂ) * z := by
  simp only [complexMean, mean, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_mul, mul_assoc]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem mixedScalarArrayLaw_probability {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Z → J → PMF ℤ) :
    IsProbabilityMeasure (mixedScalarArrayLaw c w p) := by
  let : ∀ i j, IsProbabilityMeasure (affineCoefficientMeasure (c i j) (w i j)) :=
    fun i j => affineCoefficientMeasure_probability _ (hw i j)
  unfold mixedScalarArrayLaw
  infer_instance

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexSampledSquarePerturbation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace FiniteProbabilityWeights

theorem complexMean_integral {Y X : Type*} [Fintype Y] [MeasurableSpace X]
    (law : FiniteProbabilityWeights Y) (μ : Measure X) (f : Y → X → ℂ)
    (hf : ∀ y, Integrable (f y) μ) :
    law.complexMean (fun y => ∫ x, f y x ∂μ) =
      ∫ x, law.complexMean (fun y => f y x) ∂μ := by
  simp only [complexMean]
  rw [integral_finsetSum _ (fun y _ => (hf y).const_mul _)]
  simp only [integral_const_mul]

theorem mean_density_test_integral {Y X : Type*} [Fintype Y] [MeasurableSpace X]
    (law : FiniteProbabilityWeights Y) (μ : Measure X) (g : Y → X → ℝ)
    (hgi : ∀ y, Integrable (g y) μ)
    (φ : X → ℂ) (hφ : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1) :
    law.complexMean (fun y => ∫ x, (g y x : ℂ) * φ x ∂μ) =
      ∫ x, (law.mean (fun y => g y x) : ℂ) * φ x ∂μ := by
  refine (law.complexMean_integral μ _ (fun y =>
    (hgi y).ofReal.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb))).trans ?_
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x =>
    law.complexMean_ofReal_mul (fun y => g y x) (φ x)))

end FiniteProbabilityWeights
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedCoefficientSampler
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedCoefficientSource_probability :
    IsProbabilityMeasure (allocatedCoefficientSource B U b hR hσ S) := by
  let : ∀ j, IsProbabilityMeasure (mixedScalarArrayLaw (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j)) :=
    fun j => mixedScalarArrayLaw_probability _ _ (allocatedLayerWidths_pos B U b hR hσ S j) _
  exact Measure.pi.instIsProbabilityMeasure _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedProgressionDensityIdentity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] in
theorem CoefficientDeckDensityLaw.test_integral
    (source : Measure (CoefficientSamplerArrays (K := K) I n))
    (density : CoefficientTorus (K := K) U → ℝ) (d : ℕ) [NeZero d]
    (hlaw : CoefficientDeckDensityLaw U bW b hb o μ source density d)
    (φ : CoefficientTorus (K := K) U → ℂ) (hφ : Measurable φ) :
    (∫ p : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d,
      φ (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)
      ∂source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure) =
      ∫ z, φ z ∂realDensityMeasure μ (fun z => density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d z)) := by
  have h := (integral_map (μ := source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure)
    (canonicalCoefficientDeckSample_measurable U bW b hb o d).aemeasurable hφ.aestronglyMeasurable).symm
  exact h.trans (congrArg (fun ν => ∫ z, φ z ∂ν) hlaw)

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] in
theorem CoefficientDeckDensityLaw.mapped_test_integral
    (source : Measure (CoefficientSamplerArrays (K := K) I n))
    (density : CoefficientTorus (K := K) U → ℝ) (d : ℕ) [NeZero d]
    (hlaw : CoefficientDeckDensityLaw U bW b hb o μ source density d)
    {Y : Type*} [MeasurableSpace Y] (ξ : Measure Y)
    (T : CoefficientTorus (K := K) U → Y) (hT : Measurable T)
    (g : Y → ℝ) (hgm : Measurable g) (hg0 : ∀ y, 0 ≤ g y)
    (hglaw : (realDensityMeasure μ (fun z => density
      (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d z))).map T = realDensityMeasure ξ g)
    (φ : Y → ℂ) (hφ : Measurable φ) :
    (∫ p : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d,
      φ (T (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2))
      ∂source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure) =
      ∫ z, (g z : ℂ) * φ z ∂ξ := by
  have hfirst := hlaw.test_integral U bW b hb o μ source density d (φ ∘ T) (hφ.comp hT)
  have hsecond := (integral_map
    (μ := realDensityMeasure μ (fun z => density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d z)))
    hT.aemeasurable hφ.aestronglyMeasurable).symm
  rw [hglaw] at hsecond
  exact hfirst.trans (hsecond.trans (realDensityMeasure_integral_complex ξ g hgm hg0 φ))

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] in
theorem CoefficientDeckDensityLaw.mean_mapped_test_integral
    (source : Measure (CoefficientSamplerArrays (K := K) I n)) [IsProbabilityMeasure source]
    (density : CoefficientTorus (K := K) U → ℝ) (d : ℕ) [NeZero d]
    (hlaw : CoefficientDeckDensityLaw U bW b hb o μ source density d)
    {Y V : Type*} [MeasurableSpace Y] [Fintype V] (ξ : Measure Y) (law : FiniteProbabilityWeights V)
    (T : V → CoefficientTorus (K := K) U → Y) (hT : ∀ v, Measurable (T v))
    (g : V → Y → ℝ) (hgm : ∀ v, Measurable (g v)) (hg0 : ∀ v y, 0 ≤ g v y)
    (hgi : ∀ v, Integrable (g v) ξ)
    (hglaw : ∀ v, (realDensityMeasure μ (fun z => density
      (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d z))).map (T v) = realDensityMeasure ξ (g v))
    (φ : Y → ℂ) (hφ : Measurable φ) (hφb : ∀ y, ‖φ y‖ ≤ 1) :
    (∫ p : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d,
      law.complexMean (fun v => φ (T v (canonicalCoefficientDeckSample U bW b hb o d
        (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
      ∂source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure) =
      ∫ z, (law.mean (fun v => g v z) : ℂ) * φ z ∂ξ := by
  have hi (v) : Integrable (fun p : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d =>
      φ (T v (canonicalCoefficientDeckSample U bW b hb o d
        (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
      (source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure) :=
    Integrable.of_bound ((hφ.comp (hT v)).comp
      (canonicalCoefficientDeckSample_measurable U bW b hb o d)).aestronglyMeasurable
      1 (Filter.Eventually.of_forall (fun p => hφb _))
  refine (law.complexMean_integral _ _ hi).symm.trans ?_
  have he (v) := CoefficientDeckDensityLaw.mapped_test_integral U bW b hb o μ source density d hlaw ξ
    (T v) (hT v) (g v) (hgm v) (hg0 v) (hglaw v) φ hφ
  exact (congrArg (fun f => law.complexMean f) (funext he)).trans
    (law.mean_density_test_integral ξ g hgi φ hφ hφb)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "ξ" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [DecidableEq G] [∀ index, DecidableEq (B index)] [∀ index, DecidableEq (O index)]
  [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
private theorem allocatedPhysicalCubeJet_measurable
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S)) :
    Measurable (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) :=
  (euclideanCoefficientJetMap_continuous U (wholeRoot y) (wholeDirs y) rows).measurable

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] [∀ j, (ν j).IsAddLeftInvariant]
  [∀ j, IsProbabilityMeasure (ν j)] [DecidableEq G]
  [∀ index, DecidableEq (O index)] in
theorem allocatedProgressionCoveredExpectation_density_s2_oai
    (hdeck : CoefficientDeckDensityLaw U bW basis hb o μ source density d)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U O → ℝ)
    (hgm : ∀ y, Measurable (g y)) (hg0 : ∀ y z, 0 ≤ g y z)
    (hgi : ∀ y, Integrable (g y) ξ)
    (hglaw : ∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
      (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) = realDensityMeasure ξ (g y))
    (φ : EuclideanJetLayers U O → ℂ) (hφ : Measurable φ) (hbφ : ∀ z, ‖φ z‖ ≤ 1) :
    allocatedProgressionCoveredExpectation B U basis hR hσ S rows x Q hb o bW d
      (fun p => φ p.2) H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell =
      ∫ z, ((wholeLaw).mean (fun y => g y z) : ℂ) * φ z ∂ξ := by
  let : IsProbabilityMeasure source := allocatedCoefficientSource_probability B U basis hR hσ S
  rw [allocatedProgressionCoveredExpectation]
  have ht := CoefficientDeckDensityLaw.mean_mapped_test_integral U bW basis hb o μ source density d hdeck ξ wholeLaw
    (fun y => euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows)
    (allocatedPhysicalCubeJet_measurable B U basis S rows x)
    g hgm hg0 hgi hglaw φ hφ hbφ
  refine Eq.trans ?_ ht
  dsimp only
  congr! (transparency := .reducible) 5

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedProgressionCoveredExpectation_density_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.allocatedProgressionCoveredExpectation_density_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
