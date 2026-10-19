-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.retainedRecoveredRationalFactor_abs_le_grid_modulus_pow_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:00:13.003926+00:00
-- url     : https://prove2.me/submissions/c61af40b-da0d-4edb-8cdd-fe84bcf99ade

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B247
import Definitions.Def_OAIE3v2B303

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalForecastGridTail
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem rationalOutputDensity_nonneg {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    (b : J → ZMod N) : 0 ≤ rationalOutputDensity p Y N b := by
  unfold rationalOutputDensity finiteImageMass
  exact mul_nonneg (Nat.cast_nonneg _) (p.mean_nonneg (fun _ => by split_ifs <;> norm_num))

theorem rationalInactiveForecast_nonneg {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : 0 ≤ gridVolume) (z : Z) (b : J → ZMod N) :
    0 ≤ rationalInactiveForecast inactive active gridPoint Y N gridVolume z b :=
  mul_nonneg hV (inactive.fiberMean_nonneg gridPoint z _
    (fun i => rationalOutputDensity_nonneg (active i) (Y i) N b))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem rationalOutputDensity_le_modulus_pow
    {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (law : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    (b : J → ZMod N) :
    rationalOutputDensity law Y N b ≤ (N : ℝ) ^ Fintype.card J := by
  have hmass : finiteImageMass law (fun x j => (Y x j : ZMod N)) b ≤ 1 := by
    unfold finiteImageMass
    calc
      _ ≤ law.mean (fun _ => 1) := law.mean_mono (fun _ => by split_ifs <;> norm_num)
      _ = 1 := law.mean_const 1
  unfold rationalOutputDensity
  calc
    _ ≤ (Fintype.card (J → ZMod N) : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg _)
    _ = _ := by simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow, mul_one]

theorem rationalInactiveForecast_le_grid_mass_modulus_pow
    {I A Z J : Type*} [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {volume : ℝ} (hV : 0 ≤ volume) (z : Z) (b : J → ZMod N) :
    rationalInactiveForecast inactive active gridPoint Y N volume z b ≤
      volume * inactive.fiberMean gridPoint z (fun _ => 1) *
        (N : ℝ) ^ Fintype.card J := by
  unfold rationalInactiveForecast FiniteProbabilityWeights.fiberMean
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hV
  unfold FiniteProbabilityWeights.mean
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : gridPoint i = z
  · simp only [hi, ite_true, mul_one]
    exact mul_le_mul_of_nonneg_left
      (rationalOutputDensity_le_modulus_pow (active i) (Y i) N b) (inactive.nonneg i)
  · simp only [hi, ite_false, mul_zero, zero_mul, le_refl]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawRecoveredRationalCardinalityCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rat" => forecastLawRecoveredRationalFactor B U basis S law selected sample x
  active Y N volume hb bW

theorem forecastLawRecoveredRationalFactor_nonneg (hV : 0 ≤ volume)
    (r : X → ZMod N) (β : (Σ j, J j) → ℤ) : 0 ≤ rat r β :=
  rationalInactiveForecast_nonneg _ _ _ _ N hV _ _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualFixedSpatialSlicedRetainedKernelComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.retainedBoundsReferenceNonzero
variable (cutoff : ℕ)
local notation "q" => slice.path.referenceRetainedCRTModulus cutoff
local notation "vol" => (∏ a, (basisAxisScale (b (Sigma.fst (selected a))) (Sigma.snd (selected a)) : ℝ))
local notation "Y" => (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
  (fun k => (z (Prod.fst k) (Prod.snd k) : ℤ)) q t j)

omit [Fintype Tsp] in
theorem retainedRecoveredRationalFactor_nonneg
    (r : X → ZMod q) (β : Fin d → ℤ) :
    0 ≤ slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β :=
  forecastLawRecoveredRationalFactor_nonneg B U b S slice.principalLaw selected
    slice.path.sample slice.path.commonTuple (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff)
    Y q vol hb bW (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
    r (fun a => β (e.symm a))

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedRetainedKernelGridCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rat" => forecastLawRecoveredRationalFactor B U basis S law selected sample x
  active Y N volume hb bW

theorem forecastLawRecoveredRationalFactor_le_grid_modulus_pow
    {Icap : ℝ} (hV : 0 ≤ volume)
    (hgrid : ∀ z : A → ℤ,
      volume * law.fiberMean
        (forecastInactiveFixedOutput B U basis S selected
          (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
        (fun a _ => z a) (fun _ => 1) ≤ Icap)
    (r : X → ZMod N) (β : (Σ j, J j) → ℤ) :
    rat r β ≤ Icap * (N : ℝ) ^ Fintype.card Out := by
  let z : A → ℤ := fun a => forecastRecoveredIntegerLabels U basis hb bW β
    (selected a).1 (Sum.inl (selected a).2)
  exact (rationalInactiveForecast_le_grid_mass_modulus_pow law active
    (forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
    Y N hV (fun a _ => z a) _).trans
      (mul_le_mul_of_nonneg_right (hgrid z) (pow_nonneg (Nat.cast_nonneg N) _))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

local instance instNeZeroNatReferenceRetainedCRTModulusPath_1 (cutoff : ℕ) :
    NeZero (slice.path.referenceRetainedCRTModulus cutoff) :=
  ⟨(slice.path.referenceRetainedCRTModulus_pos cutoff).ne'⟩

local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout
  (allocatedShortAxis (I := I) U b S.value))

variable (cutoff : ℕ)
local notation "q" => slice.path.referenceRetainedCRTModulus cutoff
local notation "vol" => (∏ a, (basisAxisScale (b (Sigma.fst (selected a))) (Sigma.snd (selected a)) : ℝ))
local notation "grid" => forecastInactiveFixedOutput B U b S selected
  (allocatedOriginalSampleInactiveCoefficients B selected slice.path.sample) slice.path.commonTuple
local notation "Y" => (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
  (fun k => (z (Prod.fst k) (Prod.snd k) : ℤ)) q t j)

omit [Fintype Tsp] in

theorem retainedRecoveredRationalFactor_abs_le_grid_modulus_pow_s2_oai
    {Icap : ℝ}
    (hgrid : ∀ z : A → ℤ, vol * slice.principalLaw.fiberMean grid
      (fun a _ => z a) (fun _ => 1) ≤ Icap)
    (r : X → ZMod q) (β : Fin d → ℤ) :
    |slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β| ≤
      Icap * (q : ℝ) ^ Fintype.card Out := by
  rw [abs_of_nonneg (slice.retainedRecoveredRationalFactor_nonneg selected bW hb e cutoff r β)]
  exact forecastLawRecoveredRationalFactor_le_grid_modulus_pow B U b S slice.principalLaw
    selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff) Y q vol hb bW
    (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) hgrid r
    (fun a => β (e.symm a))

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.retainedRecoveredRationalFactor_abs_le_grid_modulus_pow_s2_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.retainedRecoveredRationalFactor_abs_le_grid_modulus_pow_s2_oai
