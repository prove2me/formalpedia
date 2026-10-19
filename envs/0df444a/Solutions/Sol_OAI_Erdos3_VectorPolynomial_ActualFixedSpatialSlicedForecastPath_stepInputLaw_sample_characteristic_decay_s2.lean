-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.stepInputLaw_sample_characteristic_decay_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:44:03.001991+00:00
-- url     : https://prove2.me/submissions/9aab6a63-3c13-4838-b51c-f71815141589

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B252
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedForecastPolynomial_crt_decay_of_bad_product_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedRecoveredForecastDecay
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable [∀ j, Fintype (J j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n

omit [Fintype X] [∀ j, Fintype (E j)] in

theorem allocatedRecoveredForecastPolynomial_eq
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hnoise : allocatedReadNoise read = noise) (sample : Sample)
    (hinteger : ∀ j i d, allocatedReadProjection read ⟨j, Sum.inr i⟩ d = (sample j).2 i d) :
    allocatedForecastPolynomial short base noise (allocatedReadDeck read)
      (allocatedOriginalSampleCongruenceProjection B U basis S sample) =
    allocatedForecastPolynomial short base (allocatedReadNoise read) (allocatedReadDeck read)
      (fun j a => allocatedReadProjection read ⟨j,a.val⟩) := by
  rw [hnoise]
  funext output
  rcases output with ⟨j, a | a | a⟩
  · rfl
  · rfl
  · have hi : (sample j).2 a.val = allocatedReadProjection read ⟨j, Sum.inr a.val⟩ :=
      (funext (hinteger j a.val)).symm
    simp only [allocatedForecastPolynomial, allocatedSeparatedCongruencePolynomial,
      allocatedUnconditionedCongruenceIntegerPolynomial, allocatedOriginalSampleCongruenceProjection,
      allocatedCongruenceIntegerEmbedding]
    change MvPolynomial.rename _ (modularBoundedCoefficientPolynomial (j.val + 1)
      ((sample j).2 a.val)) = MvPolynomial.rename _
      (modularBoundedCoefficientPolynomial (j.val + 1)
        (allocatedReadProjection read ⟨j, Sum.inr a.val⟩))
    rw [hi]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedTargetReal
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

namespace ActualFixedSpatialForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.actualPathReferenceNeZero
omit [Fintype Tsp] in
theorem reference_characteristic_decay (hm : 0 < m)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S))
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) ℂ) :
    ‖finiteImageCharacteristic path.referenceInputLaw
      (fun t j => (integerLongPolynomialOutput path.referencePolynomial
        (fun k => (y k.1 k.2 : ℤ)) path.referenceModulus t j : ZMod path.referenceModulus)) χ‖ ≤
      ((path.Rbad * ∏ p : path.primes, p.val ^ path.prescribed p.val : ℕ) : ℝ) ^
        (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
          modularRankChargeFactor m) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ)) := by
  let _ := path.primeNeZero
  exact allocatedForecastPolynomial_crt_decay_of_bad_product_s2
    (allocatedShortAxis (I := I) U b S.value) path.noise (allocatedReadDeck path.read)
    (fun j a => allocatedReadProjection path.read ⟨j,a.val⟩) spatial kernel block
    hm path.primes path.exponent path.prescribed path.prime
    (modularForecastRankConstant m Dmod : ℝ) (Nat.cast_nonneg _) path.Rbad path.hbad
    path.base path.origin (fun k => (y k.1 k.2 : ℤ)) χ

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ActualFixedSpatialSlicedCRTIdentification
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

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.slicedReferenceModulusNeZero
omit [Fintype Tsp] in
theorem referenceInputLaw_eq_step : slice.path.referenceInputLaw = slice.stepInputLaw := by
  have hp : (fun p : slice.path.primes => slice.path.prescribed p.val) =
      (fun p : slice.path.primes => padicValNat p.val slice.step) :=
    funext fun p => slice.prescribed_eq p.val
  have ho : slice.path.origin = (fun (p : slice.path.primes)
      (v : LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B) => ((Sum.elim slice.kernelStart
      (fun a => slice.principalStart ⟨a.1.val,a.2⟩) v : ℤ) :
        ZMod (p.val ^ slice.path.exponent p.val))) :=
    funext fun p => funext fun v => slice.origin_eq p v
  simp only [ActualFixedSpatialForecastPath.referenceInputLaw, stepInputLaw, hp, ho]
  congr 1

omit [Fintype Tsp] in
theorem referencePolynomial_eq_sample : slice.path.referencePolynomial =
    allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
      slice.path.base slice.path.noise (allocatedReadDeck slice.path.read)
      (allocatedOriginalSampleCongruenceProjection B U b S slice.path.sample) := by
  have h := allocatedRecoveredForecastPolynomial_eq B U b S slice.path.base slice.path.noise
    slice.path.read slice.path.readNoise slice.path.sample slice.path.readProjection
  rw [slice.path.readNoise] at h
  exact h.symm

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedDataComparison
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

local instance slicedDecayModulusNeZero_rf10faf_1 : NeZero slice.path.referenceModulus :=
  ⟨slice.path.referenceModulus_pos.ne'⟩
omit [Fintype Tsp] in

theorem stepInputLaw_sample_characteristic_decay_s2_oai (hm : 0 < m)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S))
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod slice.path.referenceModulus) ℂ) :
    ‖finiteImageCharacteristic slice.stepInputLaw
      (fun t j => (integerLongPolynomialOutput
        (allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
          slice.path.base slice.path.noise (allocatedReadDeck slice.path.read)
          (allocatedOriginalSampleCongruenceProjection B U b S slice.path.sample))
        (fun k => (y k.1 k.2 : ℤ)) slice.path.referenceModulus t j :
          ZMod slice.path.referenceModulus)) χ‖ ≤
      ((slice.path.Rbad * ∏ p : slice.path.primes,
        p.val ^ slice.path.prescribed p.val : ℕ) : ℝ) ^
        (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
          modularRankChargeFactor m) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent m
          (modularForecastRankConstant m Dmod : ℝ)) := by
  have h := slice.path.reference_characteristic_decay hm y χ
  rw [slice.referenceInputLaw_eq_step, slice.referencePolynomial_eq_sample] at h
  exact h

end ActualFixedSpatialSlicedForecastPath

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.stepInputLaw_sample_characteristic_decay_s2_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.stepInputLaw_sample_characteristic_decay_s2_oai
