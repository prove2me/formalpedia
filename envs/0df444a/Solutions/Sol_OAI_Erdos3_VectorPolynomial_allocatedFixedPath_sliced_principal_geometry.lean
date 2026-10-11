-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_principal_geometry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-11T09:49:20.058985+00:00
-- url     : https://prove2.me/submissions/139bcf43-d6b5-45f3-b8a4-b9a29395ca54

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B141

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators

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

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem progression_slice_endpoint_geometry {L step H : ℕ} (c : ℤ)
    (hL : 0 < L) (hstep : 0 < step) (hH : 2 ≤ H) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (hdense : δ * L ≤ ((integerProgressionSupport c (step : ℤ) H).card : ℝ)) :
    let lower := (c : ℝ) / L
    let width := (step : ℝ) * ((H : ℝ) - 1) / L
    0 ≤ lower ∧ δ / 2 ≤ width ∧ |lower| + |width| ≤ 1 ∧
      (step : ℝ) / L ≤ 2 / ((H : ℝ) - 1) := by
  have hbase := hsubset (integerProgressionSupport_point c step H hstep 0 (by omega))
  have hlast := hsubset (integerProgressionSupport_point c step H hstep (H - 1) (by omega))
  have hc : (0 : ℝ) ≤ c := by
    have hh : 0 ≤ c := by simpa using (Finset.mem_Ico.mp hbase).1
    exact_mod_cast hh
  have hh : (c : ℝ) + (step : ℝ) * ((H : ℝ) - 1) < L := by
    have hh := (Finset.mem_Ico.mp hlast).2
    have he : (c : ℝ) + (step : ℝ) * ((H - 1 : ℕ) : ℝ) < L := by exact_mod_cast hh
    simpa only [Nat.cast_sub (by omega : 1 ≤ H), Nat.cast_one] using he
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hstep1 : (1 : ℝ) ≤ step := by exact_mod_cast hstep
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  rw [card_integerProgressionSupport c step H hstep] at hdense
  have hwidth : δ / 2 ≤ (step : ℝ) * ((H : ℝ) - 1) / L := by
    apply (le_div_iff₀ hLp).mpr
    have h1 : (H : ℝ) / 2 ≤ (H : ℝ) - 1 := by linarith
    have h2 : (H : ℝ) - 1 ≤ (step : ℝ) * ((H : ℝ) - 1) := by nlinarith
    nlinarith
  have hw0 : 0 ≤ (step : ℝ) * ((H : ℝ) - 1) / L := (half_pos hδ).le.trans hwidth
  refine ⟨div_nonneg hc hLp.le, hwidth, ?_, ?_⟩
  · rw [abs_of_nonneg (div_nonneg hc hLp.le), abs_of_nonneg hw0, ← add_div]
    exact (div_le_one hLp).mpr hh.le
  · apply (le_div_iff₀ (by linarith : 0 < (H : ℝ) - 1)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hLp).mpr
    linarith

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

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "Active" => {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))

theorem allocatedFixedPath_sliced_principal_geometry
    (stepG : ℕ) (hstepG : 0 < stepG) (H : Input → ℕ) (c : Input → ℤ)
    (hH : ∀ j, 2 ≤ H j) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ)) :
    let lower := fun (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) =>
      (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) =>
      (stepG : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    (∀ a p, δ / 2 ≤ width a p) ∧ (∀ a p, 0 ≤ lower a p) ∧
      (∀ a p, |lower a p| + |width a p| ≤ 1) := by
  intro lower width
  have hg (j : Input) := progression_slice_endpoint_geometry (c j) S.positive hstepG
    (hH j) hδ (hsubset j) (hdense j)
  exact ⟨fun a p => (hg ⟨a, p⟩).2.1, fun a p => (hg ⟨a, p⟩).1,
    fun a p => (hg ⟨a, p⟩).2.2.1⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => Spatial × (Output → ℝ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
variable {Cidx : Type*}
variable (selected : Cidx → Σ j : Fin m, Fin (n j))
variable (hshort : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U basis S.value) j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ}
variable (hV : gridVolume ≠ 0)
variable (test : (Cidx → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      ((Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) → ZMod q) → (((Σ _ : X, Unit ⊕ Empty) → ℝ) × ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℂ)
variable {Kφ : ℝ≥0}
variable (htest : ∀ grid residue, LipschitzWith Kφ (test grid residue))
variable (hbound : ∀ grid residue y, ‖test grid residue y‖ ≤ 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => (Spatial × (Output → ℝ))
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty sides

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
  (allocatedLayerWidths B U basis S j)
  (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable (base : X → ℤ) (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (box : X → ℕ) (hbox : ∀ a, 0 < box a) {τ : ℝ} (hτ : τ ≠ 0)
variable (q : ℕ) [NeZero q] (hm : 0 < m)
variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)

variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)
variable (HG : G → ℕ) (hHG : ∀ g, 2 ≤ HG g) (cG : G → ℤ) (stepG : ℕ)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
  Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (S.value : ℤ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => Spatial × (Output → ℝ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (hm : 0 < m)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ} (hV : gridVolume ≠ 0)

variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G T : Type*} {X : Type} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => Spatial × (Output → ℝ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (hm : 0 < m)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ} (hV : gridVolume ≠ 0)

variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)

local notation "actualActive" => (fun _ : Original => crtPolynomialInputLaw primes exponent
  (fun l => padicValNat (primes l) stepG) hcoprime
  (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l))))

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (radius : ℝ≥0) (hradius0 : 0 < radius) (hradius3 : (3 : ℝ) ≤ radius)
variable (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
variable (chartCap : Fin m → ℝ) (hchartCap : ∀ j, 0 ≤ chartCap j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
  chartCap j * ‖v‖)
variable (hchartBudget : ∀ j, chartCap j * (((Fintype.card (I j) : ℝ) + 1) *
  (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
variable (hVpos : 0 < gridVolume)
variable {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
variable (nativeCoeff : Findex → ℂ) (δnative : ℝ)
variable {Pambient Eprec Rrank M : ℝ} (hPambient : 0 ≤ Pambient) (hEprec : 0 ≤ Eprec)
variable (hX : (Fintype.card X : ℝ) ≤ Pambient)
variable (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ Pambient)
variable (hLip : ((Lip * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal coverCap) : ℝ≥0) : ℝ) ≤ Real.exp Pambient)
variable (hmass : ∑ i, ‖nativeCoeff i‖ ≤ M)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (box i : ℝ))
  Rrank (U j) (nativePoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {D Pdecay δgrid : ℝ} (hD : 0 ≤ D)
variable (hPdecay : ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) + 2 : ℕ) : ℝ) ≤ Pdecay)
variable (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G T : Type*} {X : Type} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => Spatial × (Output → ℝ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (hm : 0 < m)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ} (hV : gridVolume ≠ 0)

variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)

local notation "actualActive" => (fun _ : Original => crtPolynomialInputLaw primes exponent
  (fun l => padicValNat (primes l) stepG) hcoprime
  (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l))))

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (radius : ℝ≥0) (hradius0 : 0 < radius) (hradius3 : (3 : ℝ) ≤ radius)
variable (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
variable (chartCap : Fin m → ℝ) (hchartCap : ∀ j, 0 ≤ chartCap j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
  chartCap j * ‖v‖)
variable (hchartBudget : ∀ j, chartCap j * (((Fintype.card (I j) : ℝ) + 1) *
  (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
variable (hVpos : 0 < gridVolume)
variable {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
variable (nativeCoeff : Findex → ℂ) (δnative : ℝ)
variable {Pambient Eprec Rrank M : ℝ} (hPambient : 0 ≤ Pambient) (hEprec : 0 ≤ Eprec)
variable (hX : (Fintype.card X : ℝ) ≤ Pambient)
variable (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ Pambient)
variable (hLip : ((Lip * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal coverCap) : ℝ≥0) : ℝ) ≤ Real.exp Pambient)
variable (hmass : ∑ i, ‖nativeCoeff i‖ ≤ M)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (box i : ℝ))
  Rrank (U j) (nativePoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {D Pdecay δgrid : ℝ} (hD : 0 ≤ D)
variable (hPdecay : ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) + 2 : ℕ) : ℝ) ≤ Pdecay)
variable (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_principal_geometry.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_principal_geometry.{u_1, u_2, u_3, u_4}
