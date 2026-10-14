-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_jointResidueOutput_eq_congruence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-11T13:39:26.733331+00:00
-- url     : https://prove2.me/submissions/bd4023b5-3979-4c1d-b37d-a4380c791533

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B171
import Definitions.Def_OAIErdos3B173

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

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem boundedCoefficientJetMatrix_empty {α K : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ)
    (e : VectorPolynomial.BoundedCoefficientExponent K h) :
    boundedCoefficientJetMatrix root D h (fun _ : Unit => ∅) () e =
      VectorPolynomial.boundedSiteMatrix h (fun _ : Unit => root) () e := by
  simp [boundedCoefficientJetMatrix, boundedDegreeIntegerJetMatrix,
    boundedCoefficientIntegerExponentEquiv, integerJetMatrix, booleanCoefficient,
    integerAffineCube, VectorPolynomial.boundedSiteMatrix, MvPolynomial.eval_monomial]

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S))

theorem allocatedOriginalSamplePhysicalMixedValue_integer (j : Fin m) (i : Fin (n j)) :
    (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j).2 i =
      MvPolynomial.eval (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (∑ d, MvPolynomial.monomial d.val ((sample j).2 i d)) := by
  simp only [map_sum, MvPolynomial.eval_monomial, Finsupp.prod]
  change (∑ d, boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (j.val + 1) (fun _ : Unit => ∅) () d * (sample j).2 i d) = _
  apply Finset.sum_congr rfl
  intro d _
  rw [boundedCoefficientJetMatrix_empty]
  exact mul_comm _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X K : Type*} [Fintype X] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3
open scoped BigOperators Classical

namespace VectorPolynomial
open Module
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S))


end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)]
variable [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]


namespace NormalizedPolynomialTwist

variable {X : Type*} [Fintype X] {periodCap coverCap : ℝ} {L : ℝ≥0}

end NormalizedPolynomialTwist

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped Classical NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable [CompactSpace (EuclideanJetLayers U (fun _ => Unit))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]


namespace NormalizedPolynomialTwist

variable {X : Type*} [Fintype X] {periodCap coverCap : ℝ} {L : ℝ≥0}

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpatialMatrixBlockWideProbability
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

theorem spatialRankPolynomial_actual_eval {K X : Type*} [Fintype K]
    (base : X → ℤ) (noise : Option K × X → ℤ) (x : X) (t : K → ℤ) :
    MvPolynomial.eval t (C (base x) + spatialRankPolynomial (fun e => noise (e,x))) =
      BooleanCubeKernel.jointIntegerPhysicalSite t (base, noise) x := by
  rw [spatialRankPolynomial_eq]
  simp only [map_add, eval_C, map_sum, map_mul, eval_X]
  simp only [BooleanCubeKernel.jointIntegerPhysicalSite, Pi.add_apply,
    BooleanCubeKernel.integerPhysicalSite]
  congr 1
  simp only [mul_comm]

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G A R : Type*} {B : D → Type*} [CommRing R]

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

end VectorPolynomial
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

open _root_.MvPolynomial
open scoped BigOperators

variable {K J R : Type*} [Fintype K] [CommRing R]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open BooleanCubeKernel

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {G P X : Type*} [Fintype G] [Fintype P] [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {G P : Type*} [Fintype G] [Fintype P] {n : ℕ}

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineFixedPathRationalReference
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V Short Out : Type*} [Fintype L] [Fintype V]
  [Fintype Out] [DecidableEq Out]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (start : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < (allocatedPrincipalSides B U basis S) j)
variable (hH : ∀ j, 0 < H j)

variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)

variable {Ω Out : Type*} [Fintype Ω] [Fintype Out] [DecidableEq Out]
variable (active : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) → FiniteProbabilityWeights Ω) (Y : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) → Ω → Out → ℤ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "sides" => allocatedPrincipalSides B U basis S

variable (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (deck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis short j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)

theorem allocatedJointResidueOutput_actual
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (q : ℕ)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (v : PrincipalIntegerTuples B degree Empty sides) :
    allocatedJointResidueOutput B U basis S base noise deck projection q
        (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q v) =
      fun o => ((MvPolynomial.eval (Sum.elim (fun g => (x g none : ℤ))
        (fun j => (v j none : ℤ)))
        (allocatedUnconditionedCongruenceIntegerPolynomial short o.1 base noise deck
          (projection o.1) o.2) : ℤ) : ZMod q) := by
  funext o
  rw [integerPolynomial_eval_residue]
  unfold allocatedJointResidueOutput allocatedForecastPolynomial allocatedSeparatedCongruencePolynomial
  rw [MvPolynomial.eval₂_rename]
  congr 1
  funext k
  cases k with
  | inl g => rfl
  | inr j =>
    by_cases hj : short j.1
    · simp only [Function.comp_apply, samplerSeparatedVariable_inactive short degree _ _ _ hj,
        Sum.elim_inr, principalResidueLabel]
      rfl
    · simp only [Function.comp_apply, samplerSeparatedVariable_active short degree _ _ _ hj,
        Sum.elim_inl, Sum.elim_inr, principalResidueLabel]
      rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n

variable (H parameterStep : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (start : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (parameterStep j : ℤ) * t.val ∧
    start j + (parameterStep j : ℤ) * t.val < allocatedPrincipalSides B U basis S j)
variable (hH : ∀ j, 0 < H j)

variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleCongruenceOutput
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical
open BooleanCubeKernel

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedOriginalSample_jointResidueOutput_eq_congruence
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (q : ℕ) (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty sides) :
    allocatedJointResidueOutput B U basis S base noise deck
      (allocatedOriginalSampleCongruenceProjection B U basis S sample) q
      (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q y) =
      fun o => (forecastCongruenceOutput (R := ℤ) short
        (base + integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) noise)
        (fun j => Sum.elim
          (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j).2
          (allocatedOriginalSampleDeckValue B U basis S deck x y j)) o : ZMod q) := by
  rw [allocatedJointResidueOutput_actual]
  have hroot : Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) =
      allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y := by
    funext v
    simp only [allocatedPhysicalCubeRoot, zero_add]
  rw [hroot]
  funext o
  apply congrArg (fun z : ℤ => (z : ZMod q))
  rcases o with ⟨j, a | e | i⟩
  · exact spatialRankPolynomial_actual_eval base noise a.val _
  · rfl
  · change MvPolynomial.eval _ (modularBoundedCoefficientPolynomial _
      ((sample j).2 i.val)) =
      (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j).2 i.val
    exact (allocatedOriginalSamplePhysicalMixedValue_integer B U basis S sample x y j i.val).symm

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_jointResidueOutput_eq_congruence.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_jointResidueOutput_eq_congruence.{u_1, u_2, u_3, u_4, u_5, u_6}
