-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedProductChartIdealApproximation_measurable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-11T14:55:32.451696+00:00
-- url     : https://prove2.me/submissions/7ae8a4af-2079-4566-99ae-b871ac0fc5a5

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B198
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedMaskedSiteChartFactor_measurable

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRecenteredIdealError
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

theorem allocatedProductChartIdealApproximation_measurable {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s v, ‖f k s v‖ ≤ 1) :
    Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) := by
  unfold allocatedProductChartIdealApproximation
  apply Finset.measurable_sum
  intro label _
  apply Finset.measurable_sum
  intro k _
  apply measurable_const.mul
  apply Finset.measurable_prod
  intro s _
  apply (allocatedMaskedSiteChartFactor_measurable B U b S o hb bW d r hr period (label s) (f k s)
    (hf k s) (hf1 k s)).comp
  have hcont : Continuous (fun y : EuclideanJetLayers U rowTypes => coveredRowsSiteValue rowSets U y s) := by
    unfold coveredRowsSiteValue
    fun_prop
  exact hcont.measurable

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period] (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})

variable {K : Type*} [Fintype K] (a : K → ℂ)
variable (f : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (v : X → (Unit ⊕ Fin dim) → ℤ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "r" => allocatedProductIdealSiteRadius (G := G) B rowSets

variable (hR : ∀ j, 0 < R j)

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) *
    (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) * R j)))) ≤ 1 / 4)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (hR : ∀ j, 0 < R j)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q : ℕ) (δ : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin dim)))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


variable (hperiod : ∀ j, integerScalarLattice {t : Finset (Fin dim) // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset (Fin dim) // t ∈ rowSets j} → Finset (Fin dim))).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ rowSets j} → Finset (Fin dim))) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ rowSets j} → Finset (Fin dim))) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ rowSets j} → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ rowSets j} → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable {X : Type*} [Fintype X]
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (stride N : X → ℕ) (hs : ∀ t, 0 < stride t) (hN : ∀ t, 0 < N t)
variable (modulus : ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value) (base : X → ℤ)
variable {W τ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "H" => trimmedSpatialRootScale τ N stride
local notation "T" => trimmedSpatialSlopeScale W τ N stride


end Erdos3.BooleanCubeKernel

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedProductChartIdealApproximation_measurable.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.allocatedProductChartIdealApproximation_measurable.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
