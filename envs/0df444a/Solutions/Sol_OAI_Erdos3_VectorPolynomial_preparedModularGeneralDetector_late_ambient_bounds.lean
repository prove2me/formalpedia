-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_late_ambient_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-13T05:13:40.089667+00:00
-- url     : https://prove2.me/submissions/701a2974-95e4-4e50-8d6c-d567dcdd1a68

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B199

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRefinedLongJetComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

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
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

omit [∀ j, DecidableEq (O j)] in
theorem allocatedLongJetOutputScale_pos (a : {a // ¬grid a}) :
    0 < allocatedLongJetOutputScale B U basis S (O := O) a := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i => exact zero_lt_one
  | inr i => exact pow_pos (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)) _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable (modulus : ℕ) (hmodulus : 0 < modulus)
variable (r : PrincipalTupleIndex
  (fun a : {a // ¬allocatedGridAxis (I := I) U basis S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus)
variable (hsize : ∀ d, (Fintype.card α+1)*modulus ≤
  principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
    (allocatedPrincipalSides B U basis S) d)

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable (modulus : ℕ) (hmodulus : 0 < modulus)
variable (r : PrincipalTupleIndex
  (fun a : {a // ¬allocatedGridAxis (I := I) U basis S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus)
variable (hsize : ∀ d, (Fintype.card α+1)*modulus ≤
  principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
    (allocatedPrincipalSides B U basis S) d)

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable (kernelModulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod kernelModulus))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedNaturalChartScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*}
variable {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (j : Fin m) (i : Fin (n j))

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

include hR in
theorem allocatedPrincipalGridScale_pos_of_radius : 0 < scale := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (principalProfileSize_pos (hR j) _)
    (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))

include hR in
theorem allocatedPrincipalChartRatio_pos :
    0 < allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i := by
  exact div_pos (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
    (Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U basis hR j i))

include hR in
theorem allocatedPrincipalChartRatio_le :
    allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i ≤
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) / R j := by
  have hN : (0 : ℝ) < scale :=
    Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U basis hR j i)
  have hg : 0 < gamma := principalProfileSize_pos (hR j) _
  have hlow : gamma * (basisAxisScale (basis j) i : ℝ) ≤ scale := Nat.le_ceil _
  calc
    _ ≤ 1 / gamma := (div_le_div_iff₀ hN hg).mpr (by nlinarith)
    _ = _ := by
      unfold principalProfileSize
      field_simp

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedProbabilityGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem allocatedGridAxisScale_bounds (a : {a // grid a}) :
    1 ≤ allocatedGridAxisScale B U b S a ∧
      allocatedGridAxisScale B U b S a ≤ (S.value : ℝ≥0) ^ (layerTailDegree m + 1) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · constructor
    · change (1 : ℝ≥0) ≤ (basisAxisScale (b j) i : ℝ≥0)
      exact_mod_cast Nat.succ_le_of_lt (basisAxisScale_pos (b j) i)
    · change (basisAxisScale (b j) i : ℝ≥0) ≤ _
      change basisAxisScale (b j) i ≤ S.value ^ (layerTailDegree m + 1) at ha
      exact_mod_cast ha

variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)


variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (p : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, PMF (CoefficientJetAxisRow O a.val))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedErrorInterpolation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "longScale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)

theorem allocatedGridJetScale_pos : 0 < allocatedGridJetScale B U b S (O := O) :=
  Finset.prod_pos (fun a _ => pow_pos
    (lt_of_lt_of_le zero_lt_one (by exact_mod_cast (allocatedGridAxisScale_bounds B U b S a).1)) _)

theorem allocatedGridLongJetScale_product :
    allocatedGridJetScale B U b S (O := O) * longScale =
      ∏ j, (∏ i, (basisAxisScale (b j) i : ℝ)) ^ Fintype.card (O j) := by
  let f : LayerSamplerAxis I n → ℝ := fun a =>
    match a with
    | ⟨_, .inl _⟩ => 1
    | ⟨j, .inr i⟩ => (basisAxisScale (b j) i : ℝ) ^ Fintype.card (O j)
  have hg : (∏ a : {a // grid a}, f a.val) = allocatedGridJetScale B U b S (O := O) := by
    apply Finset.prod_congr rfl
    intro a _
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · rfl
  have hl : (∏ a : {a // ¬grid a}, f a.val) = longScale := by
    apply Finset.prod_congr rfl
    intro a _
    rcases a with ⟨⟨j, i | i⟩, ha⟩ <;> rfl
  rw [← hg, ← hl, Fintype.prod_subtype_mul_prod_subtype]
  change (∏ a : Σ j, I j ⊕ Fin (n j), f a) = _
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  rw [Fintype.prod_sum_type]
  simp only [f, Finset.prod_const_one, one_mul, Finset.prod_pow]

theorem allocatedGridLongJetScale_covolume :
    (allocatedGridJetScale B U b S (O := O) * longScale * coveredJetArrayScale (O := O) U)⁻¹ =
      ∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (O j) := by
  rw [allocatedGridLongJetScale_product, coveredJetArrayScale, ← Finset.prod_mul_distrib,
    ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← mul_pow, ← inv_pow, mul_inv_rev, inv_inv, mixedDensityCovolumeRatio, div_eq_mul_inv]

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedActiveGridPlateau
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*}
variable {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α]
variable (rowFamily : (Σ j : Fin m, Fin (n j)) → Finset (Finset α))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}

local notation "ig" => allocatedGridIntegerAxis B U b S

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedGridIntegerAxis_grid (a : gridAxes) :
    allocatedGridAxis (I := I) U b S.value ⟨(ig a).1, Sum.inr (ig a).2⟩ := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact ha


local notation "axisN" => allocatedGridNaturalScale B U b S

include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedGridNaturalScale_pos (a : gridAxes) : 0 < axisN a :=
  allocatedPrincipalGridScale_pos_of_radius B U b hR (ig a).1 (ig a).2

variable (x : G → IntegerScalarCubeBox α S.value)
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable (P ε : ℝ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridGlobal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))


include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype α] [DecidableEq α] in
theorem allocatedFullGridNaturalVolume_pos : 0 < allocatedFullGridNaturalVolume B U b S rowSets :=
  Finset.prod_pos (fun a _ => pow_pos (Nat.cast_pos.mpr (allocatedGridNaturalScale_pos B U b hR S a)) _)

variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (rowSets : Fin m → Finset (Finset α))

omit [DecidableEq α] in
theorem allocatedFullGridNaturalVolume_le_exp
    (hR : ∀ j, 0 < R j) {P L D : ℝ}
    (hP : 0 ≤ P) (hL : 0 ≤ L) (_hD : 0 ≤ D)
    (hRP : ∀ j, R j ≤ Real.exp P) (hSL : (S.value : ℝ) ≤ Real.exp L)
    (hrows : ∀ j, ((rowSets j).card : ℝ) ≤ D) :
    allocatedFullGridNaturalVolume B U b S rowSets ≤
      Real.exp ((Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} : ℝ) *
        (D * (P + ((layerTailDegree m + 1 : ℕ) : ℝ) * L + 1))) := by
  let T := P + ((layerTailDegree m + 1 : ℕ) : ℝ) * L
  have hT : 0 ≤ T := add_nonneg hP (mul_nonneg (Nat.cast_nonneg _) hL)
  have hscale (a : {a // allocatedGridAxis (I := I) U b S.value a}) :
      (allocatedGridNaturalScale B U b S a : ℝ) ≤ Real.exp (T + 1) := by
    let j := (allocatedGridIntegerAxis B U b S a).1
    let i := (allocatedGridIntegerAxis B U b S a).2
    have hbnd : (basisAxisScale (b j) i : ℝ) ≤ Real.exp (((layerTailDegree m + 1 : ℕ) : ℝ) * L) := by
      have hh := allocatedGridIntegerAxis_grid B U b S a
      change basisAxisScale (b j) i ≤ S.value ^ (layerTailDegree m + 1) at hh
      have hh' : (basisAxisScale (b j) i : ℝ) ≤ (S.value : ℝ) ^ (layerTailDegree m + 1) := by exact_mod_cast hh
      exact hh'.trans (by
        simpa only [← Real.exp_nat_mul] using pow_le_pow_left₀ (Nat.cast_nonneg _) hSL (layerTailDegree m + 1))
    have hγ : principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)) ≤ Real.exp P := by
      apply le_trans _ (hRP j)
      unfold principalProfileSize
      apply div_le_self (hR j).le
      have hh := Nat.cast_nonneg (α := ℝ) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
      linarith
    have hp : 0 ≤ principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)) *
        (basisAxisScale (b j) i : ℝ) :=
      mul_nonneg (principalProfileSize_pos (hR j) _).le (Nat.cast_nonneg _)
    have hc := (Nat.ceil_lt_add_one hp).le
    have hprod := mul_le_mul hγ hbnd (Nat.cast_nonneg _) (Real.exp_nonneg P)
    rw [← Real.exp_add] at hprod
    have hN : (allocatedGridNaturalScale B U b S a : ℝ) ≤ Real.exp T + 1 :=
      hc.trans (add_le_add hprod le_rfl)
    have h1 : 1 ≤ Real.exp T := Real.one_le_exp hT
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp T + 1 := hN
      _ ≤ Real.exp T * 2 := by linarith
      _ ≤ Real.exp T * Real.exp 1 := mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  unfold allocatedFullGridNaturalVolume
  calc
    _ ≤ ∏ a : {a // allocatedGridAxis (I := I) U b S.value a}, Real.exp (D * (T + 1)) := by
      apply Finset.prod_le_prod (fun a _ => pow_nonneg (Nat.cast_nonneg _) _)
      intro a _
      apply (pow_le_pow_left₀ (Nat.cast_nonneg _) (hscale a) _).trans
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (hrows _) (by linarith)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
      rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))


variable {D : ℝ} (hd : AllocatedComparisonDimensions (G := G) B α (fun j : Fin m => (rowSets j : Type uα)) D)

variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))


variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

variable (x : G → IntegerScalarCubeBox α S.value)

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{uα,uα} (Finset α))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (q : ℕ)


variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (e : {a // allocatedGridAxis (I := I) U b S.value a} →
  ScalarSiteExpansion.{uα,uα} (Finset α))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (T : Fin m → ℝ)
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (T : Fin m → ℝ)
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalNormalizer
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (rowSets : Fin m → Finset (Finset α))


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
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "single" => (fun _ : Fin m => Unit)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

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
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "single" => (fun _ : Fin m => Unit)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

section Extraction

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable (rowSets : Fin m → Finset (Finset α)) (d : ℕ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [NeZero d]


end Extraction

section Cutoff

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "single" => (fun _ : Fin m => Unit)


variable (hrow : ∀ j, Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j))) ≤ 1 / 4)

end Cutoff
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

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "naturalVolume" => allocatedFullGridNaturalVolume B U b S rowSets
local notation "gridScale" => allocatedGridJetScale B U b S (O := rowTypes)
local notation "longScale" => (∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)
local notation "radiusVolume" => (∏ t : (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a))), R (Sigma.fst (Subtype.val (Sigma.fst t))))

omit [Fintype α] [DecidableEq α] in
theorem allocatedGridJetScale_natural_ratio :
    gridScale / naturalVolume = ∏ a : {a // grid a},
      (allocatedPrincipalChartRatio (G := G) B U b (R := R) (ig a).1 (ig a).2) ^
        Fintype.card (rowTypes a.val.1) := by
  unfold allocatedGridJetScale allocatedFullGridNaturalVolume
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · simp only [allocatedGridAxisScale, allocatedGridNaturalScale, allocatedGridIntegerAxis,
      allocatedPrincipalChartRatio, Fintype.card_coe, div_pow, NNReal.coe_natCast]
    norm_cast

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hR : ∀ j, 0 < R j)

omit [Fintype α] [DecidableEq α] in
include hR in
theorem allocatedProductIdealNormalizer_pos :
    0 < allocatedProductIdealNormalizer B U b S rowSets := by
  exact mul_pos (mul_pos (mul_pos (allocatedFullGridNaturalVolume_pos B U b hR S rowSets)
    (coveredJetArrayScale_pos U))
    (Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)))
    (Finset.prod_pos (fun t _ => hR (Sigma.fst (Subtype.val (Sigma.fst t)))))

omit [Fintype α] [DecidableEq α] in
include hR in
theorem allocatedProductIdealNormalizer_inv_eq :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ =
      (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (rowTypes j)) *
      (∏ a : {a // grid a},
        allocatedPrincipalChartRatio (G := G) B U b (R := R) (ig a).1 (ig a).2 ^
          Fintype.card (rowTypes a.val.1)) * radiusVolume⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg
    (allocatedProductIdealNormalizer_pos B U b S rowSets hR).le]
  rw [← allocatedGridJetScale_natural_ratio B U b S rowSets,
    ← allocatedGridLongJetScale_covolume B U b S (O := rowTypes)]
  have hg := (allocatedGridJetScale_pos B U b S (O := rowTypes)).ne'
  have hn := (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).ne'
  have hl : longScale ≠ 0 := (Finset.prod_pos
    (fun a _ => allocatedLongJetOutputScale_pos B U b S a)).ne'
  have hc := (coveredJetArrayScale_pos (O := rowTypes) U).ne'
  have hr : radiusVolume ≠ 0 := (Finset.prod_pos (fun t _ => hR (Sigma.fst (Subtype.val (Sigma.fst t))))).ne'
  unfold allocatedProductIdealNormalizer
  field_simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "radiusVolume" => (∏ t : (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a))), R (Sigma.fst (Subtype.val (Sigma.fst t))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hR : ∀ j, 0 < R j)

omit [Fintype α] [DecidableEq α] in
include hR in
theorem allocatedProductIdealNormalizer_inv_le (V : Fin m → ℝ)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {Q κ : ℝ} (hQ : 1 ≤ Q) (hκ0 : 0 ≤ κ) (hκ : ∀ j, (R j)⁻¹ ≤ κ)
    (hslots : ∀ j i, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) ≤ Q) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤
      (∏ j, V j ^ Fintype.card (rowTypes j)) *
        (Q * κ) ^ Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)) := by
  have hV0 (j) : 0 ≤ V j := (mixedDensityCovolumeRatio_pos (euclideanSubspace (U j)) (b j)).le.trans (hV j)
  have hbase : 0 ≤ Q * κ := mul_nonneg (zero_le_one.trans hQ) hκ0
  have hg0 : 0 ≤ ∏ a : {a // grid a},
      allocatedPrincipalChartRatio (G := G) B U b (R := R) (ig a).1 (ig a).2 ^
        Fintype.card (rowTypes a.val.1) :=
    Finset.prod_nonneg (fun a _ => pow_nonneg (allocatedPrincipalChartRatio_pos B U b hR _ _).le _)
  have hl0 : 0 ≤ radiusVolume⁻¹ := inv_nonneg.mpr (Finset.prod_nonneg (fun t _ => (hR (Sigma.fst (Subtype.val (Sigma.fst t)))).le))
  have hgrid : (∏ a : {a // grid a},
      allocatedPrincipalChartRatio (G := G) B U b (R := R) (ig a).1 (ig a).2 ^
        Fintype.card (rowTypes a.val.1)) ≤
      ∏ a : {a // grid a}, (Q * κ) ^ Fintype.card (rowTypes a.val.1) := by
    apply Finset.prod_le_prod
    · intro a _
      exact pow_nonneg (allocatedPrincipalChartRatio_pos B U b hR _ _).le _
    · intro a _
      apply pow_le_pow_left₀ (allocatedPrincipalChartRatio_pos B U b hR _ _).le
      apply (allocatedPrincipalChartRatio_le B U b hR _ _).trans
      rw [div_eq_mul_inv]
      exact mul_le_mul (hslots _ _) (hκ _) (inv_nonneg.mpr (hR _).le) (zero_le_one.trans hQ)
  have hlong : radiusVolume⁻¹ ≤
      ∏ a : {a // ¬grid a}, (Q * κ) ^ Fintype.card (rowTypes a.val.1) := by
    simp only [Fintype.prod_sigma, Finset.prod_const, Finset.card_univ, ← Finset.prod_inv_distrib, ← inv_pow]
    apply Finset.prod_le_prod
    · intro a _
      exact pow_nonneg (inv_nonneg.mpr (hR a.val.1).le) _
    · intro a _
      apply pow_le_pow_left₀ (inv_nonneg.mpr (hR a.val.1).le)
      exact (hκ a.val.1).trans (le_mul_of_one_le_left hκ0 hQ)
  have hcov : (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^
      Fintype.card (rowTypes j)) ≤ ∏ j, V j ^ Fintype.card (rowTypes j) := by
    apply Finset.prod_le_prod
    · intro j _
      exact pow_nonneg (mixedDensityCovolumeRatio_pos (euclideanSubspace (U j)) (b j)).le _
    · intro j _
      exact pow_le_pow_left₀ (mixedDensityCovolumeRatio_pos (euclideanSubspace (U j)) (b j)).le (hV j) _
  rw [allocatedProductIdealNormalizer_inv_eq B U b S rowSets hR, mul_assoc]
  calc
    _ ≤ (∏ j, V j ^ Fintype.card (rowTypes j)) *
        ((∏ a : {a // grid a}, (Q * κ) ^ Fintype.card (rowTypes a.val.1)) *
          ∏ a : {a // ¬grid a}, (Q * κ) ^ Fintype.card (rowTypes a.val.1)) :=
      mul_le_mul hcov
        (mul_le_mul hgrid hlong hl0 (Finset.prod_nonneg (fun a _ => pow_nonneg hbase _)))
        (mul_nonneg hg0 hl0) (Finset.prod_nonneg (fun j _ => pow_nonneg (hV0 j) _))
    _ = _ := by
      rw [Fintype.prod_subtype_mul_prod_subtype grid
        (fun a : LayerSamplerAxis I n => (Q * κ) ^ Fintype.card (rowTypes a.1)),
        Finset.prod_pow_eq_pow_sum, Fintype.card_sigma]

omit [Fintype α] [DecidableEq α] in
include hR in
theorem allocatedProductIdealNormalizer_inv_le_exp {P : ℝ} (hP : 0 ≤ P)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P)
    (hκ : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hslots : ∀ j i, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) ≤ Real.exp P) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤
      Real.exp (((∑ j, Fintype.card (rowTypes j) : ℕ) : ℝ) * P +
        (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)) : ℝ) * (2 * P)) := by
  have h := allocatedProductIdealNormalizer_inv_le B U b S rowSets hR (fun _ => Real.exp P) hV
    (Real.one_le_exp hP) (Real.exp_pos P).le hκ hslots
  apply h.trans_eq
  simp only [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCanonicalBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

omit [DecidableEq α] in
theorem allocatedIdealNormalizer_row_counts {P : ℝ} (hP : 0 ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P) :
    ((∑ j, Fintype.card (rowTypes j) : ℕ) : ℝ) ≤ m * (2 : ℝ) ^ Fintype.card α ∧
      (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)) : ℝ) ≤
        (m * (2 : ℝ) ^ Fintype.card α) * (2 * P) := by
  have hrow (j : Fin m) : (Fintype.card (rowTypes j) : ℝ) ≤ (2 : ℝ) ^ Fintype.card α := by
    have h := Finset.card_le_univ (rowSets j)
    rw [Fintype.card_finset] at h
    rw [Fintype.card_coe]
    exact_mod_cast h
  constructor
  · push_cast
    calc
      _ ≤ ∑ _j : Fin m, (2 : ℝ) ^ Fintype.card α := Finset.sum_le_sum (fun j _ => hrow j)
      _ = _ := by simp
  · have hcount : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)) : ℝ) =
        ∑ j, ((Fintype.card (I j) : ℝ) + n j) * Fintype.card (rowTypes j) := by
      simp only [Fintype.card_sigma, Fintype.sum_sigma, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro j _
      change (∑ _a : I j ⊕ Fin (n j), (Fintype.card (rowTypes j) : ℝ)) = _
      simp
    rw [hcount]
    calc
      _ ≤ ∑ _j : Fin m, (2 * P) * (2 : ℝ) ^ Fintype.card α := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul (by linarith [hI j, hn j]) (hrow j) (Nat.cast_nonneg _) (by positivity)
      _ = _ := by simp; ring

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [DecidableEq α] in
theorem allocatedProductIdealNormalizer_early_budget
    (hR : ∀ j, 0 < R j) {P : ℝ} (hP0 : 0 ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤
      Real.exp ((m * (2 : ℝ) ^ Fintype.card α) * (P + 8) * (1 + 4 * P)) := by
  have hP8 : 0 ≤ P + 8 := by linarith [hP0]
  have hP : P ≤ P + 8 := by linarith
  have hslots (j : Fin m) (i : Fin (n j)) :
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) ≤ Real.exp (P + 8) := by
    have hc : (Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) ≤ P :=
      (Nat.cast_le.mpr (Finset.card_le_univ _)).trans (hcoeff j)
    have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    calc
      _ ≤ 8 * (P + 1) := by linarith
      _ ≤ Real.exp 8 * Real.exp P := mul_le_mul h8 (Real.add_one_le_exp P)
        (by linarith [hP0]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h := allocatedProductIdealNormalizer_inv_le_exp B U b S rowSets hR hP8
    (fun j => (hV j).trans (Real.exp_le_exp.mpr hP))
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hP)) hslots
  have hc := allocatedIdealNormalizer_row_counts (I := I) (n := n) rowSets
    hP0 hI hn
  apply h.trans (Real.exp_le_exp.mpr ?_)
  calc
    _ ≤ (m * (2 : ℝ) ^ Fintype.card α) * (P + 8) +
        ((m * (2 : ℝ) ^ Fintype.card α) * (2 * P)) * (2 * (P + 8)) :=
      add_le_add (mul_le_mul_of_nonneg_right hc.1 hP8)
        (mul_le_mul_of_nonneg_right hc.2 (by positivity))
    _ = _ := by ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (E : Fin m → Type*) [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (hR : ∀ j, 0 < R j) (C V : Fin m → ℝ≥0) {Pnum : ℝ}
variable (hnum : AllocatedSourceNumerics B U b S C V Pnum)
variable (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hR hnum hV

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (E : Fin m → Type*) [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (hR : ∀ j, 0 < R j) {Pnum : ℝ} (hPnum : 0 ≤ Pnum)
variable (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum) (hn : ∀ j, (n j : ℝ) ≤ Pnum)
variable (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
variable (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
variable (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pnum)

include hR hPnum hI hn hcoeff hRi hV

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

section CoverParameter

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

end CoverParameter

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineSourceAccuracy
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem allocatedRowSlicedSiteRadius_buffer_le_exp (rowSets : Fin m → Finset (Finset α)) :
    2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤
      Real.exp (((m : ℝ) + 2) * Fintype.card α + m + 4) := by
  let A : ℝ := ((m : ℝ) + 2) * Fintype.card α + 3
  have hT : 0 ≤ partitionedIdealRadius α m + 1 := by
    have := partitionedIdealRadius_nonneg α m
    positivity
  have hr : (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ 1 + m * idealSiteBoxRadius α m := by
    change 1 + ∑ j : Fin m, (rowSets j).card * (partitionedIdealRadius α m + 1) ≤ _
    apply add_le_add_right
    calc
      _ ≤ ∑ _j : Fin m, idealSiteBoxRadius α m := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right _ hT
        exact_mod_cast (Finset.card_le_univ (rowSets j)).trans_eq (Fintype.card_finset (α := α))
      _ = _ := by simp
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hone : 1 ≤ Real.exp A := Real.one_le_exp_iff.mpr hA
  calc
    _ ≤ 2 + m * (2 * idealSiteBoxRadius α m) := by nlinarith only [hr]
    _ ≤ 2 + m * Real.exp A := by
      gcongr
      exact idealSiteBoxRadius_buffer_le_exp α m
    _ ≤ ((m : ℝ) + 2) * Real.exp A := by nlinarith only [hone]
    _ ≤ Real.exp ((m : ℝ) + 1) * Real.exp A := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      simpa only [add_assoc, one_add_one_eq_two] using Real.add_one_le_exp ((m : ℝ) + 1)
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [A]; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (E : Fin m → Type*) [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable (hR : ∀ j, 0 < R j) {Pnum : ℝ} (hPnum : 0 ≤ Pnum)
variable (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum) (hn : ∀ j, (n j : ℝ) ≤ Pnum)
variable (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
variable (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
variable (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pnum)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorGeometricBoundsGeneral
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem preparedModularGeneralDetector_grid_axes {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) :
    (Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} : ℝ) ≤ D :=
  (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hdim.axes

theorem preparedModularGeneralDetector_natural_volume {P D : ℝ}
    (hP : 0 ≤ P) (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hDP : D ≤ P) (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hS : (S.value : ℝ) ≤ Real.exp P) :
    allocatedFullGridNaturalVolume B U b S rowSets ≤
      Real.exp (P ^ 2 * (((layerTailDegree m + 1 : ℕ) : ℝ) * P + 1)) := by
  have hrow (j : Fin m) : ((rowSets j).card : ℝ) ≤ P := by
    have hr : ((rowSets j).card : ℝ) ≤ D := by
      simpa only [Fintype.card_coe] using hdim.rows j
    exact hr.trans hDP
  have hvol := allocatedFullGridNaturalVolume_le_exp B U b S rowSets hR
    (P := 0) (L := P) (D := P) (by norm_num) hP hP
    (fun j => by simpa only [Real.exp_zero] using hRone j) hS hrow
  apply hvol.trans (Real.exp_le_exp.mpr ?_)
  have hgrid := (preparedModularGeneralDetector_grid_axes B rowSets U b S hdim).trans hDP
  calc
    _ ≤ P * (P * (0 + ((layerTailDegree m + 1 : ℕ) : ℝ) * P + 1)) :=
      mul_le_mul_of_nonneg_right hgrid (by positivity)
    _ = _ := by ring

theorem preparedModularGeneralDetector_site_radius {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hDP : D ≤ P) :
    2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp (2 * P ^ 2 + 8) := by
  apply (allocatedRowSlicedSiteRadius_buffer_le_exp rowSets).trans
  apply Real.exp_le_exp.mpr
  simp only [Fintype.card_fin]
  have hmP : (m : ℝ) ≤ P := hdim.degree.trans hDP
  have hdP : (dim : ℝ) ≤ P := by simpa only [Fintype.card_fin] using hdim.cube.trans hDP
  have hprod := mul_le_mul hmP hdP (Nat.cast_nonneg dim) (hdim.nonneg.trans hDP)
  nlinarith only [hprod, hmP, hdP, sq_nonneg (P - 3 / 2)]

theorem preparedModularGeneralDetector_chart_sum (C : Fin m → ℝ≥0) {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hDP : D ≤ P) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp P) :
    ((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp (3 * P) := by
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  have hPexp : P ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  have hmexp : (m : ℝ) ≤ Real.exp P := hdim.degree.trans (hDP.trans hPexp)
  push_cast
  calc
    _ ≤ ∑ _j : Fin m, Real.exp P * P := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul (hC j) (hJ j) (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = (m : ℝ) * (Real.exp P * P) := by simp
    _ ≤ Real.exp P * (Real.exp P * Real.exp P) := mul_le_mul hmexp
      (mul_le_mul_of_nonneg_left hPexp (Real.exp_nonneg _)) (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularCanonicalDetectorAmbientConsumer
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin 1)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)


variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem preparedModularGeneralDetector_early_normalizer {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) (hDP : D ≤ P)
    (hR : ∀ j, 0 < R j) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤
      Real.exp ((m * (2 : ℝ) ^ dim) * (P + 8) * (1 + 4 * P)) := by
  obtain ⟨hI, hn⟩ := preparedModularGeneralDetector_layer_axes B rowSets hdim
  simpa only [Fintype.card_fin] using
    allocatedProductIdealNormalizer_early_budget B U b S rowSets hR (hdim.nonneg.trans hDP)
      (fun j => (hI j).trans hDP) (fun j => (hn j).trans hDP)
      (fun j => (hdim.coefficients j).trans hDP) hRi hV

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem preparedModularGeneralDetector_late_ambient_bounds
    (K : PreparedModularCanonicalDetectorResourceConstants) (hm : K.m = m) {P L D : ℝ}
    (hPL : P ≤ L)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D) (hDP : D ≤ P)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hS : (S.value : ℝ) ≤ Real.exp L)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P)
    (hforward : ∀ j, (Cforward j : ℝ) ≤ Real.exp P) (hK : (Ksource : ℝ) ≤ Real.exp P)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp P) :
    PreparedModularGeneralLateAmbientBounds B rowSets U b S Cforward Ksource
      (preparedModularGeneralDetectorResources K dim P L) := by
  let r := preparedModularGeneralDetectorResources K dim P L
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  have hL : 0 ≤ L := hP.trans hPL
  have hb := ((Classical.choose_spec (exists_preparedModularGeneralDetector_resource_budget K dim)).2 hP hPL).1
  have htail : 0 ≤ ((layerTailDegree K.m + 1 : ℕ) : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hL
  have hconst : (0 : ℝ) ≤ comparisonProfileBound := Nat.cast_nonneg _
  have hsites0 : (0 : ℝ) ≤ (2 ^ dim : ℕ) := Nat.cast_nonneg _
  have hbase : r.baseAmbient = r.Pproj + r.coverLog + r.Vlog + r.Nlog + r.Q +
      (layerTailDegree K.m + 1 : ℕ) * L + 3 * P + comparisonProfileBound + (2 ^ dim : ℕ) + 32 := rfl
  have hPbase : P ≤ r.baseAmbient := by
    linarith only [hbase, hb.Pproj.1, hb.coverLog.1, hb.Vlog.1, hb.Nlog.1, hb.Q.1, htail, hP, hconst, hsites0]
  have h3Pbase : 3 * P ≤ r.baseAmbient := by
    linarith only [hbase, hb.Pproj.1, hb.coverLog.1, hb.Vlog.1, hb.Nlog.1, hb.Q.1, htail, hconst, hsites0]
  have h2Pbase : 2 * P ≤ r.baseAmbient := (by linarith only [hP] : 2 * P ≤ 3 * P).trans h3Pbase
  have hvol : allocatedFullGridNaturalVolume B U b S rowSets ≤ Real.exp r.Vlog := by
    simpa only [r, preparedModularGeneralDetectorResources, hm] using
      preparedModularGeneralDetector_natural_volume B rowSets U b S hL hdim (hDP.trans hPL) hR hRone hS
  have hnorm : ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp r.Nlog := by
    simpa only [r, preparedModularGeneralDetectorResources, hm, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      preparedModularGeneralDetector_early_normalizer B rowSets U b S hdim hDP hR hRi hV
  have hrows : ((∑ j, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp (2 * P) := by
    have hPexp : P ≤ Real.exp P := by linarith only [Real.add_one_le_exp P]
    have hmexp : (m : ℝ) ≤ Real.exp P := hdim.degree.trans (hDP.trans hPexp)
    push_cast
    calc
      _ ≤ ∑ _j : Fin m, P := Finset.sum_le_sum (fun j _ => by
        simpa only [Fintype.card_coe] using (hdim.rows j).trans hDP)
      _ = (m : ℝ) * P := by simp
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hmexp hPexp hP (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp r.baseAmbient := by
    have hlog : ((layerTailDegree m + 1 : ℕ) : ℝ) * L ≤ r.baseAmbient := by
      rw [← hm]
      linarith only [hbase, hb.Pproj.1, hb.coverLog.1, hb.Vlog.1, hb.Nlog.1, hb.Q.1, hP, hconst, hsites0]
    calc
      _ ≤ (Real.exp L) ^ (layerTailDegree m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hS _
      _ = Real.exp (((layerTailDegree m + 1 : ℕ) : ℝ) * L) := by rw [← Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  refine {
    hPbox := hb.Pbox.1
    hVlog := hb.Vlog.1
    hNlog := hb.Nlog.1
    hbox := preparedModularGeneralDetector_site_radius B rowSets hdim hDP
    hvolume := hvol
    hnormalizer := hnorm
    hbaseAmbient := hb.baseAmbient.1
    hvbase := ?_
    hnbase := ?_
    hsites := ?_
    haxes := hdim.axes.trans (hDP.trans hPbase)
    hKbase := hK.trans (Real.exp_le_exp.mpr hPbase)
    hcoords := (preparedModularGeneralDetector_chart_sum B rowSets Cforward hdim hDP hJ hforward).trans (Real.exp_le_exp.mpr h3Pbase)
    hcutoff := hcutoff.trans (Real.exp_le_exp.mpr hPbase)
    hrowsAmbient := hrows.trans (Real.exp_le_exp.mpr h2Pbase)
    houtputs := hdim.outputs.trans (hDP.trans hPbase)
    hheight := hheight }
  · linarith only [hbase, hb.Pproj.1, hb.coverLog.1, hb.Nlog.1, hb.Q.1, htail, hP, hconst, hsites0]
  · linarith only [hbase, hb.Pproj.1, hb.coverLog.1, hb.Vlog.1, hb.Q.1, htail, hP, hconst, hsites0]
  · simp only [Fintype.card_finset, Fintype.card_fin]
    linarith only [hbase, hb.Pproj.1, hb.coverLog.1, hb.Vlog.1, hb.Nlog.1, hb.Q.1, htail, hP, hconst]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable {P : ℝ}

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_late_ambient_bounds.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_late_ambient_bounds.{u_1, u_2, u_3, u_4}
