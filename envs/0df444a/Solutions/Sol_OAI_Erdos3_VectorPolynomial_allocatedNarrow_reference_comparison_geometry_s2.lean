-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedNarrow_reference_comparison_geometry_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:15:46.757969+00:00
-- url     : https://prove2.me/submissions/0815efdb-ba91-4a3e-9008-cdbcaa4acdee

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194
import Definitions.Def_OAIE3v2B195
import Theorems.Thm_OAI_Erdos3_BooleanCubeKernel_referenceJetEnvelopeWidths_trimmed_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialScales
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem trimmedSpatial_scale_lower {X : Type*} {B τ ρ : ℝ}
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (N modulus : X → ℕ) (x : X) (hq : 0 < modulus x)
    (hlarge : 8 * (1 + B) * (modulus x : ℝ) * ρ ≤ τ * (N x : ℝ)) :
    ρ ≤ trimmedSpatialRootScale τ N modulus x ∧ ρ ≤ trimmedSpatialSlopeScale B τ N modulus x := by
  have hq' : (0 : ℝ) < modulus x := by exact_mod_cast hq
  have hb : (0 : ℝ) < 8 * (1 + B) := by positivity
  have hs : ρ ≤ trimmedSpatialSlopeScale B τ N modulus x := by
    unfold trimmedSpatialSlopeScale
    apply (le_div_iff₀ hq').mpr
    apply (le_div_iff₀ hb).mpr
    nlinarith [hlarge]
  refine ⟨?_, hs⟩
  unfold trimmedSpatialRootScale
  apply (le_div_iff₀ hq').mpr
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  nlinarith [mul_nonneg hB (mul_nonneg hq'.le hρ)]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

theorem allocatedPhysicalEntryBudget_one_le : 1 ≤ allocatedPhysicalEntryBudget B U basis S c := by
  have h := allocatedPhysicalRootBudget_nonneg B U basis S c
  unfold allocatedPhysicalEntryBudget
  linarith [Nat.cast_nonneg (α := ℝ) S.value]

omit [Fintype α] in
theorem allocatedPhysicalCube_root_entry_bound (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)| ≤ allocatedPhysicalEntryBudget B U basis S c := by
  apply (allocatedPhysicalCube_root_budget B U basis S c x y k).trans
  unfold allocatedPhysicalEntryBudget
  linarith [Nat.cast_nonneg (α := ℝ) S.value]

omit [Fintype α] in
theorem allocatedPhysicalCube_direction_entry_bound (i : α) (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeDirections B U basis S x y i k : ℝ)| ≤ allocatedPhysicalEntryBudget B U basis S c := by
  apply (allocatedPhysicalCube_directions_bound B U basis S x y i k).trans
  have h := allocatedPhysicalRootBudget_nonneg B U basis S c
  unfold allocatedPhysicalEntryBudget
  linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedWholeResidueShift
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)

local notation "vars" => LayerSamplerVariables G I n B
local notation "sides" => allocatedPrincipalSides B U basis S

omit [Fintype α] [DecidableEq α] in
theorem allocatedPhysicalCube_coefficient_entry_bound
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    (i : Unit ⊕ α) (k : Option vars) :
    |(physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) i k : ℝ)| ≤
        allocatedPhysicalEntryBudget B U basis S c := by
  cases k with
  | none =>
    cases i with
    | inl i =>
      simpa only [physicalCubeCoefficient, Int.cast_one, abs_one] using
        allocatedPhysicalEntryBudget_one_le B U basis S c
    | inr i =>
      simpa only [physicalCubeCoefficient, Int.cast_zero, abs_zero] using
        zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U basis S c)
  | some k =>
    cases i with
    | inl i => exact allocatedPhysicalCube_root_entry_bound B U basis S c x y k
    | inr i => exact allocatedPhysicalCube_direction_entry_bound B U basis S c x y i k

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSpatialProxyCap
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

theorem narrowTrimmedSpatial_scale_lower {X : Type*}
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (hρ : 0 ≤ ρ)
    (N q : X → ℕ) (x : X) (hN : 0 < N x) (hq : 0 < q x)
    (hsize : 8 * (1 + W) * (q x : ℝ) * ρ ≤ (ξ * τ) * (N x : ℝ)) :
    ρ ≤ trimmedSpatialRootScale τ N q x ∧
      ρ ≤ trimmedSpatialSlopeScale W τ N q x ∧
      ρ ≤ ξ * trimmedSpatialSlopeScale W τ N q x := by
  have h := trimmedSpatial_scale_lower hW hρ N q x hq hsize
  have hH : trimmedSpatialRootScale (ξ * τ) N q x = ξ * trimmedSpatialRootScale τ N q x := by
    unfold trimmedSpatialRootScale
    ring
  have hT : trimmedSpatialSlopeScale W (ξ * τ) N q x = ξ * trimmedSpatialSlopeScale W τ N q x := by
    unfold trimmedSpatialSlopeScale
    ring
  rw [hH, hT] at h
  have hp := trimmedSpatial_scales_pos hW hτ N q x hN hq
  exact ⟨h.1.trans (mul_le_of_le_one_left hp.1.le hξ1),
    h.2.trans (mul_le_of_le_one_left hp.2.le hξ1), h.2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedReferenceJetWindow
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} (c : LayerSamplerVariables G I n B → ℤ)
variable (x : G → IntegerScalarCubeBox α S.value)

theorem allocatedPhysicalCube_coefficient_row_sum
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (i : Unit ⊕ α) :
    (∑ k, |(physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) i k : ℝ)|) ≤
      Fintype.card (Option (LayerSamplerVariables G I n B)) * allocatedPhysicalEntryBudget B U basis S c := by
  calc
    _ ≤ ∑ _k : Option (LayerSamplerVariables G I n B), allocatedPhysicalEntryBudget B U basis S c :=
      Finset.sum_le_sum (fun k _ => allocatedPhysicalCube_coefficient_entry_bound B U basis S c x y i k)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem allocatedNarrow_reference_jet_geometry
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    {X : Type*} (N stride : X → ℕ) (hN : ∀ t, 0 < N t) (hs : ∀ t, 0 < stride t)
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (hρ : 0 < ρ)
    (hsize : ∀ t, 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ ρ) (t : X) :
    let H := trimmedSpatialRootScale τ N stride
    0 < H t ∧
      (∀ i, (∑ k, |(physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) i k : ℝ)|) ≤ H t) ∧
      τ * (N t : ℝ) ≤ 20 * (stride t : ℝ) * H t ∧
      8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t := by
  intro H
  have hH : ρ ≤ H t :=
    (narrowTrimmedSpatial_scale_lower hW hτ hξ1 hρ.le N stride t (hN t) (hs t) (hsize t)).1
  have hpos : 0 < H t := hρ.trans_le hH
  refine ⟨hpos, ?_, ?_, ?_⟩
  · intro i
    apply (allocatedPhysicalCube_coefficient_row_sum B U basis S c x y i).trans
    have he : 0 ≤ allocatedPhysicalEntryBudget B U basis S c :=
      zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U basis S c)
    have hc := mul_nonneg (Nat.cast_nonneg (Fintype.card (Option (LayerSamplerVariables G I n B))) :
      (0 : ℝ) ≤ Fintype.card (Option (LayerSamplerVariables G I n B))) he
    nlinarith
  · have he := referenceJetEnvelopeWidths_trimmed_s2 (q := 0) stride N hs τ (none,t)
    change 20 * (stride t : ℝ) * H t = (5 / 2 : ℝ) * τ * (N t : ℝ) at he
    rw [he]
    nlinarith [mul_nonneg hτ.le (Nat.cast_nonneg (N t) : (0 : ℝ) ≤ N t)]
  · exact hρ8.trans (hH.trans (by linarith))

theorem allocatedNarrow_reference_comparison_geometry_s2_oai
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    {X : Type*} (N stride : X → ℕ) (hN : ∀ t, 0 < N t) (hs : ∀ t, 0 < stride t)
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
    (hsize : ∀ t, 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ ρ) :
    let H := trimmedSpatialRootScale τ N stride
    (∀ t i, (∑ k, |(physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) i k : ℝ)|) ≤ H t) ∧
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) ∧
    (∀ t, 1 ≤ H t) := by
  intro H
  have he := allocatedPhysicalEntryBudget_one_le B U basis S c
  have hc : (1 : ℝ) ≤ Fintype.card (Option (LayerSamplerVariables G I n B)) := by
    rw [Fintype.card_option, Nat.cast_add, Nat.cast_one]
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hprod := mul_le_mul hc (show (1 : ℝ) ≤ allocatedPhysicalEntryBudget B U basis S c from he)
    zero_le_one (Nat.cast_nonneg _)
  have hρ : 1 ≤ ρ := by nlinarith only [hρshift, hprod]
  have hgeom (t : X) := allocatedNarrow_reference_jet_geometry B U basis S c x y N stride hN hs
    hW hτ hξ1 (zero_lt_one.trans_le hρ) hsize hρ8 hρshift t
  refine ⟨fun t => (hgeom t).2.1, fun t => (hgeom t).2.2.2, ?_⟩
  intro t
  exact hρ.trans (narrowTrimmedSpatial_scale_lower hW hτ hξ1
    (zero_le_one.trans hρ) N stride t (hN t) (hs t) (hsize t)).1

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedNarrow_reference_comparison_geometry_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedNarrow_reference_comparison_geometry_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
