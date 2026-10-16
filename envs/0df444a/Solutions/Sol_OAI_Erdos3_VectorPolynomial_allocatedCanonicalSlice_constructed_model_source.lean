-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedCanonicalSlice_constructed_model_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T05:16:07.52913+00:00
-- url     : https://prove2.me/submissions/14373bad-9e94-4eb3-a90a-3064dfa0700e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B162
import Definitions.Def_OAIErdos3B200
import Definitions.Def_OAIErdos3B1375
import Definitions.Def_OAIErdos3B1385
import Theorems.Thm_OAI_Erdos3_BooleanCubeKernel_referenceJetEnvelopeWidths_trimmed
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineLength_slice_ready
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCanonicalSlice_model_source_of_length
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedCanonicalSlice_bounded_ambient
import Theorems.Thm_OAI_Erdos3_canonicalSlicedModulus_le_exp
import Theorems.Thm_OAI_Erdos3_canonicalSlicedModulus_pos
import Theorems.Thm_OAI_Erdos3_containedSupportedProgressionLaw_residue_eq

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialScales
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem trimmedSpatial_scales_pos {X : Type*} {B τ : ℝ} (hB : 0 ≤ B) (hτ : 0 < τ)
    (N modulus : X → ℕ) (x : X) (hN : 0 < N x) (hq : 0 < modulus x) :
    0 < trimmedSpatialRootScale τ N modulus x ∧ 0 < trimmedSpatialSlopeScale B τ N modulus x := by
  have hn : (0 : ℝ) < N x := by exact_mod_cast hN
  have hq' : (0 : ℝ) < modulus x := by exact_mod_cast hq
  unfold trimmedSpatialRootScale trimmedSpatialSlopeScale
  constructor <;> positivity

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

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix



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

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix



end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSpatialProxyCap
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical


end Erdos3.FiniteProbabilityWeights

end

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

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical



end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule
open scoped BigOperators Classical Matrix

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedReferenceJetWindow
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

end Erdos3.BooleanCubeKernel

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
  · have he := referenceJetEnvelopeWidths_trimmed (q := 0) stride N hs τ (none,t)
    change 20 * (stride t : ℝ) * H t = (5 / 2 : ℝ) * τ * (N t : ℝ) at he
    rw [he]
    nlinarith [mul_nonneg hτ.le (Nat.cast_nonneg (N t) : (0 : ℝ) ≤ N t)]
  · exact hρ8.trans (hH.trans (by linarith))

theorem allocatedNarrow_reference_comparison_geometry
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

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientSquareSpatialBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

theorem coefficientErrorSpatialFactor_exp_bound {G : Type*} [Fintype G] (q : ℕ)
    (X : Type*) [Fintype X] (selection : Fin q ↪ G) {M period : ℕ} {P D W L : ℝ}
    (hP : 0 ≤ P) (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P)
    (hperiod : (period : ℝ) ≤ Real.exp (P ^ 2))
    (hq : ((q + 1 : ℕ) : ℝ) ≤ P) (hG : (Fintype.card G : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L) :
    let Cψ := ((period : ℝ) ^ Fintype.card (Unit ⊕ Fin q) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
      (((1 + W) / L) ^ q) ^ Fintype.card X
    0 ≤ Cψ * Vsp ∧ Cψ * Vsp ≤ Real.exp (coefficientErrorSpatialLog P) := by
  intro Cψ Vsp
  have hj : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ P := by
    simpa [Nat.add_comm] using hq
  have hc := anisotropicSpatialDensityCap_exp_bound selection hP hM hMP hj hG
  have hc0 := anisotropicSpatialDensityCap_nonneg selection (by positivity : 0 ≤ 1 / (M : ℝ))
  have hh : (period : ℝ) ^ Fintype.card (Unit ⊕ Fin q) ≤ Real.exp (P ^ 3) :=
    (pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hperiod (sq_nonneg P) _ hj).trans_eq
      (congrArg Real.exp (by ring))
  have hb : (period : ℝ) ^ Fintype.card (Unit ⊕ Fin q) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ)) ≤
      Real.exp (P ^ 3 + anisotropicSpatialCapLog P) := by
    calc
      _ ≤ Real.exp (P ^ 3) * Real.exp (anisotropicSpatialCapLog P) := by gcongr
      _ = _ := (Real.exp_add _ _).symm
  have hcapLog := anisotropicSpatialCapLog_nonneg hP
  have hψ : Cψ ≤ Real.exp (P * (P ^ 3 + anisotropicSpatialCapLog P)) :=
    pow_le_exp_mul_of_le_exp (by positivity) hb (by positivity) _ hX
  have hvol : Vsp ≤ Real.exp (coefficientErrorVolumeLog P) :=
    referenceErrorVolumeFactor_exp_bound q X hP hq hX hL hW hD hWL
  have hprofile0 := smoothProbabilityProfile_pos_zero
  refine ⟨by dsimp [Cψ, Vsp]; positivity, ?_⟩
  calc
    _ ≤ Real.exp (P * (P ^ 3 + anisotropicSpatialCapLog P)) *
        Real.exp (coefficientErrorVolumeLog P) := by gcongr
    _ = _ := by rw [← Real.exp_add]; rfl

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalL1SourceAccuracy
namespace OAI

section

namespace Erdos3

theorem l1SourceAccuracy_pos (target spatialCap spatialVolume : ℝ) :
    0 < l1SourceAccuracy target spatialCap spatialVolume := Real.exp_pos _

theorem l1Source_error_le_exp_of_joint_bound
    {target budget Cψ factor window E δ η ε εtrunc : ℝ}
    (hC0 : 0 ≤ Cψ) (hf0 : 0 ≤ factor) (hw0 : 0 ≤ window)
    (hf : Cψ * factor ≤ Real.exp budget) (hw : Cψ * window ≤ Real.exp budget)
    (hE : E ≤ l1SourceAccuracy target budget 0)
    (hδ : δ ≤ l1SourceAccuracy target budget 0)
    (hη : η ≤ l1SourceAccuracy target budget 0)
    (hε : ε ≤ l1SourceAccuracy target budget 0)
    (ht : εtrunc ≤ l1SourceAccuracy target budget 0) :
    Cψ * (factor * (E + 2 * δ + (2 * η + ε)) + window * εtrunc) ≤ Real.exp (-target) := by
  let e := l1SourceAccuracy target budget 0
  have he : 0 ≤ e := (l1SourceAccuracy_pos _ _ _).le
  have hsum : E + 2 * δ + (2 * η + ε) ≤ 6 * e := by dsimp only [e]; linarith
  have hfirst : (Cψ * factor) * (E + 2 * δ + (2 * η + ε)) ≤ Real.exp budget * (6 * e) :=
    (mul_le_mul_of_nonneg_left hsum (mul_nonneg hC0 hf0)).trans
      (mul_le_mul_of_nonneg_right hf (by positivity))
  have hsecond : (Cψ * window) * εtrunc ≤ Real.exp budget * e :=
    (mul_le_mul_of_nonneg_left ht (mul_nonneg hC0 hw0)).trans (mul_le_mul_of_nonneg_right hw he)
  have h7 : (7 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  calc
    _ ≤ 7 * Real.exp budget * e := by nlinarith only [hfirst, hsecond]
    _ ≤ Real.exp 8 * Real.exp budget * e := by gcongr
    _ = _ := by
      dsimp only [e, l1SourceAccuracy]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators

theorem physicalWindowFactor_le_referenceFactor (dim : ℕ) (X : Type*) [Fintype X]
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L) :
    (9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X ≤
    (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X := by
  have hc : Fintype.card (X × (Unit ⊕ Fin dim)) = Fintype.card (Option (Fin dim) × X) := by
    simp [Nat.add_comm, Nat.mul_comm]
  rw [hc]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9)
  apply (le_div_iff₀ smoothProbabilityProfile_pos_zero).mpr
  linarith [(smoothProbabilityProfile_range 0).2]

theorem physicalL1Source_error_le_exp {G : Type*} [Fintype G] (dim : ℕ)
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) {M period : ℕ} {P D W L target : ℝ}
    (hP : 0 ≤ P) (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P)
    (hperiod : (period : ℝ) ≤ Real.exp (P ^ 2))
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ P) (hG : (Fintype.card G : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L)
    {E δ η ε εtrunc : ℝ}
    (hE : E ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0)
    (hδ : δ ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0)
    (hη : η ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0)
    (hε : ε ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0)
    (ht : εtrunc ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0) :
    let Cψ := ((period : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    let window := (9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    Cψ * (factor * (E + 2 * δ + (2 * η + ε)) + window * εtrunc) ≤ Real.exp (-target) := by
  intro Cψ factor window
  have hC : 0 ≤ Cψ := pow_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (anisotropicSpatialDensityCap_nonneg selection (one_div_nonneg.mpr (Nat.cast_nonneg _)))) _
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hratio : 0 ≤ (1 + W) / L := div_nonneg (by linarith) hL0.le
  have hf0 : 0 ≤ factor := mul_nonneg (pow_nonneg (div_nonneg (by norm_num)
    smoothProbabilityProfile_pos_zero.le) _) (pow_nonneg (pow_nonneg hratio _) _)
  have hw0 : 0 ≤ window := mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (pow_nonneg hratio _) _)
  have hf := (coefficientErrorSpatialFactor_exp_bound dim X selection hP hM hMP hperiod
    hdim hG hX hL hW hD hWL).2
  have hw : Cψ * window ≤ Real.exp (coefficientErrorSpatialLog P) :=
    (mul_le_mul_of_nonneg_left (physicalWindowFactor_le_referenceFactor dim X hW hL0) hC).trans hf
  exact l1Source_error_le_exp_of_joint_bound hC hf0 hw0 hf hw hE hδ hη hε ht

theorem physicalL1Source_error_le_exp_of_precision {G : Type*} [Fintype G] (dim : ℕ)
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) {M period : ℕ} {P D W L target precision : ℝ}
    (hP : 0 ≤ P) (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P)
    (hperiod : (period : ℝ) ≤ Real.exp (P ^ 2))
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ P) (hG : (Fintype.card G : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L)
    (hprecision : target + coefficientErrorSpatialLog P + 8 ≤ precision)
    {η ε εtrunc : ℝ}
    (hη : η ≤ Real.exp (-precision)) (hε : ε ≤ Real.exp (-precision))
    (ht : εtrunc ≤ Real.exp (-precision)) :
    let Cψ := ((period : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    let window := (9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    Cψ * (factor * (Real.exp (-precision) + 2 * Real.exp (-precision) + (2 * η + ε)) +
      window * εtrunc) ≤ Real.exp (-target) := by
  have ha : Real.exp (-precision) ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0 := by
    unfold l1SourceAccuracy
    apply Real.exp_le_exp.mpr
    linarith
  exact physicalL1Source_error_le_exp dim X selection hP hM hMP hperiod hdim hG hX hL hW hD hWL
    ha ha (hη.trans ha) (hε.trans ha) (ht.trans ha)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalSliceConstructedModelSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ uX
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal








end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal









end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ uX
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {dim : ℕ}
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable [∀ j, Nonempty (rowSets j)]
local notation "selectedRows" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (selection : Fin dim ↪ G)
variable (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
variable {X₀ : Type*} [Fintype X₀] (stride₀ : X₀ → ℕ)
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ)
variable (hcanonical : modulus = canonicalSlicedModulus (M := Mk) selection stride₀ m x)
variable (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := (Fin dim)) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j => Measure.pi (fun _ : rowSets j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin dim) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

omit [∀ j, Nonempty (rowSets j)] in
include hcanonical μrows hR hσ hMk hgood hP hMkP hRP hRi hσi hcount in
theorem allocatedCanonicalSlice_constructed_model_source_oai
    {D target Pk Prho F Qstride : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin dim) selectedRows D)
    (hPk : 0 ≤ Pk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target) (hF : 0 ≤ F) (hQstride : 0 ≤ Qstride)
    (hstride₀ : ∀ i, 0 < stride₀ i) (hstrideBound : ∀ i, (stride₀ i : ℝ) ≤ Real.exp Qstride)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card X₀ * Qstride)) ≤ S.value)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U basis S) →
  EuclideanJetLayers U selectedRows → ℝ)
    (hgm : ∀ y, Measurable (g y)) (hg0 : ∀ y z, 0 ≤ g y z)
    (hgi : ∀ y, Integrable (g y) jetHaar)
    (hglaw : ∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
  (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) = realDensityMeasure jetHaar (g y))
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j)
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hq : Fintype.card (Fin dim) ≤ m + 1)
    (hrowDegree : ∀ j (a : rowSets j), a.val.card ≤ j.val + 1)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U basis S))
    (hy₀ : 0 < (wholeLaw).weight y₀)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius (Fin dim) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin dim) * ((Fintype.card (Fin dim) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4)))
    (period : ℕ) [NeZero period]
    (hperiodCanonical : period = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hgood m))
    (hdiv : period ∣ d) (siteRadius : ℝ≥0) (hrone : 1 ≤ siteRadius)
    (hsitebudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ))
    {Pbox Vlog Nlog Mlog baseAmbient : ℝ}
    (hPbox : 0 ≤ Pbox) (hVlog : 0 ≤ Vlog) (hNlog : 0 ≤ Nlog) (hMlog : 0 ≤ Mlog)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (hvolume : allocatedFullGridNaturalVolume B U basis S rowSets ≤ Real.exp Vlog)
    (hnormalizer : ‖((allocatedProductIdealNormalizer B U basis S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp Nlog)
    (hmask : (layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
      coefficientDeckPeriodCap selectedRows Q period ≤ Real.exp Mlog)
    (hbaseAmbient : 0 ≤ baseAmbient)
    (hvbase : Vlog ≤ baseAmbient) (hnbase : Nlog ≤ baseAmbient) (hmbase : Mlog ≤ baseAmbient)
    (hsites : (Fintype.card (Finset (Fin dim)) : ℝ) ≤ baseAmbient)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ baseAmbient)
    (hlabels : (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤ Real.exp baseAmbient)
    (hKbase : (K : ℝ) ≤ Real.exp baseAmbient)
    (hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp baseAmbient)
    (hdbase : (d : ℝ) ≤ Real.exp baseAmbient) (hpbase : (period : ℝ) ≤ Real.exp baseAmbient)
    (hrowsAmbient : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ baseAmbient)
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp baseAmbient) :
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin dim))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    let center := principalProgressionSliceCenter (α := (Fin dim)) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := (Fin dim)) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, selectedRows a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option (Fin dim))
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let profile := fun y => ((gridLaw).mean (fun u =>
      allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows
        hb o bW d (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) modulus ideal y) : ℂ)
    ∀ (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : X → ℕ),
    spatialModulus = period →
    let refined := residueRefinedPeriod spatialModulus stride
    modulus = refined →
    let labels := PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined
    let wholeReference : labels → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
        (allocatedPrincipalSides B U basis S) := fun _ => y₀
    let r := principalResidueLabel refined y₀

    ∀ {W τ ξn mesh : ℝ} (hW : 0 ≤ W) (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ),
    let point := physicalCubeRowSample U d rows poly hmem
    ∀ (model : EuclideanJetLayers U selectedRows → ℂ)
      {κ lossTarget Pphysical Dphysical εtrunc Psample Rrank Sstride εsample ηsample : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → 0 < τ → 0 < mesh →
    allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W →
    (∀ v, ‖test v‖ ≤ 1) →
    κ ≤ ((wholeLaw).complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξn)
      B U basis S X spatialModulus stride wholeReference x hMk selection hgood N hW mesh base cells point test
      (fun y z => (g y z : ℂ)))).re →
    0 ≤ εtrunc → (∀ z, ‖profile z - model z‖ ≤ εtrunc) →
    0 ≤ Psample → (Fintype.card X : ℝ) ≤ Psample →
    (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Psample →
    (d : ℝ) ≤ Real.exp Psample →
    0 ≤ Sstride → Sstride ≤ Real.exp Psample → 0 < εsample →
    1 / τ ≤ Real.exp Psample → 1 / εsample ≤ Real.exp Psample →
    (∀ i, (stride i : ℝ) ≤ Sstride) →
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{uX,uJ,0} m dim)
    (∀ i, Real.exp ((Psample + A) ^ A) ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    ∀ (actual : (JetAmbientIndex selectedRows J → UnitAddCircle) → ℂ)
      (La Ca : ℝ≥0),
    LipschitzWith La actual → (∀ z, ‖actual z‖ ≤ Ca) →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Psample →
    (La : ℝ) ≤ Real.exp Psample → (Ca : ℝ) ≤ Real.exp Psample →
    ambientBudget ≤ Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    (∀ y, ((wholeLaw).mean (fun v => g v y) : ℂ) = actual (coveredJetAmbientTorus U 1 y)) →
    let _root := allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (wholeReference r)
    let _dirs := allocatedPhysicalCubeDirections B U basis S x (wholeReference r)
    let Hsp := trimmedSpatialRootScale τ N stride
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    let _Csp := ((spatialModulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (Mk : ℝ))) ^ Fintype.card X
    let _volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    (∀ z, 0 < V z) → (0 < ∑' z, selectedResidueSmoothWeight stride cells V z) →
    ∀ {ρphysical : ℝ}, ξn ≤ 1 →
    (∀ t, 8 * (1 + W) * (stride t : ℝ) * ρphysical ≤ (ξn * τ) * (N t : ℝ)) →
    8 * (probabilityProfileLipschitz : ℝ) ≤ ρphysical →
    2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U basis S (fun _ => 0))) ≤ ρphysical →
    0 ≤ Pphysical → (Mk : ℝ) ≤ Real.exp Pphysical →
    (spatialModulus : ℝ) ≤ Real.exp (Pphysical ^ 2) →
    ((dim + 1 : ℕ) : ℝ) ≤ Pphysical → (Fintype.card G : ℝ) ≤ Pphysical →
    (Fintype.card X : ℝ) ≤ Pphysical → Dphysical ≤ Real.exp Pphysical →
    W ≤ Dphysical * S.value →
    lossTarget + coefficientErrorSpatialLog Pphysical + 8 ≤ target →
    ηsample ≤ Real.exp (-target) → εsample ≤ Real.exp (-target) → εtrunc ≤ Real.exp (-target) →
    κ - Real.exp (-lossTarget) ≤
      (∑ t : cells × spatialWindow (α := Fin dim) Hsp 4, (selectedResidueCellWeight stride cells V t.1 : ℂ) *
        allocatedRecenteredResidueWeight (τ := τ) B U basis S X spatialModulus stride wholeReference x hMk selection hgood
          N hW mesh base cells test r t.1 t.2.val *
        model (point (allocatedWholeResidueReconstruction B U basis S X spatialModulus stride wholeReference x base r
          t.1.val t.2.val))).re := by
  intro ambientQ ambientBudget center width ideal profile
  have hm : 0 < modulus := by
    rw [hcanonical]
    exact canonicalSlicedModulus_pos selection stride₀ m hstride₀ x
  have hmodulus : (modulus : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card X₀ * Qstride) := by
    rw [hcanonical]
    exact canonicalSlicedModulus_le_exp selection stride₀ m hPk hQstride hMkPk hstrideBound x
  have hTmod : 0 ≤ ((m + 1 : ℕ) : ℝ) * Pk + Fintype.card X₀ * Qstride := by positivity
  have hready := allocatedAffineLength_slice_ready B U basis hdimensions hP hPrho hPk htarget hF hTmod
    S hlength H₀ step₀ c₀ hsubset₀ hδ hδF modulus hm hmodulus hstep hdense
  have hw (i) : |center i| + |width i| ≤ 1 :=
    (principalProgressionSlice_parameters activeB activeDegree L H step c positiveLengths
      hstep hready.1 hδ hsubset hdense i).2.2
  have hr : 0 < siteRadius := zero_lt_one.trans_le hrone
  have hT0 (j) : 0 ≤ T j :=
    (add_nonneg (partitionedIdealRadius_nonneg (Fin dim) m) zero_le_one).trans (hT j)
  have hσ1 (j) : σ j ≤ 1 := (hσsmall j).trans htone
  obtain ⟨surrogate, hLs, hCs, happrox⟩ := exists_allocatedCanonicalSlice_bounded_ambient
    B U basis S rowSets x y₀ modulus d period siteRadius hr hb o bW hR C hC hchart hsitebudget
    (ρ grid) center width hσ H₀ step₀ c₀ hH₀ hsubset₀ r₀ hcell hMk selection hgood stride₀
    hcanonical hperiodCanonical hy₀ (by simpa only [Fintype.card_fin] using hq) hrowDegree hdiv
    Cforward hforward K hK T hT0 hT hsource hradius hσ1 hρ hρ1 hw
    hPbox hPrho hVlog hNlog hMlog htarget hbox hρlog hvolume hnormalizer hmask
    hbaseAmbient hvbase hnbase hmbase hsites haxes hlabels hKbase hcoords hcutoff hrone hdbase
    hpbase hrowsAmbient houtputs hheight
  intro spatialModulus _ stride N hspatialCanonical refined hmodulusRefined labels wholeReference r
    W τ ξn mesh hW base cells poly hp hmem test point model κ lossTarget Pphysical Dphysical εtrunc Psample Rrank Sstride εsample ηsample
    hstridepos hN hτ hmesh hrootbudget htest hpositive hεtrunc htrunc
    hPs hX hframe hdP hSstride hSstrideP hεsample hτP hεsampleP hstride A hsize hrank hRrank
    actual La Ca hLa hCa hηsample hamb hLaP hCaP hAmbientP hjet hηsampleP hactual
    root dirs Hsp V Csp volumeFactor hV hZ ρphysical hξn1 hsizePhysical hρ8 hρshift
    hPphysical hMkPhysical hPeriodPhysical hDimPhysical hGPhysical hXPhysical hDPhysical hWL
    hprecision hηprecision hεprecision htprecision
  have hlabel : ∀ y, (wholeLaw).weight y ≠ 0 → principalResidueLabel refined y = r := by
    intro y hy
    change principalResidueLabel refined y = principalResidueLabel refined y₀
    rw [← hmodulusRefined]
    exact containedSupportedProgressionLaw_residue_eq B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S)
      hH₀ hsubset₀ modulus r₀ hcell y y₀ hy hy₀.ne'
  have hwhole : principalResidueLabel refined (wholeReference r) = r := rfl
  have hspatialPeriod : integerScalarLattice (Unit ⊕ Fin dim) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection) := by
    rw [hspatialCanonical, hperiodCanonical]
    exact (goodKernelUniformCandidate_spec.{0,_,0} selection x hgood m).1 _
  obtain ⟨hrows, hscale, hH1⟩ := allocatedNarrow_reference_comparison_geometry B U basis S
    (fun _ => 0) x (wholeReference r) N stride hN hstridepos hW hτ hξn1 hsizePhysical hρ8 hρshift
  have hcost := physicalL1Source_error_le_exp_of_precision dim X selection hPphysical hMk hMkPhysical
    hPeriodPhysical hDimPhysical hGPhysical hXPhysical
    (by exact_mod_cast Nat.succ_le_of_lt S.positive : (1 : ℝ) ≤ S.value) hW hDPhysical hWL
    hprecision hηprecision hεprecision htprecision
  exact allocatedCanonicalSlice_model_source_of_length
    B U basis hR hσ S rowSets x hMk selection hgood stride₀ hP hMkP hRP hRi hσi hcount
    Q hb o bW d H₀ step₀ c₀ hH₀ hsubset₀ modulus hcanonical r₀ hcell ν μ μrows
    hdimensions hPk hMkPk hPrho htarget hF hQstride hstride₀ hstrideBound hlength
    g hgm hg0 hgi hglaw ρ t htone hs hρ hρ1 hσsmall hstep hδ hδF hdense hq hrowDegree
    y₀ hy₀ T hT hsource C hC hchart hbudget hρlog hη0 hηsmall
    spatialModulus stride N wholeReference r hlabel hwhole hW base cells poly hp hmem test model
    hstridepos hN hτ hmesh hrootbudget hspatialPeriod htest hpositive hεtrunc htrunc
    hPs hX hframe hdP hSstride hSstrideP hεsample hτP hεsampleP hstride hsize hrank hRrank
    actual surrogate La ⟨Real.exp ambientBudget, Real.exp_nonneg _⟩ Ca ⟨Real.exp ambientBudget, Real.exp_nonneg _⟩
    hLa hLs hCa hCs hηsample hamb hLaP (Real.exp_le_exp.mpr hAmbientP) hCaP
    (Real.exp_le_exp.mpr hAmbientP) hjet hηsampleP hactual happrox hV hZ hrows hscale hH1 hcost

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{uJ, uQ, uX, u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedCanonicalSlice_constructed_model_source_oai.{uJ, uQ, uX, u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.allocatedCanonicalSlice_constructed_model_source_oai.{uJ, uQ, uX, u_1, u_2, u_3, u_4}
