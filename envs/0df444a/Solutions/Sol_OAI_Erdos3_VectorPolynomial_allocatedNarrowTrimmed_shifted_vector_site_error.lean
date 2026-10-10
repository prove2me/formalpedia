-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_shifted_vector_site_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T18:46:38.700711+00:00
-- url     : https://prove2.me/submissions/ed09b02b-fb1a-4b31-b285-95203175d33c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B054
import Theorems.Thm_OAI_Erdos3_canonicalVectorSpatialSiteApprox_shift_error
import Theorems.Thm_OAI_Erdos3_goodScalarKernelTuple_anisotropic_error

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SmoothSplitSampling
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem smoothCoefficientPMF_apply (S : ℝ) (hS : 0 < S) (k : ℤ) :
    (smoothCoefficientPMF S hS k).toReal = smoothProbabilityProfile ((k : ℝ) / S) / smoothSampleSum S :=
  realWeightPMF_apply _ _ _ _ k

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothProductPMF_apply {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) (z : I → ℤ) :
    (smoothProductPMF S hS z).toReal = ∏ i, (smoothCoefficientPMF (S i) (hS i) (z i)).toReal := by
  rw [smoothProductPMF, realWeightPMF_apply, smoothProductSamples_sum S hS]
  simp only [smoothProductProfile, smoothCoefficientPMF_apply, Finset.prod_div_distrib]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductPMFMap
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem dependentProductPMF_apply {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) (x : ∀ d, X d) : dependentProductPMF p x = ∏ d, p d (x d) := by
  simp only [dependentProductPMF, Measure.toPMF_apply, Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun d _ => (p d).toMeasure_apply_singleton (x d) (measurableSet_singleton _))

theorem dependentProductPMF_scaled {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) (S : D → ℝ) (x : ∀ d, X d) :
    (∏ d, S d) * (dependentProductPMF p x).toReal = ∏ d, S d * (p d (x d)).toReal := by
  rw [dependentProductPMF_apply, ENNReal.toReal_prod, Finset.prod_mul_distrib]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem dependentProductPMF_map {J : Type*} [Fintype J] {X Y : J → Type*}
    [∀ j, Countable (X j)] [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSingletonClass (X j)]
    [∀ j, Countable (Y j)] [∀ j, MeasurableSpace (Y j)] [∀ j, MeasurableSingletonClass (Y j)]
    (p : ∀ j, PMF (X j)) (f : ∀ j, X j → Y j) :
    (dependentProductPMF p).map (fun x j => f j (x j)) =
      dependentProductPMF (fun j => (p j).map (f j)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  simp only [dependentProductPMF, Measure.toPMF_toMeasure]
  rw [Measure.pi_map_pi (fun j => (measurable_of_countable (f j)).aemeasurable)]
  congr 1
  funext j
  exact PMF.toMeasure_map (f j) (p j) (measurable_of_countable _)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarCubeMinorPolynomial
namespace OAI

section

namespace Erdos3

theorem scalarCubeMinorPolynomial_grid_eval {I J : Type*} [Fintype I] [DecidableEq I]
    {N L : ℕ} (e : J × Option I ≃ Fin N) (s : I → J) (x : J → IntegerScalarCubeBox I L) :
    MvPolynomial.eval (fun i => (scalarCubeGrid e x i : ℝ) / L) (scalarCubeMinorPolynomial e s) =
      normalizedScalarCubeMinor s x := by
  rw [scalarCubeMinorPolynomial, coordinateMatrixPolynomial_eval]
  let A := (scalarCubeDifferenceMatrix x).submatrix id s
  have hm : ((fun i j => (scalarCubeGrid e x (e (s j, some i)) : ℝ) / L) : Matrix I I ℝ) =
      (L : ℝ)⁻¹ • A.map (Int.castRingHom ℝ) := by
    ext i j
    simp [A, scalarCubeGrid, scalarCubeDifferenceMatrix, sampledColumnMatrix,
      Matrix.submatrix_apply, div_eq_mul_inv, mul_comm]
  have hcast : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) :=
    ((Int.castRingHom ℝ).map_det A).symm
  rw [hm, Matrix.det_smul, hcast, inv_pow]
  change ((L : ℝ) ^ Fintype.card I)⁻¹ * (A.det : ℝ) = (A.det : ℝ) / (L : ℝ) ^ Fintype.card I
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI

namespace Erdos3

theorem normalizedScalarCubePivot_det {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {L : ℕ}
    (s : I → J) (x : J → IntegerScalarCubeBox I L) :
    (normalizedScalarCubePivot s x).det = normalizedScalarCubeMinor s x := by
  let e := Fintype.equivFin (J × Option I)
  have h := scalarCubeMinorPolynomial_grid_eval e s x
  rw [scalarCubeMinorPolynomial, coordinateMatrixPolynomial_eval] at h
  change Matrix.det (fun i j => ((x (s j) (some i) : ℤ) : ℝ) / (L : ℝ)) = _
  simpa only [scalarCubeGrid, e.symm_apply_apply] using h

end Erdos3

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothProfileReindexing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_map_equiv_apply {X Y : Type*} (p : PMF X) (e : X ≃ Y) (y : Y) :
    (p.map e) y = p (e.symm y) := by
  classical
  rw [PMF.map_apply, tsum_eq_single (e.symm y)]
  · simp
  · intro z hz
    have he : y ≠ e z := by
      intro he
      apply hz
      apply e.injective
      simpa only [e.apply_symm_apply] using he.symm
    simp only [ite_eq_right_iff]
    exact fun h => (he h).elim

theorem smoothProductPMF_reindex_apply {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (S : J → ℝ) (hS : ∀ j, 0 < S j) (z : J → ℤ) :
    smoothProductPMF (S ∘ e) (fun i => hS (e i)) (z ∘ e) = smoothProductPMF S hS z := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [smoothProductPMF_apply, smoothProductPMF_apply]
  exact Equiv.prod_comp e (fun j => (smoothCoefficientPMF (S j) (hS j) (z j)).toReal)

theorem smoothProductPMF_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (S : J → ℝ) (hS : ∀ j, 0 < S j) :
    (smoothProductPMF (S ∘ e) (fun i => hS (e i))).map
      (fun z => z ∘ e.symm) = smoothProductPMF S hS := by
  let E : (I → ℤ) ≃ (J → ℤ) := Equiv.arrowCongr e (Equiv.refl ℤ)
  change (smoothProductPMF (S ∘ e) (fun i => hS (e i))).map E = _
  ext z
  rw [pmf_map_equiv_apply]
  exact smoothProductPMF_reindex_apply e S hS z

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothIntegerImage
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem smoothMatrixImagePMF_reindex {O I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix O J ℤ) (e : I ≃ J) (S : J → ℝ) (hS : ∀ j, 0 < S j) :
    smoothMatrixImagePMF (A.submatrix id e) (S ∘ e) (fun i => hS (e i)) =
      smoothMatrixImagePMF A S hS := by
  unfold smoothMatrixImagePMF
  rw [← smoothProductPMF_reindex e S hS, PMF.map_comp]
  congr 1
  funext z
  exact Matrix.submatrix_mulVec_equiv A z id e

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedProductCoordinateLaw
namespace OAI

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped Matrix

end Erdos3

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem shiftedSmoothProductMass_grouped {K X : Type*} [Fintype K] [Fintype X]
    (a S : K × X → ℝ) (hS : ∀ z, 0 < S z) :
    shiftedSmoothProductMass a S =
      ∏ x, shiftedSmoothProductMass (fun k => a (k, x)) (fun k => S (k, x)) := by
  rw [shiftedSmoothProductMass_eq_prod a S hS]
  simp_rw [shiftedSmoothProductMass_eq_prod _ _ (fun k => hS (k, _))]
  rw [Fintype.prod_prod_type]
  exact Finset.prod_comm

theorem shiftedSmoothProductMass_slice_pos {K X : Type*} [Fintype K] [Fintype X]
    (a S : K × X → ℝ) (hS : ∀ z, 0 < S z)
    (hZ : 0 < shiftedSmoothProductMass a S) (x : X) :
    0 < shiftedSmoothProductMass (fun k => a (k, x)) (fun k => S (k, x)) := by
  rw [shiftedSmoothProductMass_eq_prod _ _ (fun k => hS (k, x))]
  exact Finset.prod_pos (fun k _ => shiftedSmoothProductMass_coordinate_pos a S hS hZ (k, x))

theorem shiftedSmoothProductPMF_grouped {K X : Type*} [Fintype K] [Fintype X]
    (a S : K × X → ℝ) (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S) :
    (shiftedSmoothProductPMF a S hS hZ).map (spatialCoordinateArrayEquiv K X) =
      dependentProductPMF (fun x => shiftedSmoothProductPMF
        (fun k => a (k, x)) (fun k => S (k, x)) (fun k => hS (k, x))
        (shiftedSmoothProductMass_slice_pos a S hS hZ x)) := by
  ext z
  have hm := pmf_map_injective_at (shiftedSmoothProductPMF a S hS hZ)
    (spatialCoordinateArrayEquiv K X) (spatialCoordinateArrayEquiv K X).injective
    ((spatialCoordinateArrayEquiv K X).symm z)
  rw [Equiv.apply_symm_apply] at hm
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [hm, shiftedSmoothProductPMF_toReal, dependentProductPMF_apply, ENNReal.toReal_prod]
  simp_rw [shiftedSmoothProductPMF_toReal]
  rw [Finset.prod_div_distrib, shiftedSmoothProductMass_grouped a S hS]
  congr 1
  simp only [rectangularWeight, smoothProductProfile, rectangularLatticePoint,
    spatialCoordinateArrayEquiv, Equiv.coe_fn_symm_mk, Fintype.prod_prod_type]
  exact Finset.prod_comm

end Erdos3

end OAI

end

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

theorem trimmedSpatial_scale_ratio {X : Type*} {B τ : ℝ} (hB : 0 ≤ B)
    (N modulus : X → ℕ) (x : X) :
    trimmedSpatialRootScale τ N modulus x =
      (1 + B) * trimmedSpatialSlopeScale B τ N modulus x := by
  have hb : 1 + B ≠ 0 := ne_of_gt (by linarith)
  unfold trimmedSpatialRootScale trimmedSpatialSlopeScale
  field_simp

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedProductTestError
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {X Y : Type*} [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [Countable Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem shiftedSmoothProductPMF_zero {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass 0 S) :
    shiftedSmoothProductPMF 0 S hS hZ = smoothProductPMF S hS := by
  have hz (z : I → ℤ) : rectangularLatticePoint 0 S z = fun i => (z i : ℝ) / S i := by
    funext i
    change ((z i : ℝ) - 0) / S i = (z i : ℝ) / S i
    rw [sub_zero]
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp only [shiftedSmoothProductPMF_toReal, smoothProductPMF, realWeightPMF_apply,
    shiftedSmoothProductMass, rectangularWeight, hz]

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

variable {K X : Type*} [Fintype K] [Fintype X]
variable {I : X → Type*} [∀ x, Fintype (I x)]

theorem shiftedSmoothProductPMF_matrix_image (a S : K × X → ℝ)
    (hS : ∀ z, 0 < S z) (hZ : 0 < shiftedSmoothProductMass a S)
    (M : ∀ x, Matrix (I x) K ℤ) :
    (shiftedSmoothProductPMF a S hS hZ).map (fun z x => M x *ᵥ (fun k => z (k, x))) =
      dependentProductPMF (fun x =>
        (shiftedSmoothProductPMF (fun k => a (k, x)) (fun k => S (k, x))
          (fun k => hS (k, x)) (shiftedSmoothProductMass_slice_pos a S hS hZ x)).map
            (fun z => M x *ᵥ z)) := by
  have hm : (fun z x => M x *ᵥ (fun k => z (k, x))) =
      (fun z x => M x *ᵥ z x) ∘ spatialCoordinateArrayEquiv K X := rfl
  rw [hm, ← PMF.map_comp, shiftedSmoothProductPMF_grouped,
    dependentProductPMF_map]

variable [DecidableEq K] [∀ x, DecidableEq (I x)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Matrix

variable {K X : Type*} [Fintype K] [DecidableEq K] [Fintype X]
variable {I : X → Type*} [∀ x, Fintype (I x)] [∀ x, DecidableEq (I x)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelCover
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
theorem allocatedPhysicalCube_principal_columns (i : Unit ⊕ α)
    (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
    physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) i (some (.inr j)) =
      principalSpatialColumns (fun j => c (.inr j)) id y i j := by
  cases i <;> rfl

omit [Fintype α] in
theorem allocatedPhysicalCube_kernel_columns (i : Unit ⊕ α) (g : G) :
    physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) i (some (.inl g)) =
      rootDifferenceMatrix (fun g => c (.inl g) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) i (.inr g) := by
  cases i <;> rfl

omit [Fintype α] in
theorem allocatedPhysicalCube_base_column (i : Unit ⊕ α) :
    physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) i none =
      rootDifferenceMatrix (fun g => c (.inl g) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) i (.inl ()) := by
  cases i with
  | inl i => cases i; rfl
  | inr i => rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

open BooleanCubeKernel Polynomial

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedAnisotropicSpatialLaw
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Matrix

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

omit [Fintype α] in
theorem allocatedPhysicalCube_split :
    (physicalCubeCoefficient root dirs).submatrix id
      (physicalSpatialSplitEquiv G (PrincipalTupleIndex B (layerSamplerDegree I n))) =
        Matrix.fromCols (rootDifferenceMatrix ker (scalarCubeDifferenceMatrix x)) cols := by
  ext i j
  cases j with
  | inl j =>
    cases j with
    | inl u =>
      cases u
      exact allocatedPhysicalCube_base_column B U basis S c x y i
    | inr g => exact allocatedPhysicalCube_kernel_columns B U basis S c x y i g
  | inr j => exact allocatedPhysicalCube_principal_columns B U basis S c x y i j

variable [DecidableEq α] [DecidableEq G]

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CenteredPhysicalProductLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem shiftedSmoothProductMass_zero_pos {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) : 0 < shiftedSmoothProductMass 0 S := by
  rw [shiftedSmoothProductMass_eq_prod 0 S hS]
  apply Finset.prod_pos
  intro i _
  simpa only [shiftedSmoothSampleSum, Pi.zero_apply, sub_zero, smoothSampleSum] using
    smoothSampleSum_pos (hS i)

theorem smoothProductPMF_matrix_image {K X : Type*} [Fintype K] [Fintype X]
    {I : X → Type*} [∀ x, Fintype (I x)]
    (S : K × X → ℝ) (hS : ∀ z, 0 < S z) (M : ∀ x, Matrix (I x) K ℤ) :
    (smoothProductPMF S hS).map (fun z x => M x *ᵥ (fun k => z (k, x))) =
      dependentProductPMF (fun x => smoothMatrixImagePMF (M x) (fun k => S (k, x)) (fun k => hS (k, x))) := by
  have h := shiftedSmoothProductPMF_matrix_image (0 : K × X → ℝ) S hS
    (shiftedSmoothProductMass_zero_pos S hS) M
  have hz (x : X) : (fun k : K => (0 : K × X → ℝ) (k, x)) = 0 := rfl
  simpa only [hz, shiftedSmoothProductPMF_zero, smoothMatrixImagePMF] using h

theorem smoothProductPMF_matrix_image_scaled {K X : Type*} [Fintype K] [Fintype X]
    {I : X → Type*} [∀ x, Fintype (I x)]
    (S : K × X → ℝ) (hS : ∀ z, 0 < S z) (M : ∀ x, Matrix (I x) K ℤ)
    (P : ∀ x, I x → ℝ) (v : ∀ x, I x → ℤ) :
    (∏ x, ∏ i, P x i) *
        (((smoothProductPMF S hS).map (fun z x => M x *ᵥ (fun k => z (k, x)))) v).toReal =
      ∏ x, (∏ i, P x i) * (smoothMatrixImagePMF (M x) (fun k => S (k, x)) (fun k => hS (k, x)) (v x)).toReal := by
  rw [smoothProductPMF_matrix_image, dependentProductPMF_scaled]

end Erdos3

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

variable [DecidableEq α] [DecidableEq G]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators NNReal

theorem anisotropicSpatialError_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (N : Type*) [Fintype N] (B : ℕ) {κ C ρ ξ : ℝ}
    (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hξ : 0 ≤ ξ) :
    0 ≤ anisotropicSpatialError s N B κ C ρ ξ := by
  unfold anisotropicSpatialError normalizedFiberErrorConstant integerFiberErrorConstant
    anisotropicSpatialDetAllowance physicalSpatialInverseBound spatialKernelErrorConstant
  positivity

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

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
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

omit [Fintype α] [DecidableEq α] in
theorem allocatedPhysicalResidue_shift_principal
    (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    {X : Type*} (r : Option vars × X → ℤ) (q : X → ℕ) :
    physicalResidueOffsetShift (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeRoot B U basis S c x y₀)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (allocatedPhysicalCubeDirections B U basis S x y₀) r q =
    fun d => residueMatrixShift (principalSpatialColumns (fun j => c (Sum.inr j)) id y)
      (principalSpatialColumns (fun j => c (Sum.inr j)) id y₀) (q d)
      (fun j => r (some (Sum.inr j), d)) := by
  funext d i
  unfold physicalResidueOffsetShift residueMatrixShift
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Fintype.sum_option,
    Fintype.sum_sum_type, allocatedPhysicalCube_principal_columns]
  cases i <;> simp [physicalCubeCoefficient, allocatedPhysicalCubeRoot, allocatedPhysicalCubeDirections]

end Erdos3.VectorPolynomial

end

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
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedNarrowSpatialLaw
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Matrix

theorem splitPhysicalSpatialInputScale_pos (G N : Type*)
    {H T : ℝ} {Q : N → ℝ} (hH : 0 < H) (hT : 0 < T) (hQ : ∀ j, 0 < Q j) :
    ∀ k, 0 < splitPhysicalSpatialInputScale G N H T Q k := by
  rintro (_ | (g | j))
  · exact hH
  · exact hT
  · exact hQ j

theorem splitPhysicalSpatialInputScale_reindex (G N : Type*)
    (H T : ℝ) (Q : N → ℝ) :
    splitPhysicalSpatialInputScale G N H T Q ∘ physicalSpatialSplitEquiv G N =
      Sum.elim (anisotropicSpatialScale G H T) Q := by
  funext j
  cases j with
  | inl j => cases j <;> rfl
  | inr j => rfl

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "principal" => PrincipalTupleIndex B (layerSamplerDegree I n)
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

theorem allocatedPhysicalCube_split_width_law {H T : ℝ}
    (Q : principal → ℝ) (hH : 0 < H) (hT : 0 < T) (hQ : ∀ j, 0 < Q j) :
    smoothMatrixImagePMF (physicalCubeCoefficient root dirs)
      (splitPhysicalSpatialInputScale G principal H T Q)
      (splitPhysicalSpatialInputScale_pos G principal hH hT hQ) =
      anisotropicSpatialOutputLaw ker (scalarCubeDifferenceMatrix x) cols H T Q hH hT hQ := by
  have h := smoothMatrixImagePMF_reindex (physicalCubeCoefficient root dirs)
    (physicalSpatialSplitEquiv G principal)
    (splitPhysicalSpatialInputScale G principal H T Q)
    (splitPhysicalSpatialInputScale_pos G principal hH hT hQ)
  rw [allocatedPhysicalCube_split] at h
  simpa only [splitPhysicalSpatialInputScale_reindex, anisotropicSpatialOutputLaw] using h.symm

variable [DecidableEq α] [DecidableEq G]

theorem allocatedPhysicalCube_narrow_error (selection : α ↪ G) {M : ℕ}
    {H T W κ C₀ ρ ξ : ℝ} (hH : 0 < H) (hT : 0 < T) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hWT : W * T ≤ H) (hWC : W ≤ C₀) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hscaleH : ρ ≤ H) (hscaleQ : ρ ≤ ξ * T)
    (hmesh : anisotropicSpatialMeshThreshold selection principal C₀ ≤ ρ) :
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    ∀ v, |(∏ i, physicalSpatialOutputScale α H T S.value i) *
        (smoothMatrixImagePMF (physicalCubeCoefficient root dirs)
          (splitPhysicalSpatialInputScale G principal H T (fun _ => ξ * T))
          (splitPhysicalSpatialInputScale_pos G principal hH hT (fun _ => mul_pos hξ hT)) v).toReal -
      maskedIntegerImageDensity (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection) cols)
        (physicalSpatialOutputScale α H T S.value)
        (anisotropicSpatialKernelDensity selection ker (scalarCubeDifferenceMatrix x) hp H T S.value
          hH hT (Nat.cast_pos.mpr S.positive)) v| ≤
      anisotropicSpatialError selection principal M κ C₀ ρ ξ := by
  classical
  intro hp
  have hrall (k) : |(root k : ℝ)| ≤ W :=
    (allocatedPhysicalCube_root_budget B U basis S c x y k).trans hbudget
  have hr (g) : |(ker g : ℝ)| * T ≤ H :=
    (mul_le_mul_of_nonneg_right (hrall (.inl g)) hT.le).trans hWT
  have hrC (g) : |(ker g : ℝ)| ≤ C₀ := (hrall (.inl g)).trans hWC
  have hcols : ∀ i j, |(cols i j : ℝ)| * (ξ * T) ≤
      ξ * physicalSpatialOutputScale α H T S.value i := by
    rintro (i | i) j
    · change |(root (.inr j) : ℝ)| * (ξ * T) ≤ ξ * H
      calc
        _ = ξ * (|(root (.inr j) : ℝ)| * T) := by ring
        _ ≤ ξ * H := mul_le_mul_of_nonneg_left
          ((mul_le_mul_of_nonneg_right (hrall (.inr j)) hT.le).trans hWT) hξ.le
    · change |(dirs i (.inr j) : ℝ)| * (ξ * T) ≤ ξ * ((S.value : ℝ) * T)
      calc
        _ ≤ (S.value : ℝ) * (ξ * T) := mul_le_mul_of_nonneg_right
          (allocatedPhysicalCube_directions_bound B U basis S x y i (.inr j)) (mul_pos hξ hT).le
        _ = _ := by ring
  have hscaleT : ρ ≤ T := hscaleQ.trans (mul_le_of_le_one_left hT.le hξ1)
  rw [allocatedPhysicalCube_split_width_law B U basis S c x y]
  exact goodScalarKernelTuple_anisotropic_error S.positive selection x ker cols (fun _ => ξ * T)
    hH hT hκ hρ hx hC₀ hLC hr hrC (fun _ => mul_pos hξ hT) hξ.le hξ1 hcols
    hscaleH hscaleT (fun _ => hscaleQ) hmesh

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSpatialProxyCap
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {Ω R : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq R]
variable (p : FiniteProbabilityWeights Ω) (label : Ω → R)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open BooleanCubeKernel

theorem narrowTrimmedSpatial_residue_scale {G J X : Type*}
    (W τ ξ : ℝ) (N q : X → ℕ) (x : X) :
    (fun k => residueProfileWidth q (narrowTrimmedSpatialWidths (G := G) (J := J) W τ ξ N) (k,x)) =
      splitPhysicalSpatialInputScale G J (trimmedSpatialRootScale τ N q x)
        (trimmedSpatialSlopeScale W τ N q x) (fun _ => ξ * trimmedSpatialSlopeScale W τ N q x) := by
  funext k
  rcases k with _ | (g | j) <;>
    simp only [residueProfileWidth, narrowTrimmedSpatialWidths, trimmedSpatialWidths,
      centeredSpatialWidths, splitPhysicalSpatialInputScale, trimmedSpatialRootScale,
      trimmedSpatialSlopeScale, one_mul] <;> ring

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

variable {G J X : Type*} [Fintype G] [Fintype J] [Fintype X] [DecidableEq X]
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
variable (N : X → ℕ) (hN : ∀ x, 0 < N x)
variable (hτ1 : τ ≤ 1 / 2) (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))

variable {dim : ℕ} (root : G ⊕ J → ℤ) (dirs : Matrix (Fin dim) (G ⊕ J) ℤ)
variable (hsite : ∀ s : Finset (Fin dim), (∑ k, |(integerAffineCube root dirs s k : ℝ)|) ≤ W)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (c : LayerSamplerVariables G I n B → ℤ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hx : ∀ g, (integerScalarCubeWeights (Fin dim) S.value S.positive).weight (x g) ≠ 0)
variable (hy : (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).weight y ≠ 0)

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {W τ ξ : ℝ} (hbudget : allocatedPhysicalRootBudget B U b S c ≤ W)
variable (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (N : X → ℕ) (hN : ∀ a, 0 < N a)
variable (hτ1 : τ ≤ 1 / 2) (hsize : ∀ a, 4 ≤ τ * (N a : ℝ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

theorem allocatedNarrowTrimmed_kernel_error (selection : α ↪ G) {M : ℕ}
    {X : Type*} (N q : X → ℕ) (d : X) (hN : ∀ a, 0 < N a) (hq : ∀ a, 0 < q a)
    {W τ κ C₀ ρ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hsize : 8 * (1 + W) * (q d : ℝ) * ρ ≤ (ξ * τ) * (N d : ℝ))
    (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ) :
    let H := trimmedSpatialRootScale τ N q d
    let T := trimmedSpatialSlopeScale W τ N q d
    let hs := trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    ∀ v, |(∏ i, physicalSpatialOutputScale α H T S.value i) *
        (smoothMatrixImagePMF (physicalCubeCoefficient root dirs)
          (fun k => residueProfileWidth q V (k, d))
          (fun k => residueProfileWidth_pos q V hq hV (k, d)) v).toReal -
      maskedIntegerImageDensity (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection) cols)
        (physicalSpatialOutputScale α H T S.value)
        (anisotropicSpatialKernelDensity selection ker (scalarCubeDifferenceMatrix x) hp H T S.value
          hs.1 hs.2 (Nat.cast_pos.mpr S.positive)) v| ≤
      anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M κ C₀ ρ ξ := by
  intro H T hs V hV hp
  have hWT : W * T ≤ H := by
    change W * T ≤ trimmedSpatialRootScale τ N q d
    rw [trimmedSpatial_scale_ratio hW]
    exact mul_le_mul_of_nonneg_right (by linarith) hs.2.le
  have hscale := narrowTrimmedSpatial_scale_lower hW hτ hξ1 hρ.le N q d (hN d) (hq d) hsize
  have h := allocatedPhysicalCube_narrow_error B U basis S c x y selection hs.1 hs.2 hκ hρ
    hx hC₀ hLC hbudget hWT hWC hξ hξ1 hscale.1 hscale.2.2 hmesh
  simpa only [H, T, V, ← narrowTrimmedSpatial_residue_scale W τ ξ N q d] using h

theorem allocatedNarrowTrimmed_shifted_vector_site_error (selection : α ↪ G) {M : ℕ}
    {X : Type*} [Fintype X] (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ κ C₀ ρ ξ δ b r : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hsize : ∀ d, 8 * (1 + W) * (q d : ℝ) * ρ ≤ (ξ * τ) * (N d : ℝ))
    (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (modulus : ℕ) [NeZero modulus]
    (hperiod : integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection))
    (residue : Option vars × X → ℤ) (hresidue : ∀ k d, |(residue (k,d) : ℝ)| ≤ q d)
    (hCR : ∀ d, integerResidueMatrix cols (q d * modulus) =
      integerResidueMatrix refcols (q d * modulus))
    (hδ : 0 ≤ δ)
    (hmove : ∀ d i, (∑ j, |((cols i j - refcols i j : ℤ) : ℝ)|) ≤
      δ * trimmedSpatialRootScale τ N q d)
    (hb : 0 < b) (hr : 0 < r) (v : X → (Unit ⊕ α) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / trimmedSpatialRootScale τ N q d| ≤ b) :
    let H := fun d => trimmedSpatialRootScale τ N q d
    let T := fun d => trimmedSpatialSlopeScale W τ N q d
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let Q := residueProfileWidth q V
    let hQ := residueProfileWidth_pos q V hq hV
    let hpivot := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hpivot W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let E := anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M κ C₀ ρ ξ
    let G₀ := (modulus : ℝ) ^ Fintype.card (Unit ⊕ α)
    let shift := physicalResidueOffsetShift root (allocatedPhysicalCubeRoot B U basis S c x y₀)
      dirs (allocatedPhysicalCubeDirections B U basis S x y₀) residue q
    let E' := E + G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * δ
    ‖(((∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) S.value i) *
        (((smoothProductPMF Q hQ).map (fun z d => physicalCubeCoefficient root dirs *ᵥ
          (fun k => z (k, d)))) (v - shift)).toReal : ℝ) : ℂ) -
      ∏ d, spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix refcols modulus))) modulus f (H d) b r (v d)‖ ≤
      Fintype.card X * (E' + 4 * G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * r) *
        (1 + G₀ * anisotropicSpatialDensityCap selection κ + E') ^ Fintype.card X := by
  classical
  intro H T V hV Q hQ hpivot f E G₀ shift E'
  have hH (d) : 0 < H d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1
  have hT (d) : 0 < T d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).2
  have hroot (g : G) : |(ker g : ℝ)| ≤ 1 + W := by
    have h : |(ker g : ℝ)| ≤ W :=
      (allocatedPhysicalCube_root_budget B U basis S c x y (.inl g)).trans hbudget
    linarith
  have hD (i : α) (g : G) : |(scalarCubeDifferenceMatrix x i g : ℝ)| ≤ S.value :=
    allocatedPhysicalCube_directions_bound B U basis S x y i (.inl g)
  have hminor : κ ≤ |(Matrix.of (fun i j => (scalarCubeDifferenceMatrix x i (selection j) : ℝ) /
      (S.value : ℝ))).det| := by
    change κ ≤ |(normalizedScalarCubePivot selection x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  have hE : 0 ≤ E := anisotropicSpatialError_nonneg selection _ M hκ.le
    (zero_le_one.trans hC₀) hρ.le hξ.le
  have hpoint (d) := allocatedNarrowTrimmed_kernel_error B U basis S c x y selection N q d hN hq
    hW hτ hκ hρ hx hbudget hC₀ hLC hWC hξ hξ1 (hsize d) hmesh
  have hshift : shift = fun d => residueMatrixShift cols refcols (q d)
      (fun j => residue (some (Sum.inr j), d)) :=
    allocatedPhysicalResidue_shift_principal B U basis S c x y y₀ residue q
  rw [hshift, smoothProductPMF_matrix_image_scaled]
  exact canonicalVectorSpatialSiteApprox_shift_error selection ker (scalarCubeDifferenceMatrix x) hpivot
    (fun _ => cols) (fun _ => refcols) H T hH hT hW (Nat.cast_pos.mpr S.positive)
    (by exact_mod_cast S.positive) hκ (fun d => trimmedSpatial_scale_ratio hW N q d)
    hroot hD hminor modulus hperiod q hq (fun d j => residue (some (Sum.inr j), d))
    (fun d j => hresidue (some (Sum.inr j)) d) hCR hδ hmove _ hE hb hr hpoint v hv

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

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_shifted_vector_site_error.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_shifted_vector_site_error.{u_1, u_2, u_3, u_4, u_5, u_6}
