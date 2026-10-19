-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedRecentered_probability_mass_of_rank_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:36:41.562997+00:00
-- url     : https://prove2.me/submissions/749f6392-a658-4df5-bae8-a638e818e143

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B178
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_BooleanCubeKernel_referenceJetEnvelopeWidths_trimmed_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialScales
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem trimmedSpatial_scale_ratio {X : Type*} {B τ : ℝ} (hB : 0 ≤ B)
    (N modulus : X → ℕ) (x : X) :
    trimmedSpatialRootScale τ N modulus x =
      (1 + B) * trimmedSpatialSlopeScale B τ N modulus x := by
  have hb : 1 + B ≠ 0 := ne_of_gt (by linarith)
  unfold trimmedSpatialRootScale trimmedSpatialSlopeScale
  field_simp

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalAmbientVolumeRatio
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalSpatial_uniform_volume {X α : Type*} [Fintype X] [Fintype α]
    (H T : X → ℝ) {W L : ℝ} (hL : L ≠ 0) (hscale : ∀ d, H d = (1 + W) * T d) :
    (∏ d, ∏ _i : Unit ⊕ α, H d) =
      (((1 + W) / L) ^ Fintype.card α) ^ Fintype.card X *
        ∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) L i := by
  have hrow (d) : (∏ _i : Unit ⊕ α, H d) =
      ((1 + W) / L) ^ Fintype.card α * ∏ i, physicalSpatialOutputScale α (H d) (T d) L i := by
    simp only [Fintype.prod_sum_type, physicalSpatialOutputScale, Sum.elim_inl, Sum.elim_inr,
      Finset.prod_const, Finset.card_univ, Fintype.card_unique, pow_one]
    have he : (1 + W) / L * (L * T d) = H d := by rw [hscale d]; field_simp
    rw [mul_left_comm _ (H d), ← mul_pow, he]
    simp only [Fintype.card_sum, Fintype.card_unique, pow_add, pow_one]
  simp_rw [hrow]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedReferenceJetMass
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem reference_density_spatial_error {K X Y : Type*} [Fintype K] [Fintype X] {q : ℕ}
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern (Option K) X stride))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (base : X → ℤ)
    (H T : X → ℝ) {L : ℝ}
    (hA : 0 < ∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i)
    (point : (X → (Unit ⊕ Fin q) → ℤ) → Y) (g : Y → ℝ) (hg : ∀ y, 0 ≤ g y)
    (test : (X → (Unit ⊕ Fin q) → ℤ) → ℂ) (htest : ∀ v, ‖test v‖ ≤ 1)
    {E C : ℝ} (hE : 0 ≤ E)
    (hmass : ∀ a : cells, (∑ v ∈ spatialWindow H 4, g (point
      (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative stride a.val) stride v))) ≤
        C * (∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i)) :
    (∑ a : cells, selectedResidueCellWeight stride cells V a *
      ((E / (∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i)) *
        ∑ v ∈ spatialWindow H 4,
          ‖test (physicalResidueReconstruction root D base
            (boundedColumnResidueRepresentative stride a.val) stride v)‖ *
          g (point (physicalResidueReconstruction root D base
            (boundedColumnResidueRepresentative stride a.val) stride v)))) ≤ E * C := by
  let A := ∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i
  have hbound (a : cells) : (E / A) * (∑ v ∈ spatialWindow H 4,
      ‖test (physicalResidueReconstruction root D base
        (boundedColumnResidueRepresentative stride a.val) stride v)‖ *
      g (point (physicalResidueReconstruction root D base
        (boundedColumnResidueRepresentative stride a.val) stride v))) ≤ E * C := by
    have hs : (∑ v ∈ spatialWindow H 4,
        ‖test (physicalResidueReconstruction root D base
          (boundedColumnResidueRepresentative stride a.val) stride v)‖ *
        g (point (physicalResidueReconstruction root D base
          (boundedColumnResidueRepresentative stride a.val) stride v))) ≤ C * A := by
      apply le_trans _ (hmass a)
      apply Finset.sum_le_sum
      intro v _
      exact (mul_le_mul_of_nonneg_right (htest _) (hg _)).trans_eq (one_mul _)
    have h := mul_le_mul_of_nonneg_left hs (div_nonneg hE hA.le)
    have hA0 : A ≠ 0 := hA.ne'
    have he : E / A * (C * A) = E * C := by field_simp [hA0]
    exact h.trans_eq he
  calc
    _ ≤ ∑ a : cells, selectedResidueCellWeight stride cells V a * (E * C) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hbound a)
        (selectedResidueCellWeight_nonneg stride cells V a))
    _ = (∑ a : cells, selectedResidueCellWeight stride cells V a) * (E * C) :=
      (Finset.sum_mul _ _ _).symm
    _ = E * C := by rw [selectedResidueCellWeight_sum stride cells V hV hZ, one_mul]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem coarse_reference_density_spatial_error {K X Y : Type*} [Fintype K] [Fintype X] {q : ℕ}
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern (Option K) X stride))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (base : X → ℤ)
    (H T : X → ℝ) {W L : ℝ} (hL : L ≠ 0) (hscale : ∀ x, H x = (1 + W) * T x)
    (hA : 0 < ∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i)
    (point : (X → (Unit ⊕ Fin q) → ℤ) → Y) (g : Y → ℝ) (hg : ∀ y, 0 ≤ g y)
    (test : (X → (Unit ⊕ Fin q) → ℤ) → ℂ) (htest : ∀ v, ‖test v‖ ≤ 1)
    {E : ℝ} (hE : 0 ≤ E)
    (hmass : ∀ a : cells, (∑ v ∈ spatialWindow H 4, g (point
      (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative stride a.val) stride v))) ≤
        (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) *
          (∏ x, ∏ _i : Unit ⊕ Fin q, H x)) :
    (∑ a : cells, selectedResidueCellWeight stride cells V a *
      ((E / (∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) L i)) *
        ∑ v ∈ spatialWindow H 4,
          ‖test (physicalResidueReconstruction root D base
            (boundedColumnResidueRepresentative stride a.val) stride v)‖ *
          g (point (physicalResidueReconstruction root D base
            (boundedColumnResidueRepresentative stride a.val) stride v)))) ≤
      E * coarseReferenceMassConstant q X W L := by
  apply reference_density_spatial_error stride cells V hV hZ root D base H T hA point g hg test htest hE
  intro a
  have h := hmass a
  rw [physicalSpatial_uniform_volume H T hL hscale] at h
  simpa only [coarseReferenceMassConstant, Fintype.card_fin, mul_assoc] using h

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSlicedSpatialToCoarse
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
  pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
    (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (htest : ∀ v, ‖test v‖ ≤ 1)

include hN hq hτ hξ hW hmass in
omit [DecidableEq G] [NeZero modulus] in
theorem allocatedRecenteredProfileMass_le_of_window_law
    (law : FiniteProbabilityWeights fullTuple)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    (hwindow : ∀ y, law.weight y ≠ 0 → ∀ a : cells,
      (∑ v ∈ window, ‖profile y (point (allocatedWholeResidueReconstruction B U b S X modulus q
        wholeReference x base (principalResidueLabel refined y) a.val v))‖) ≤
        (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) *
          (∏ t, ∏ _i : Unit ⊕ Fin dim, trimmedSpatialRootScale τ N q t)) :
    law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) ≤
      coarseReferenceMassConstant dim X W S.value := by
  rw [← law.mean_const (coarseReferenceMassConstant dim X W S.value)]
  apply law.mean_mono_on_support
  intro y hy
  let y₀ := wholeReference (principalResidueLabel refined y)
  have hA : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i := by
    apply Finset.prod_pos
    intro t _
    apply Finset.prod_pos
    intro i _
    have hp := trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)
    exact physicalSpatialOutputScale_pos (Fin dim) hp.1 hp.2 (Nat.cast_pos.mpr S.positive) i
  have he := coarse_reference_density_spatial_error q cells
    (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
    (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
    (allocatedPhysicalCubeDirections B U b S x y₀) base
    (trimmedSpatialRootScale τ N q) (trimmedSpatialSlopeScale W τ N q)
    (Nat.cast_pos.mpr S.positive).ne' (trimmedSpatial_scale_ratio hW N q) hA
    point (fun z => ‖profile y z‖) (fun _ => norm_nonneg _) (fun _ => (1 : ℂ))
    (fun _ => by simp) (E := 1) (by norm_num) (hwindow y hy)
  simpa only [allocatedRecenteredProfileMass, allocatedWholeResidueReconstruction,
    norm_one, one_mul, one_div_mul_eq_div, y₀] using he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedCanonicalSlicedProbabilitySource
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uX uJ uO uG uI uB

open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type uO} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))
variable (hinj : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)
variable (cover : ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
local notation "point" => physicalCubeRowSample U cover rows poly hm
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "jetHaar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))

include hinj hcard hp μ hW in
omit [DecidableEq G] [NeZero modulus] in
theorem allocatedRecentered_probability_mass_of_rank_s2_oai [DecidableEq G] [NeZero modulus]
    (law : FiniteProbabilityWeights fullTuple)
    (g : fullTuple → EuclideanJetLayers U O → ℝ)
    (hg0 : ∀ y z, 0 ≤ g y z) (hgi : ∀ y, Integrable (g y) jetHaar)
    (hgmass : ∀ y, (∫ z, g y z ∂jetHaar) = 1)
    (Lf Cf : ℝ≥0)
    (hambient : ∀ y, ∃ f : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
      LipschitzWith Lf f ∧ (∀ z, ‖f z‖ ≤ Cf) ∧
      ∀ z, (g y z : ℂ) = f (coveredJetAmbientTorus U 1 z))
    (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ) (hξ : 0 < ξ)
    {P Rrank Sstride εsample η : ℝ}
    (hP : 0 ≤ P) (hX : (Fintype.card X : ℝ) ≤ P)
    (hframe : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (hcover : 0 < cover) (hcoverP : (cover : ℝ) ≤ Real.exp P)
    (hSstride : 0 ≤ Sstride) (hSstrideP : Sstride ≤ Real.exp P)
    (hstride : ∀ i, (q i : ℝ) ≤ Sstride)
    (hε : 0 < εsample) (hτP : 1 / τ ≤ Real.exp P) (hεP : 1 / εsample ≤ Real.exp P)
    (hsize : ∀ i, Real.exp ((P + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRrank : Real.exp ((P + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)) ≤ Rrank)
    (hη : 0 < η) (hamb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ P)
    (hLf : (Lf : ℝ) ≤ Real.exp P) (hCf : (Cf : ℝ) ≤ Real.exp P)
    (hjet : ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hηP : η⁻¹ ≤ Real.exp P) (hsmall : 2 * η + εsample ≤ 3)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (hrowsize : ∀ y : fullTuple, ∀ t i,
      (∑ k, |(physicalCubeCoefficient (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) i k : ℝ)|) ≤ trimmedSpatialRootScale τ N q t)
    (hscale : ∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * trimmedSpatialRootScale τ N q t) :
    law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point (fun y z => (g y z : ℂ))) ≤
      coarseReferenceMassConstant dim X W S.value := by
  apply allocatedRecenteredProfileMass_le_of_window_law B U b S X modulus q wholeReference
    x N hW base cells point hN hq hτ hξ hmass law (fun y z => (g y z : ℂ))
  intro y _ a
  obtain ⟨f, hf, hfb, hactual⟩ := hambient y
  let y₀ := wholeReference (principalResidueLabel refined y)
  have hwidth (z : Option (Fin dim) × X) : τ * (N z.2 : ℝ) ≤
      referenceJetEnvelopeWidths q (trimmedSpatialRootScale τ N q) z := by
    rw [referenceJetEnvelopeWidths_trimmed_s2 q N hq τ z]
    nlinarith [mul_pos hτ (Nat.cast_pos.mpr (hN z.2))]
  have hsample := (Classical.choose_spec
    (exists_translated_physical_jet_density_window_mass.{uX,uJ,uO,max uG uI uB} m dim)).2
      (I := X) (J := J) (O := O)
  have he := hsample rows hinj hcard hP hX hframe U μ ν base poly hp hm cover hcover hcoverP q hq
    hSstride hSstrideP hτ hε hτP hεP hstride (fun i => (N i : ℝ)) hsize hrank hRrank
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
    (allocatedPhysicalCubeDirections B U b S x y₀) a.val (trimmedSpatialRootScale τ N q)
    (fun t => (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).1)
    (hrowsize y₀) hscale hwidth (g y) (hg0 y) (hgi y) (hgmass y)
    f Lf Cf hf hfb hactual hη hamb hLf hCf hjet hηP hsmall
  simpa only [Complex.norm_real, Real.norm_of_nonneg (hg0 y _),
    allocatedWholeResidueReconstruction, y₀] using he

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uX, uJ, uO, uG, uI, uB} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedRecentered_probability_mass_of_rank_s2_oai.{uX, uJ, uO, uG, uI, uB} := @OAI.Erdos3.VectorPolynomial.allocatedRecentered_probability_mass_of_rank_s2_oai.{uX, uJ, uO, uG, uI, uB}
