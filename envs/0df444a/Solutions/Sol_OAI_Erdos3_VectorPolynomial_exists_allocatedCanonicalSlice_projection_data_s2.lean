-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_projection_data_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:42:13.806989+00:00
-- url     : https://prove2.me/submissions/bedfc7d6-218d-4b2b-889c-b369c28fff3f

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B245

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalUniformCoarseSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

universe uX uJ uO uG uI uB
open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal
attribute [local instance 2000] fullBooleanRowSetFintype

private theorem canonical_rows_ambient_reinstance
    {m dim : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) {Y : Type*}
    (v : Y → EuclideanJetLayers U
      (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)) → ℂ)
    (L : ℝ≥0) (C : ℝ) (L' : ℝ≥0) (C' : ℝ) (hL : L ≤ L') (hC : C ≤ C')
    (h : letI : ∀ j : Fin m, Fintype (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type) :=
          fun j => Subtype.fintype (fun t : Finset (Fin dim) => t ∈ boundedBooleanJetRows (Fin dim) (j.val + 1))
        ∀ y, ∃ f : (JetAmbientIndex
          (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)) J → UnitAddCircle) → ℂ,
          LipschitzWith L f ∧ (∀ z, ‖f z‖ ≤ C) ∧
          ∀ z, v y z = f (coveredJetAmbientTorus U 1 z)) :
    ∀ y, ∃ f : (JetAmbientIndex
      (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)) J → UnitAddCircle) → ℂ,
      LipschitzWith L' f ∧ (∀ z, ‖f z‖ ≤ C') ∧
      ∀ z, v y z = f (coveredJetAmbientTorus U 1 z) := by
  let property (inst : ∀ j : Fin m, Fintype (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)) : Prop :=
    letI := inst
    ∀ y, ∃ f : (JetAmbientIndex
      (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)) J → UnitAddCircle) → ℂ,
      LipschitzWith L f ∧ (∀ z, ‖f z‖ ≤ C) ∧
      ∀ z, v y z = f (coveredJetAmbientTorus U 1 z)
  have hinst : (fun j : Fin m =>
      Subtype.fintype (fun t : Finset (Fin dim) => t ∈ boundedBooleanJetRows (Fin dim) (j.val + 1))) =
      (fun j : Fin m => fullBooleanRowSetFintype dim (j.val + 1)) := Subsingleton.elim _ _
  have hsame : property (fun j : Fin m => fullBooleanRowSetFintype dim (j.val + 1)) :=
    Eq.mp (congrArg property hinst) h
  intro y
  obtain ⟨f, hf, hbound, heq⟩ := hsame y
  exact ⟨f, hf.weaken hL, fun z => (hbound z).trans hC, heq⟩

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (Cproj Vproj : Fin m → ℝ≥0)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) (q : X → ℕ)

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) →
  ZMod (residueRefinedPeriod modulus q))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel (residueRefinedPeriod modulus q) y = label₀)))
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hy₀ : 0 < (containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
  hH hsubset (residueRefinedPeriod modulus q) label₀ hcell).weight y₀)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (hcanonical : modulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
local notation "O" => (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (Fin.val j + 1) : Type))
local notation "rows" => (fun j => (Subtype.val : O j → Finset (Fin dim)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
variable (signal : (X → ℤ) → ℂ) (hsignal : ∀ u, ‖signal u‖ ≤ 1)

variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)

variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "jetHaar" => Measure.pi (fun j => @Measure.pi (O j) _
  (fullBooleanRowSetFintype dim (Fin.val j + 1)) _ (fun _ : O j => ν j))

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)]
variable [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
variable (μcoeff : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μcoeff.IsAddLeftInvariant] [IsProbabilityMeasure μcoeff]

include μ in
theorem exists_allocatedCanonicalSlice_projection_data_s2_oai
    {Pproj Pk : ℝ} (hPproj0 : 0 ≤ Pproj) (hGproj : (Fintype.card G : ℝ) ≤ Pproj)
    (hLproj : (S.value : ℝ) ≤ Real.exp Pproj)
    (hMkPk : (M : ℝ) ≤ Real.exp Pk) (hperiodP : ((m + 1 : ℕ) : ℝ) * Pk ≤ Pproj)
    (hCactual : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ Cproj j * ‖z‖)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vproj j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (Lf Cf : ℝ≥0)
    :
    let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim)
    let coverLog := (Pproj + (dim + 2 : ℕ) + Acover) ^ Acover
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value Vproj : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) Cproj Vproj *
      allocatedAmbientFactorCap (G := G) B R σ S.value Vproj ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin dim)) : ℝ≥0) * Real.toNNReal (Real.exp coverLog)
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin dim) (j.val + 1)) : ℝ≥0)
    densityLip * sectionLip * reconstructionLip ≤ Lf → cap ≤ Cf →

    ∃ cover : ℕ, kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m) ∣ cover ∧ 0 < cover ∧ (cover : ℝ) ≤ Real.exp coverLog ∧
    ∃ g : fullTuple → EuclideanJetLayers U O → ℝ,
      (∀ y, Continuous (g y)) ∧
      (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) jetHaar) ∧
      (∀ y, (∫ z, g y z ∂jetHaar) = 1) ∧
      (∀ y, (realDensityMeasure μcoeff (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) cover z))).map
          (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) rows) = realDensityMeasure jetHaar (g y)) ∧
      (∀ y, ∃ f : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
        LipschitzWith Lf f ∧ (∀ z, ‖f z‖ ≤ Cf) ∧
        ∀ z, (g y z : ℂ) = f (coveredJetAmbientTorus U 1 z)) ∧
      (∀ law₁ : FiniteProbabilityWeights fullTuple,
        ∃ F : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
          LipschitzWith Lf F ∧ (∀ z, ‖F z‖ ≤ Cf) ∧
          ∀ z, law₁.complexMean (fun y => (g y z : ℂ)) = F (coveredJetAmbientTorus U 1 z)) ∧
      AllocatedSlicedSourceProjection.{uX} B U b S x hb o hR hσ Cproj Vproj cover g
        (Classical.choose (Classical.choose_spec
          (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim))) Pproj := by
  intro Acover coverLog cap densityLip sectionLip reconstructionLip hLipBudget hCfBudget
  obtain ⟨cover, hdiv, hcover, hcoverBound, hdata⟩ :=
    (Classical.choose_spec (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim))).2.2
      (G := G) (I := I) (n := n) (J := J) B U b S x
    hPproj0 hGproj hLproj selection hx hMkPk hperiodP
  obtain ⟨g, hcontinuous, hcap, hgi, hgmass, hglaw, hphysical, hambient, hmean, hprojection⟩ :=
    hdata hb o hR hσ Cproj Vproj hCactual hVactual hσ1 Cinv hCinv hchart hsmall μcoeff ν μ
  have hrowInst (j : Fin m) :
      Subtype.fintype (fun s : Finset (Fin dim) => s ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)) =
        fullBooleanRowSetFintype dim (j.val + 1) := Subsingleton.elim _ _
  have hHaar :
      Measure.pi (fun j : Fin m => @Measure.pi (O j) _
        (Subtype.fintype (fun t : Finset (Fin dim) => t ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)))
        _ (fun _ : O j => ν j)) = jetHaar := by
    congr 1
    funext j
    exact congrArg (fun inst => @Measure.pi (O j) _ inst _ (fun _ : O j => ν j)) (hrowInst j)
  rw [hHaar] at hgi hgmass hglaw
  have hambient' := canonical_rows_ambient_reinstance (m := m) (dim := dim) (J := J) U
    (fun y z => (g y z : ℂ)) (densityLip * sectionLip * reconstructionLip) cap Lf Cf
    hLipBudget hCfBudget hambient
  have hmean' := canonical_rows_ambient_reinstance (m := m) (dim := dim) (J := J) U
    (fun (law₁ : FiniteProbabilityWeights fullTuple) z => law₁.complexMean (fun y => (g y z : ℂ)))
    (densityLip * sectionLip * reconstructionLip) cap Lf Cf hLipBudget hCfBudget hmean
  with_reducible exact ⟨cover, hdiv, hcover, hcoverBound, g, hcontinuous, hcap, hgi, hgmass, hglaw, hambient', hmean', hprojection⟩

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uX, uJ, uG, uI, uB} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_projection_data_s2_oai.{uX, uJ, uG, uI, uB} := @OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_projection_data_s2_oai.{uX, uJ, uG, uI, uB}
