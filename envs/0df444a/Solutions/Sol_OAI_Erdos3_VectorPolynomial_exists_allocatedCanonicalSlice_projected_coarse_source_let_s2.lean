-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_projected_coarse_source_let_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T10:24:15.147614+00:00
-- url     : https://prove2.me/submissions/d1be8260-1142-45bb-8f37-e327f4cdc9df

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B245
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedSlicedSourceProjection_canonical_coarse_source_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedCanonicalSlice_projection_data_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalUniformCoarseSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

universe uX uJ uO uG uI uB
open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal
attribute [local instance 2000] fullBooleanRowSetFintype

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
local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

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
local notation "law" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
  hH hsubset refined label₀ hcell
local notation "wholeReference" => (fun _ : labels => y₀)

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
local notation "point" d => physicalCubeRowSample U d rows poly hm
variable (signal : (X → ℤ) → ℂ) (hsignal : ∀ u, ‖signal u‖ ≤ 1)
local notation "test" => physicalCubeSiteTest (integerSelfSiteTest dim signal)

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

local notation "spatialError" => allocatedTupleSpatialError (Fintype.card X) selection
  (PrincipalTupleIndex B (layerSamplerDegree I n)) M modulus C₀ ρ ξ W δ mesh
local notation "boundaryError" => (24 * (probabilityProfileLipschitz : ℝ) *
  Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ)

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

include hp μ hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8
  hcanonical hδ hρshift hρmove hmeshpos hy₀ hsignal in

theorem _root_.solution
    {Pproj Pk : ℝ} (hGproj : (Fintype.card G : ℝ) ≤ Pproj)
    (hLproj : (S.value : ℝ) ≤ Real.exp Pproj)
    (hMkPk : (M : ℝ) ≤ Real.exp Pk) (hperiodP : ((m + 1 : ℕ) : ℝ) * Pk ≤ Pproj)
    (hCactual : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ Cproj j * ‖z‖)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vproj j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (Lf Cf : ℝ≥0)
    {Pmass Rrank : ℝ} (hPmass : 0 ≤ Pmass)
    (hXmass : (Fintype.card X : ℝ) ≤ Pmass)
    (hframe : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Pmass)
    (hstrideP : ∀ i, (q i : ℝ) ≤ Real.exp Pmass)
    (hτP : 1 / τ ≤ Real.exp Pmass)
    (hsizeMass : ∀ i, Real.exp ((Pmass + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,0,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,0,max uG uI uB} m dim)) ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRrank : Real.exp ((Pmass + Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,0,max uG uI uB} m dim)) ^ Classical.choose
      (exists_translated_physical_jet_density_window_mass.{uX,uJ,0,max uG uI uB} m dim)) ≤ Rrank)
    (hamb : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Pmass)
    (hLf : (Lf : ℝ) ≤ Real.exp Pmass) (hCf : (Cf : ℝ) ≤ Real.exp Pmass)
    (hjet : ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Pmass)
    {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hcapBudget : (allocatedAmbientFactorCap (G := G) B R σ S.value Vproj : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) ≤ Cg)
    {target κ : ℝ}
    (hboundary : Cg * boundaryError ≤ normalizedSpatialShare target / 2)
    (hsite : spatialError * coarseReferenceMassConstant dim X W S.value ≤ normalizedSpatialShare target / 2)
    {p E : ℝ} (hpBudget : 0 ≤ p) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hMP : (M : ℝ) ≤ Real.exp p)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p)
    (hWscale : W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ))
    (hmeshCoarse : mesh ≤ allocatedEarlyRecenteredMesh X selection M modulus p E)
    (hPproj : 1 ≤ Pproj) (hmProj : (m : ℝ) ≤ Pproj)
    (hKproj : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pproj)
    (hWproj : W ≤ Real.exp Pproj)
    (hRproj : ∀ j, (R j)⁻¹ ≤ Real.exp Pproj) (hσproj : ∀ j, (σ j)⁻¹ ≤ Real.exp Pproj)
    (hcountProj : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pproj)
    (hIproj : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pproj) (hnProj : ∀ j, (n j : ℝ) ≤ Pproj)
    (hJproj : ∀ j, (Fintype.card (J j) : ℝ) ≤ Pproj)
    (hProfileProj : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pproj)
    (hCproj : ∀ j, (Cproj j : ℝ) ≤ Real.exp Pproj) (hVproj : ∀ j, (Vproj j : ℝ) ≤ Real.exp Pproj)
    (hXproj : (Fintype.card X : ℝ) ≤ Pproj)
    (hFrameProj : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Pproj)
    (hStrideProj : ∀ i, (q i : ℝ) ≤ Real.exp Pproj)
    (hτProj : τ⁻¹ ≤ Real.exp Pproj) (hξProj : ξ⁻¹ ≤ Real.exp Pproj)


    (hCells : cells.Nonempty) (bases : Finset (X → ℤ)) (hbases : bases.Nonempty) :
    let Aproj := Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim))
    (∀ i, Real.exp ((Pproj + Aproj) ^ Aproj) ≤ (N i : ℝ)) →
    Real.exp ((Pproj + Aproj) ^ Aproj) ≤ Rrank →
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
    coverLog ≤ Pmass → densityLip * sectionLip * reconstructionLip ≤ Lf → cap ≤ Cf →

    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let Z := selectedJointDensityMass bases q cells V
      (allocatedJointBaseDensity B U b hb o hR hσ S X poly hm)
    κ ≤ ((law).complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hm
      N hN hW hτ hξ q cells hmass bases x y signal)).re →
    ∃ cover : ℕ, modulus ∣ cover ∧ 0 < cover ∧ (cover : ℝ) ≤ Real.exp coverLog ∧
    ∃ g : fullTuple → EuclideanJetLayers U O → ℝ,
      (∀ y, Continuous (g y)) ∧
      (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) jetHaar) ∧
      (∀ y, (∫ z, g y z ∂jetHaar) = 1) ∧
      (∀ y, (realDensityMeasure μcoeff (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) cover z))).map
          (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) rows) = realDensityMeasure jetHaar (g y)) ∧
      (∀ law₁ : FiniteProbabilityWeights fullTuple,
        ∃ F : (JetAmbientIndex O J → UnitAddCircle) → ℂ,
          LipschitzWith Lf F ∧ (∀ z, ‖F z‖ ≤ Cf) ∧
          ∀ z, law₁.complexMean (fun y => (g y z : ℂ)) = F (coveredJetAmbientTorus U 1 z)) ∧
    ∃ base ∈ bases, Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
      Z * (κ - Real.exp (-Pproj) - Real.exp (-target)) - Real.exp (-E) ≤
        ((law).complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
          B U b S X modulus q wholeReference x hM selection hx N hW
          (allocatedEarlyRecenteredMesh X selection M modulus p E) base cells (point cover) test
          (fun y z => (g y z : ℂ)))).re := by
  intro Aproj hSizeProj hRankProj
  intro Acover coverLog cap densityLip sectionLip reconstructionLip hcoverLog hLipBudget hCfBudget V Z hsource
  have hPproj0 : 0 ≤ Pproj := zero_le_one.trans hPproj
  obtain ⟨cover, hdiv, hcover, hcoverBound, g, hcontinuous, hcap, hgi, hgmass,
      hglaw, hambient', hmean', hprojection⟩ :=
    exists_allocatedCanonicalSlice_projection_data_s2 B U b S hb o hR hσ Cproj Vproj x selection hx
      μ ν μcoeff hPproj0 hGproj hLproj hMkPk hperiodP
      hCactual hVactual hσ1 Cinv hCinv hchart hsmall Lf Cf hLipBudget hCfBudget
  have hcap' (y) (_hy : (law).weight y ≠ 0) (v) : ‖(g y ((point cover) v) : ℂ)‖ ≤ Cg := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hcap y _).1]
    exact (hcap y _).2.trans hcapBudget
  refine ⟨cover, ?_, hcover, hcoverBound, g, hcontinuous, hcap, hgi, hgmass, hglaw, hmean', ?_⟩
  · rwa [hcanonical]
  · with_reducible
      exact AllocatedSlicedSourceProjection.canonical_coarse_source_s2
        (B := B)
        (U := U)
        (b := b)
        (S := S)
        (hb := hb)
        (o := o)
        (hR := hR)
        (hσ := hσ)
        (Cproj := Cproj)
        (Vproj := Vproj)
        (X := X)
        (modulus := modulus)
        (q := q)
        (H := H)
        (step := step)
        (c := c)
        (hH := hH)
        (hsubset := hsubset)
        (label₀ := label₀)
        (hcell := hcell)
        (y₀ := y₀)
        (hy₀ := hy₀)
        (x := x)
        (hM := hM)
        (selection := selection)
        (hx := hx)
        (hcanonical := hcanonical)
        (N := N)
        (hW := hW)
        (mesh := mesh)
        (cells := cells)
        (poly := poly)
        (hp := hp)
        (hm := hm)
        (signal := signal)
        (hsignal := hsignal)
        (hN := hN)
        (hq := hq)
        (hτ := hτ)
        (hρ := hρ)
        (hbudget := hbudget)
        (hC₀ := hC₀)
        (hLC := hLC)
        (hWC := hWC)
        (hξ := hξ)
        (hξ1 := hξ1)
        (hsize := hsize)
        (hmesh := hmesh)
        (hρ8 := hρ8)
        (hδ := hδ)
        (hρshift := hρshift)
        (hρmove := hρmove)
        (hmeshpos := hmeshpos)
        (hmass := hmass)
        (μ := μ)
        (ν := ν)
        (Lf := Lf)
        (Cf := Cf)
        (hPmass := hPmass)
        (hXmass := hXmass)
        (hframe := hframe)
        (hstrideP := hstrideP)
        (hτP := hτP)
        (hsizeMass := hsizeMass)
        (hrank := hrank)
        (hRrank := hRrank)
        (hamb := hamb)
        (hLf := hLf)
        (hCf := hCf)
        (hjet := hjet)
        (hCg := hCg)
        (hboundary := hboundary)
        (hsite := hsite)
        (hpBudget := hpBudget)
        (hE := hE)
        (hG := hG)
        (hX := hX)
        (hdim := hdim)
        (hMP := hMP)
        (hvars := hvars)
        (hWscale := hWscale)
        (hmeshCoarse := hmeshCoarse)
        (hPproj := hPproj)
        (hmProj := hmProj)
        (hKproj := hKproj)
        (hWproj := hWproj)
        (hRproj := hRproj)
        (hσproj := hσproj)
        (hcountProj := hcountProj)
        (hIproj := hIproj)
        (hnProj := hnProj)
        (hJproj := hJproj)
        (hProfileProj := hProfileProj)
        (hCproj := hCproj)
        (hVproj := hVproj)
        (hXproj := hXproj)
        (hFrameProj := hFrameProj)
        (hStrideProj := hStrideProj)
        (hτProj := hτProj)
        (hξProj := hξProj)
        (hSizeProj := hSizeProj)
        (hRankProj := hRankProj)
        (hCells := hCells)
        (bases := bases)
        (hbases := hbases)
        (cover := cover) (g := g) (hg0 := fun y z => (Set.mem_Icc.mp (hcap y z)).1) (hgi := hgi)
        (hgmass := hgmass) (hambient := hambient') (hcover := hcover)
        (hcoverP := hcoverBound.trans (Real.exp_le_exp.mpr hcoverLog))
        (hcap := hcap') (hprojection := hprojection) hsource

end Erdos3.VectorPolynomial

end

end OAI
end

