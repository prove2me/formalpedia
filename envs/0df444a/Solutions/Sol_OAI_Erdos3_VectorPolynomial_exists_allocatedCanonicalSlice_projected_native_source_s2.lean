-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_projected_native_source_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T10:24:16.56807+00:00
-- url     : https://prove2.me/submissions/37d3124b-c463-4157-b0e3-170f195de2ca

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B277
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedCanonicalSlice_constructed_native_source_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedCanonicalSlice_uniform_projected_coarse_source_let_s2
import Theorems.Thm_OAI_Erdos3_canonicalSlicedModulus_good_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalProjectedNativeSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ uQ
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (selection : Fin (s + 1) ↪ G)
variable (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
variable (period : ℕ) [NeZero period] (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (hperiodCanonical : period = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hgood m))
variable (modulus : ℕ) (hmodulusRefined : modulus = residueRefinedPeriod period stride)
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := (Fin (s + 1))) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "wholeLaw" => containedSupportedProgressionLaw (α := Fin (s + 1)) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

include ν μ hb o bW hperiodCanonical hmodulusRefined μrows hR hσ hMk hgood hP hMkP hRP hRi hσi hcount in

theorem exists_allocatedCanonicalSlice_projected_native_source_s2_oai
    {D target Pk Prho F Qstride : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D)
    (hPk : 0 ≤ Pk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target) (hF : 0 ≤ F) (hQstride : 0 ≤ Qstride)
    (hstride : ∀ i, 0 < stride i) (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤ S.value)
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j)
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hq : Fintype.card (Fin (s + 1)) ≤ m + 1)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U basis S))
    (hy₀ : 0 < (wholeLaw).weight y₀)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) * ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4)))
    (siteRadius : ℝ≥0) (hrone : 1 ≤ siteRadius)
    (hsitebudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
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
    (hsites : (Fintype.card (Finset (Fin (s + 1))) : ℝ) ≤ baseAmbient)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ baseAmbient)
    (hlabels : (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤ Real.exp baseAmbient)
    (hKbase : (K : ℝ) ≤ Real.exp baseAmbient)
    (hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp baseAmbient)
    (hpbase : (period : ℝ) ≤ Real.exp baseAmbient)
    (hrowsAmbient : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ baseAmbient)
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp baseAmbient)
    (Qgrid : ℝ≥0) (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U basis S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U basis S a).1 (allocatedGridIntegerAxis B U basis S a).2) : ℝ) + 1) ≤ Qgrid)
    {δg : ℝ} (hδg : 0 < δg)
    (hdenseg : ∀ tg, δg * allocatedPrincipalSides B U basis S tg ≤ (H₀ tg : ℝ))
    (Tg : ℕ) (hQTg : (((Fintype.card (Fin (s + 1)) + 1) * modulus : ℕ) : ℝ) / δg ≤ Tg)
    (hstepAll : ∀ tg, 0 < step₀ tg)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition) (Pg : ℝ) (hPg : 1 ≤ Pg)
    (hcP : scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg)
    (hsP : scalarCubePrimitiveEnvelope (Fin (s + 1)) Ag 1 0 modulus ≤ Pg)
    (hstrideGrid : ∀ tg, ((step₀ tg * modulus : ℕ) : ℝ) ≤ Pg)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg tg pg : ℝ}
    (hDg : 0 ≤ Dg) (hvg : 0 ≤ vg) (hwg : 0 ≤ wg) (htg : 0 ≤ tg) (hpg : 0 ≤ pg)
    (hcube : (Fintype.card (Fin (s + 1)) : ℝ) ≤ Dg) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg) (hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : δg⁻¹ ≤ Real.exp wg) (hTg : (Tg : ℝ) ≤ Real.exp tg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (hPp₀ : Pg ≤ Real.exp pg) (haxesGrid : (Fintype.card {a // grid a} : ℝ) ≤ Dg)
    (hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ Dg)
    (hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ Dg)
    (hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ Dg)
    (hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ Dg)
    {Banalytic : ℝ} (hBanalytic : 0 ≤ Banalytic) (hDanalytic : Dg ≤ Banalytic)
    (hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Banalytic)
    (hcoordAnalytic : ((K * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Banalytic)
    (hgridAnalytic : (Qgrid : ℝ) ≤ Real.exp Banalytic)
    {Pnum : ℝ} (hPnum : 0 ≤ Pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum) (hn : ∀ j, (n j : ℝ) ≤ Pnum)
    (hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
    (hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
    (hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Real.exp Pnum)
    {gain Pproj coarseTarget Ecoarse pGain : ℝ}
    :
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin (s + 1)))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    ∀ {W τ ξn : ℝ} (hW : 0 ≤ W)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (signal : ((Fin nX) → ℤ) → ℂ),
    (∀ u ∈ integerBox N, ‖signal u‖ ≤ 1) →
    (∀ u, u ∉ integerBox N → signal u = 0) →
    ∀ {lossTarget Pphysical Dphysical Psample Rrank Sstride εsample ηsample : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → ∀ (hτ : 0 < τ),
    allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W →
    0 ≤ Psample → (Fintype.card (Fin nX) : ℝ) ≤ Psample →
    (Fintype.card (Option (Fin (s + 1)) × (Fin nX)) : ℝ) ≤ Psample →
    0 ≤ Sstride → Sstride ≤ Real.exp Psample → 0 < εsample →
    1 / τ ≤ Real.exp Psample → 1 / εsample ≤ Real.exp Psample →
    (∀ i, (stride i : ℝ) ≤ Sstride) →
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{0,uJ,0} m (s + 1))
    (∀ i, Real.exp ((Psample + A) ^ A) ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Psample →
    ambientBudget ≤ Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    (∀ z, 0 < V z) → ∀ (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z),
    ∀ {ρphysical : ℝ}, ξn ≤ 1 →
    (∀ t, 8 * (1 + W) * (stride t : ℝ) * ρphysical ≤ (ξn * τ) * (N t : ℝ)) →
    8 * (probabilityProfileLipschitz : ℝ) ≤ ρphysical →
    2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U basis S (fun _ => 0))) ≤ ρphysical →
    0 ≤ Pphysical → (Mk : ℝ) ≤ Real.exp Pphysical →
    (period : ℝ) ≤ Real.exp (Pphysical ^ 2) →
    (((s + 1) + 1 : ℕ) : ℝ) ≤ Pphysical → (Fintype.card G : ℝ) ≤ Pphysical →
    (Fintype.card (Fin nX) : ℝ) ≤ Pphysical → Dphysical ≤ Real.exp Pphysical →
    W ≤ Dphysical * S.value →
    lossTarget + coefficientErrorSpatialLog Pphysical + 8 ≤ target →
    ηsample ≤ Real.exp (-target) → εsample ≤ Real.exp (-target) →
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m (s + 1))
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m (s + 1))
    let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin (s + 1))) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * ((m + 1 : ℕ) * Pk))
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
    Dg ∈ Set.Icc 0 Pnative → p ∈ Set.Icc 0 Pnative → vg ∈ Set.Icc 0 Pnative →
    Fmodel ∈ Set.Icc 0 Pnative → Prho ∈ Set.Icc 0 Pnative → Pk ∈ Set.Icc 0 Pnative →
    target ∈ Set.Icc 0 Pnative → Banalytic ∈ Set.Icc 0 Pnative →
    Pphysical ∈ Set.Icc 0 Pnative → Ecoarse ∈ Set.Icc 0 Pnative → pGain ∈ Set.Icc 0 Pnative →
    ∀ (hξn : 0 < ξn),
    (∀ i, (stride i : ℝ) ≤ Real.exp Pphysical) →
    1 / τ ≤ Real.exp Pphysical →
    Real.exp (-pGain) / 2 ≤ gain →
    pGain + 32 ≤ Pproj → pGain + 32 ≤ coarseTarget →
    pGain + 32 ≤ Ecoarse → pGain + 32 ≤ lossTarget →
    ∀ (Cproj Vproj : Fin m → ℝ≥0),
    let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{0,uG,uI,uB,uJ} m (s + 1))
    let coverLog := (Pproj + ((s + 1) + 2 : ℕ) + Acover) ^ Acover
    let Asample := Classical.choose (exists_allocatedCanonicalProjection_composed_budget m (s + 1) Acover)
    let Pmass := (Pproj + Asample) ^ Asample
    coverLog ≤ baseAmbient → coverLog ≤ Psample → Pmass ≤ Psample →
    (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ Cproj j * ‖z‖) →
    (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vproj j) →
    (∀ j, σ j ≤ 1) →
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) →
    (Fintype.card (Fin nX) : ℝ) ≤ Pmass →
    (Fintype.card (Option (Fin (s + 1)) × Fin nX) : ℝ) ≤ Pmass →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pmass) → 1 / τ ≤ Real.exp Pmass →
    let AmassWindow := Classical.choose (exists_translated_physical_jet_density_window_mass.{0,uJ,0,max uG uI uB} m (s + 1))
    (∀ i, Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ (N i : ℝ)) →
    Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ Rrank →
    (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Pmass →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Pmass →
    ∀ {C₀ δspatial fineMesh : ℝ},
    0 < ρphysical → 1 ≤ C₀ → (S.value : ℝ) ≤ C₀ → W ≤ C₀ →
    anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρphysical →
    0 ≤ δspatial →
    Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U basis S (fun _ => 0)) ≤ δspatial * ρphysical →
    0 < fineMesh →
    Real.exp Pmass * (24 * (probabilityProfileLipschitz : ℝ) *
      Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) / ρphysical) ≤ normalizedSpatialShare coarseTarget / 2 →
    allocatedTupleSpatialError (Fintype.card (Fin nX)) selection
      (PrincipalTupleIndex B (layerSamplerDegree I n)) Mk period C₀ ρphysical ξn W δspatial fineMesh *
      coarseReferenceMassConstant (s + 1) (Fin nX) W S.value ≤ normalizedSpatialShare coarseTarget / 2 →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Pphysical →
    W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) →
    fineMesh ≤ allocatedEarlyRecenteredMesh (Fin nX) selection Mk period Pphysical Ecoarse →
    1 ≤ Pproj → (m : ℝ) ≤ Pproj →
    (Fintype.card G : ℝ) ≤ Pproj → (S.value : ℝ) ≤ Real.exp Pproj →
    ((m + 1 : ℕ) : ℝ) * Pk ≤ Pproj →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pproj → W ≤ Real.exp Pproj →
    (∀ j, (R j)⁻¹ ≤ Real.exp Pproj) → (∀ j, (σ j)⁻¹ ≤ Real.exp Pproj) →
    (∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pproj) →
    (∀ j, (Fintype.card (I j) : ℝ) ≤ Pproj) → (∀ j, (n j : ℝ) ≤ Pproj) →
    (∀ j, (Fintype.card (J j) : ℝ) ≤ Pproj) →
    (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pproj →
    (∀ j, (Cproj j : ℝ) ≤ Real.exp Pproj) → (∀ j, (Vproj j : ℝ) ≤ Real.exp Pproj) →
    (Fintype.card (Fin nX) : ℝ) ≤ Pproj →
    (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ Pproj →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pproj) → τ⁻¹ ≤ Real.exp Pproj → ξn⁻¹ ≤ Real.exp Pproj →
    let Aproj := Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{0,uG,uI,uB,uJ} m (s + 1)))
    (∀ i, Real.exp ((Pproj + Aproj) ^ Aproj) ≤ (N i : ℝ)) →
    Real.exp ((Pproj + Aproj) ^ Aproj) ≤ Rrank →
    cells.Nonempty → ∀ (bases : Finset (Fin nX → ℤ)), bases.Nonempty →
    gain ≤ ((wholeLaw).complexMean (fun y => allocatedSlicedTupleValue B U basis hb o hR hσ S
      (Fin nX) poly hmem N (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hW
      hτ hξn stride cells hZ bases x y signal)).re →
    let C := Classical.choose (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)
    let Bbudget := (Pnative + C) ^ C
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun u : integerBox N => u.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun u => signal u.val) (fun u => star (twistData.eval N poly u.val) * Fnative u)‖ := by
  intro ambientQ ambientBudget W τ ξn hW cells poly hp hmem signal hsignal hzero
    lossTarget Pphysical Dphysical Psample Rrank Sstride εsample ηsample
    hstridepos hN hτ hrootbudget hPs hX hframe hSstride hSstrideP hεsample hτP hεsampleP hstrideBoundSample
    A hsize hrank hRrank hηsample hamb hAmbientP hjet hηsampleP V hV hZ
    ρphysical hξn1 hsizePhysical hρ8 hρshift
    hPphysical hMkPhysical hPeriodPhysical hDimPhysical hGPhysical hXPhysical hDPhysical hWL
    hprecision hηprecision hεprecision Amass Aanalytic Fmodel p
    Pnative hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
    hBanalyticNative hphysicalNative hEcoarseNative hpGainNative hξn hstrideGeometry hτGeometry
    hgain hPprojGain hcoarseTarget hEcoarseGain hlossTarget
    Cproj Vproj Acover coverLog Asample Pmass hcoverAmbient hcoverSample hmassSample
    hCactual hVactual hσ1 hsmall hXmass hframeMass hstrideMass hτMass
    AmassWindow hsizeMass hRrankMass hambMass hjetMass
    C₀ δspatial fineMesh hρphysical hC₀ hLC hWC hmeshThreshold hδspatial hρmove hfineMesh
    hboundary hsite hvars hWscale hmeshCoarse hPproj hmProj hGproj hLproj hperiodP
    hKproj hWproj hRproj hσproj hcountProj hIproj hnProj hJproj hProfileProj hCproj hVproj
    hXproj hFrameProj hStrideProj hτProj hξProj Aproj hSizeProj hRankProj hCells bases hbases hdetected
    Cbudget Bbudget Anorm Anative Abudget budget
  subst modulus
  let modulus := residueRefinedPeriod period stride
  let law := containedSupportedProgressionLaw (α := Fin (s + 1)) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S)
    hH₀ hsubset₀ modulus r₀ hcell
  have hsignalAll (u) : ‖signal u‖ ≤ 1 := by
    by_cases hu : u ∈ integerBox N
    · exact hsignal u hu
    · simp only [hzero u hu, norm_zero, zero_le_one]
  with_reducible
    have hcoarse := exists_allocatedCanonicalSlice_uniform_projected_coarse_source_let_s2
      (dim := s + 1) (m := m) (G := G) (I := I) (n := n) (J := J)
      (Pproj := Pproj) (Pk := Pk) (Rrank := Rrank) (target := coarseTarget)
      (κ := gain) (p := Pphysical) (E := Ecoarse)
      (B := B) (U := U) (b := basis) (S := S) (hb := hb) (o := o)
      (hR := hR) (hσ := hσ) (Cproj := Cproj) (Vproj := Vproj)
      (X := Fin nX) («modulus» := period) (q := stride)
      («H» := H₀) («step» := step₀) («c» := c₀) (hH := hH₀) («hsubset» := hsubset₀)
      (label₀ := r₀) (hcell := hcell) (y₀ := y₀) (hy₀ := hy₀)
      (x := x) (hM := hMk) (selection := selection) (hx := hgood) (hcanonical := hperiodCanonical)
      (N := N) (hW := hW) (mesh := fineMesh) (cells := cells)
      (poly := poly) (hp := hp) (hm := hmem) (signal := signal) (hsignal := hsignalAll)
      (hN := hN) (hq := hstridepos) (hτ := hτ) (hρ := hρphysical)
      (hbudget := hrootbudget) (hC₀ := hC₀) (hLC := hLC) (hWC := hWC)
      (hξ := hξn) (hξ1 := hξn1) (hsize := hsizePhysical) (hmesh := hmeshThreshold)
      (hρ8 := hρ8) (hδ := hδspatial) (hρshift := hρshift) (hρmove := hρmove)
      (hmeshpos := hfineMesh) (hmass := hZ) (μ := μrows) (ν := ν) (μcoeff := μ)
      hGproj hLproj hMkPk hperiodP hCactual hVactual hσ1 C hC hchart hsmall
  have hcoarse := hcoarse hXmass hframeMass hstrideMass hτMass hsizeMass hrank hRrankMass hambMass hjetMass
  have hcoarse := hcoarse hboundary hsite hPphysical hEcoarseNative.1 hGPhysical hXPhysical hDimPhysical hMkPhysical
    hvars hWscale hmeshCoarse
  have hcoarse := hcoarse hPproj hmProj hKproj hWproj hRproj hσproj hcountProj
    hIproj hnProj hJproj hProfileProj hCproj hVproj hXproj hFrameProj hStrideProj hτProj hξProj
    hCells bases hbases hSizeProj hRankProj hdetected
  obtain ⟨d, hdiv, hdpos, hdBound, g, hgc, hgb, hgi, _hgMass, hglaw, hactualFamily,
    base, _hbase, hZmass, hpositive⟩ := hcoarse
  have : NeZero d := ⟨hdpos.ne'⟩
  obtain ⟨actual, hLa, hCa, hactualComplex⟩ := hactualFamily law
  have hactual (z) : (law.mean (fun y => g y z) : ℂ) =
      actual (coveredJetAmbientTorus U 1 z) := by
    simpa only [FiniteProbabilityWeights.complexMean_ofReal] using hactualComplex z
  have hcanonicalRefined : modulus = canonicalSlicedModulus (M := Mk) selection stride m x := by
    dsimp only [modulus]
    rw [canonicalSlicedModulus_good_s2 selection stride m x hgood, hperiodCanonical]
  have hdbase : (d : ℝ) ≤ Real.exp baseAmbient :=
    hdBound.trans (Real.exp_le_exp.mpr hcoverAmbient)
  have hdP : (d : ℝ) ≤ Real.exp Psample :=
    hdBound.trans (Real.exp_le_exp.mpr hcoverSample)
  have hactualP : Real.exp Pmass ≤ Real.exp Psample := Real.exp_le_exp.mpr hmassSample
  have hmesh : 0 < allocatedEarlyRecenteredMesh (Fin nX) selection Mk period Pphysical Ecoarse :=
    hfineMesh.trans_le hmeshCoarse
  have hconstructor := exists_allocatedCanonicalSlice_constructed_native_source_s2
      (s := s) (nX := nX) (gain := gain) (Pproj := Pproj)
      (coarseTarget := coarseTarget) (Ecoarse := Ecoarse) (pGain := pGain)
      (Z := selectedJointDensityMass bases stride cells V
        (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem))
      B U basis hR hσ S x hMk selection hgood stride hP hMkP hRP hRi hσi hcount
      Q hb o bW d H₀ step₀ c₀ hH₀ hsubset₀ modulus hcanonicalRefined r₀ hcell ν μ μrows
      hdimensions hPk hMkPk hPrho htarget hF hQstride hstride hstrideBound hlength
      g (fun y => (hgc y).measurable) (fun y z => (hgb y z).1) hgi hglaw
      ρ t htone hs hρ hρ1 hσsmall hstep hδ hδF hdense hq
      y₀ hy₀ T hT hsource C hC hchart hbudget hρlog hη0 hηsmall
      period hperiodCanonical hdiv siteRadius hrone hsitebudget Cforward hforward K hK hradius
      hPbox hVlog hNlog hMlog hbox hvolume hnormalizer hmask hbaseAmbient hvbase hnbase hmbase
      hsites haxes hlabels hKbase hcoords hcutoff hdbase hpbase hrowsAmbient houtputs hheight
      Qgrid hQgrid hδg hdenseg Tg hQTg hstepAll Ag hAg Pg hPg hcP hsP hstrideGrid hBa hBi
      hDg hvg hwg htg hpg hcube hdegree hrowsD htail hblocks hRv hRiGrid hδw hTg hcoeff
      hPp₀ haxesGrid hfullAxes hfullOutputs hambientCount hprofileBudget
      hBanalytic hDanalytic hcutoffAnalytic hcoordAnalytic hgridAnalytic
      hPnum hI hn hcoeffEarly hRiEarly hVEarly
  have hconstructor := hconstructor period stride N rfl rfl hW base cells poly hp hmem signal hsignal hzero
      (lossTarget := lossTarget) (Pphysical := Pphysical) (Dphysical := Dphysical)
      (Psample := Psample) (Rrank := Rrank) (Sstride := Sstride) (εsample := εsample) (ηsample := ηsample)
      hstridepos hN hτ hmesh hrootbudget hpositive
  have hconstructor := hconstructor hPs hX hframe hdP hSstride hSstrideP hεsample hτP hεsampleP hstrideBoundSample
      hsize hrank hRrank actual ⟨Real.exp Pmass, Real.exp_nonneg _⟩ ⟨Real.exp Pmass, Real.exp_nonneg _⟩
      hLa hCa hηsample hamb hactualP hactualP hAmbientP hjet hηsampleP hactual
  exact hconstructor hV hZ hξn1 hsizePhysical hρ8 hρshift hPphysical hMkPhysical hPeriodPhysical hDimPhysical
      hGPhysical hXPhysical hDPhysical hWL hprecision hηprecision hεprecision
      hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
      hBanalyticNative hphysicalNative hEcoarseNative hpGainNative hξn rfl hstrideGeometry hτGeometry
      hgain hZmass.1 hPprojGain hcoarseTarget hEcoarseGain hlossTarget

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uG, uI, uB, uJ, uQ} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_projected_native_source_s2_oai.{uG, uI, uB, uJ, uQ} := @OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_projected_native_source_s2_oai.{uG, uI, uB, uJ, uQ}
