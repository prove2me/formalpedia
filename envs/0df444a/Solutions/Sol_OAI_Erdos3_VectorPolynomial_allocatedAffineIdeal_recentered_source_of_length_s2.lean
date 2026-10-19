-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_recentered_source_of_length_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:19:21.477026+00:00
-- url     : https://prove2.me/submissions/ff4f7639-b6f5-49b0-9d23-8af025847091

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B235
import Theorems.Thm_OAI_Erdos3_BooleanCubeKernel_referenceJetEnvelopeWidths_trimmed_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineIdeal_sampled_l1_of_length_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedRecenteredSelectedMean_l1_source_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineRecenteredSource
namespace OAI

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
variable (s : ∀ j : Fin m, ↥(rowSets j) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (Subtype.val : rowSets j → Finset (Fin dim))).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := ↥(rowSets j))
  S.positive x (j.val + 1) (Subtype.val : rowSets j → Finset (Fin dim)) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
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
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := (Fin dim)) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
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

include μrows hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
omit [∀ j, Nonempty (rowSets j)] in
theorem allocatedAffineIdeal_recentered_source_of_length_s2_oai
    {D target Pk Prho F Tmod : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin dim) selectedRows D)
    (hPk : 0 ≤ Pk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target) (hF : 0 ≤ F) (hTmod : 0 ≤ Tmod)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F Tmod) ≤ S.value)
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
    (hm : 0 < modulus)
    (hmodulus : (modulus : ℝ) ≤ Real.exp Tmod)
    (selection : (Fin dim) ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hq : Fintype.card (Fin dim) ≤ m + 1)
    (hrowDegree : ∀ j (a : rowSets j), a.val.card ≤ j.val + 1)
    (hperiod : ∀ j : Fin m, integerScalarLattice (selectedRows j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := (Fin dim)) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue (allocatedAffineLength_slice_ready B U basis hdimensions hP hPrho hPk htarget hF hTmod S hlength H₀ step₀ c₀ hsubset₀ hδ hδF modulus hm hmodulus hstep hdense).2.1).weight v₀ ≠ 0)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius (Fin dim) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin dim) * ((Fintype.card (Fin dim) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4))) :
    let center := principalProgressionSliceCenter (α := (Fin dim)) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := (Fin dim)) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, selectedRows a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option (Fin dim))
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let profile := fun y => ((gridLaw).mean (fun u =>
      allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows
        hb o bW d (principalAxisJoin grid u v₀) modulus ideal y) : ℂ)
    ∀ (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : X → ℕ),
    let refined := residueRefinedPeriod spatialModulus stride
    let labels := PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined
    ∀ (wholeReference : labels → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
        (allocatedPrincipalSides B U basis S)) (r : labels),
    (∀ y, (wholeLaw).weight y ≠ 0 → principalResidueLabel refined y = r) →
    principalResidueLabel refined (wholeReference r) = r →
    ∀ {W τ ξn mesh : ℝ} (hW : 0 ≤ W) (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ),
    let point := physicalCubeRowSample U d rows poly hmem
    ∀ (model : EuclideanJetLayers U selectedRows → ℂ)
      {κ loss εtrunc Psample Rrank Sstride εsample ηsample δsur : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → 0 < τ → 0 < mesh →
    allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W →
    integerScalarLattice (Unit ⊕ Fin dim) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection) →
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
    ∀ (actual surrogate : (JetAmbientIndex selectedRows J → UnitAddCircle) → ℂ)
      (La Ls Ca Cs : ℝ≥0),
    LipschitzWith La actual → LipschitzWith Ls surrogate →
    (∀ z, ‖actual z‖ ≤ Ca) → (∀ z, ‖surrogate z‖ ≤ Cs) →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ Psample →
    (La : ℝ) ≤ Real.exp Psample → (Ls : ℝ) ≤ Real.exp Psample →
    (Ca : ℝ) ≤ Real.exp Psample → (Cs : ℝ) ≤ Real.exp Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    (∀ y, ((wholeLaw).mean (fun v => g v y) : ℂ) = actual (coveredJetAmbientTorus U 1 y)) →
    (∀ y, ‖profile y - surrogate (coveredJetAmbientTorus U 1 y)‖ ≤ δsur) →
    let root := allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (wholeReference r)
    let dirs := allocatedPhysicalCubeDirections B U basis S x (wholeReference r)
    let Hsp := trimmedSpatialRootScale τ N stride
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    let Csp := ((spatialModulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (Mk : ℝ))) ^ Fintype.card X
    let volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    (∀ z, 0 < V z) → (0 < ∑' z, selectedResidueSmoothWeight stride cells V z) →
    (∀ t i, (∑ k, |(physicalCubeCoefficient root dirs i k : ℝ)|) ≤ Hsp t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * Hsp t) →
    (∀ t, 1 ≤ Hsp t) →
    Csp * (volumeFactor * (Real.exp (-target) + 2 * δsur + (2 * ηsample + εsample)) +
      ((9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
        (((1 + W) / S.value) ^ dim) ^ Fintype.card X) * εtrunc) ≤ loss →
    κ - loss ≤
      (∑ t : cells × spatialWindow (α := Fin dim) Hsp 4, (selectedResidueCellWeight stride cells V t.1 : ℂ) *
        allocatedRecenteredResidueWeight (τ := τ) B U basis S X spatialModulus stride wholeReference x hMk selection hgood
          N hW mesh base cells test r t.1 t.2.val *
        model (point (allocatedWholeResidueReconstruction B U basis S X spatialModulus stride wholeReference x base r
          t.1.val t.2.val))).re := by
  intro center width ideal profile spatialModulus _ stride N refined labels wholeReference r hlabel hwhole
    W τ ξn mesh hW base cells poly hp hmem test point model κ loss εtrunc Psample Rrank Sstride εsample ηsample δsur
    hstridepos hN hτ hmesh hrootbudget hspatialPeriod htest hpositive hεtrunc htrunc
    hPs hX hframe hdP hSstride hSstrideP hεsample hτP hεsampleP hstride A hsize hrank hRrank
    actual surrogate La Ls Ca Cs hLa hLs hCa hCs hηsample hamb hLaP hLsP hCaP hCsP hjet hηsampleP hactual happrox
    root dirs Hsp V Csp volumeFactor hV hZ hrows hscale hH1 hcost
  apply allocatedRecenteredSelectedMean_l1_source_s2 B U basis S X spatialModulus stride wholeReference
    x hMk selection hgood N hW mesh base cells point test (wholeLaw) r hlabel hwhole
    (fun y z => (g y z : ℂ)) profile model hstridepos hN hτ hrootbudget hmesh hspatialPeriod htest
    hpositive hεtrunc htrunc hV hZ hrows hscale hH1 ?_ hcost
  intro a
  let targetCell := columnResiduePattern stride (standardPhysicalCubeFrame
    (physicalCubeRootDifferences root dirs 0 (boundedColumnResidueRepresentative stride a.val)))
  let V₁ := referenceJetEnvelopeWidths (q := dim) stride Hsp
  have hwidth (z : Option (Fin dim) × X) : τ * (N z.2 : ℝ) ≤ V₁ z := by
    change τ * (N z.2 : ℝ) ≤ referenceJetEnvelopeWidths stride (trimmedSpatialRootScale τ N stride) z
    rw [referenceJetEnvelopeWidths_trimmed_s2 stride N hstridepos τ z]
    nlinarith [mul_pos hτ (Nat.cast_pos.mpr (hN z.2))]
  have hV₁ (z : Option (Fin dim) × X) : 0 < V₁ z :=
    (mul_pos hτ (Nat.cast_pos.mpr (hN z.2))).trans_le (hwidth z)
  obtain ⟨hZa, he⟩ := allocatedAffineIdeal_sampled_l1_of_length_s2 B U basis hR hσ S rowSets x s hA hMk hi
    hP hMkP hRP hRi hσi hcount Q hb o bW d H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell ν μ μrows
    hdimensions hPk hMkPk hPrho htarget hF hTmod hlength
    g hgm hg0 hgi hglaw ρ t htone hs hρ hρ1 hσsmall hstep hδ hδF hdense hm hmodulus
    selection hgood hq hrowDegree hperiod v₀ hv₀ T hT hsource C hC hchart hbudget hρlog hη0 hηsmall
    hPs hX hframe base poly hp hmem hdP stride hstridepos hSstride hSstrideP hτ hεsample hτP hεsampleP
    hstride (fun i => (N i : ℝ)) hsize hrank hRrank {targetCell} (Finset.singleton_nonempty _)
    V₁ hV₁ hwidth actual surrogate La Ls Ca Cs hLa hLs hCa hCs hηsample hamb hLaP hLsP hCaP hCsP hjet hηsampleP
    hactual happrox
  exact ⟨hZa, by simpa only [FiniteProbabilityWeights.complexMean_ofReal] using he⟩

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uJ, uQ, uX, u_1, u_2, u_3} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_recentered_source_of_length_s2_oai.{uJ, uQ, uX, u_1, u_2, u_3} := @OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_recentered_source_of_length_s2_oai.{uJ, uQ, uX, u_1, u_2, u_3}
