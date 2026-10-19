-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_sampled_l1_of_length_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:19:22.219524+00:00
-- url     : https://prove2.me/submissions/3861d1ab-0f36-44da-a6c8-67ecabd9d7ec

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B235
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineIdeal_l1_of_length_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedRowSlicedIdeal_measurable_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedWholeMaskedCoveredProfile_measurable_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedProductPrefactorCap
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem allocatedWholeMaskedCoveredProfile_mean_measurable
    {A : Type*} [Fintype A] (p : FiniteProbabilityWeights A)
    (w : A → PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O a.val.1) → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (fun y => (p.mean (fun a =>
      allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (w a) q f y) : ℂ)) :=
  (p.mean_measurable _ (fun a =>
    allocatedWholeMaskedCoveredProfile_measurable_s2 B U b hR hσ S x rows hb o bW d (w a) q f hf)).complex_ofReal

end Erdos3.VectorPolynomial

end

end OAI
end

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
local notation "ξ" => Measure.pi (fun j => Measure.pi (fun _ : rowSets j => ν j))
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
theorem allocatedAffineIdeal_sampled_l1_of_length_s2_oai
    {D target Pk Prho F Tmod : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin dim) selectedRows D)
    (hPk : 0 ≤ Pk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target) (hF : 0 ≤ F) (hTmod : 0 ≤ Tmod)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F Tmod) ≤ S.value)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U basis S) →
  EuclideanJetLayers U selectedRows → ℝ)
    (hgm : ∀ y, Measurable (g y)) (hg0 : ∀ y z, 0 ≤ g y z)
    (hgi : ∀ y, Integrable (g y) ξ)
    (hglaw : ∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
  (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) = realDensityMeasure ξ (g y))
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
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{uX,uJ,0} m dim)
    ∀ {Psample Rrank Sstride τ εsample ηsample δsur : ℝ},
    0 ≤ Psample → (Fintype.card X : ℝ) ≤ Psample →
    (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Psample →
    ∀ (base : X → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j),
    (d : ℝ) ≤ Real.exp Psample →
    ∀ (stride : X → ℕ), (∀ i, 0 < stride i) →
    0 ≤ Sstride → Sstride ≤ Real.exp Psample → 0 < τ → 0 < εsample →
    1 / τ ≤ Real.exp Psample → 1 / εsample ≤ Real.exp Psample →
    (∀ i, (stride i : ℝ) ≤ Sstride) →
    ∀ (N : X → ℝ), (∀ i, Real.exp ((Psample + A) ^ A) ≤ N i) →
    (∀ j, HasLayerSamplingRank (j.val + 1) N Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    ∀ (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)), cells.Nonempty →
    ∀ (V : Option (Fin dim) × X → ℝ), (∀ z, 0 < V z) → (∀ z, τ * N z.2 ≤ V z) →
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
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z,
      selectedResidueDensityMass stride cells V (fun z =>
        let point := physicalCubeRowSample U d rows poly hmem
          (translatePhysicalCube base (standardPhysicalCubeOutput z))
        ‖((wholeLaw).mean (fun v => g v point) : ℂ) - profile point‖) ≤
          Real.exp (-target) + 2 * δsur + (2 * ηsample + εsample) := by
  intro center width ideal profile A Psample Rrank Sstride τ εsample ηsample δsur
    hPs hX hframe base poly hp hmem hdP stride hstridepos hSstride hSstrideP hτ hεsample hτP hεsampleP
    hstride N hsize hrank hRrank cells hcells V hV hwidth actual surrogate La Ls Ca Cs
    hLa hLs hCa hCs hηsample hamb hLaP hLsP hCaP hCsP hjet hηsampleP hactual happrox
  have hhaar := allocatedAffineIdeal_l1_of_length_s2 B U basis hR hσ S rowSets x s hA hMk hi
    hP hMkP hRP hRi hσi hcount Q hb o bW d H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell ν μ
    hdimensions hPk hMkPk hPrho htarget hF hTmod hlength
    g hgm hg0 hgi hglaw ρ t htone hs hρ hρ1 hσsmall hstep hδ hδF hdense hm hmodulus
    selection hgood hq hrowDegree hperiod v₀ hv₀ T hT hsource C hC hchart hbudget hρlog hη0 hηsmall
  have hmass : (∫ y, ‖actual (coveredJetAmbientTorus U 1 y) - profile y‖ ∂ξ) ≤ Real.exp (-target) := by
    simpa only [hactual] using hhaar
  have hmeas : Measurable profile :=
    allocatedWholeMaskedCoveredProfile_mean_measurable B U basis hR hσ S x rows hb o bW d
      (gridLaw) (fun u => principalAxisJoin grid u v₀) modulus ideal
      (allocatedRowSlicedIdeal_measurable_s2 B U basis S rowSets hR (ρ grid) hρ center width)
  have hsample := (Classical.choose_spec (exists_translated_physical_jet_l1_perturbation.{uX,uJ,0} m dim)).2
    (I := X) (J := J) (O := selectedRows)
  obtain ⟨hZ, he⟩ := hsample rows (fun _ => Subtype.val_injective) hrowDegree hPs hX hframe U μrows ν
    base poly hp hmem d (NeZero.pos d) hdP stride hstridepos hSstride hSstrideP hτ hεsample
    hτP hεsampleP hstride N hsize hrank hRrank cells hcells V hV hwidth actual surrogate La Ls Ca Cs
    hLa hLs hCa hCs hηsample hamb hLaP hLsP hCaP hCsP hjet hηsampleP profile hmeas happrox hmass
  refine ⟨hZ, ?_⟩
  simpa only [hactual] using he

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uJ, uQ, uX, u_1, u_2, u_3} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_sampled_l1_of_length_s2_oai.{uJ, uQ, uX, u_1, u_2, u_3} := @OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_sampled_l1_of_length_s2_oai.{uJ, uQ, uX, u_1, u_2, u_3}
