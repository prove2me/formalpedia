-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedCanonicalSlice_constructed_model_source_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:01:43.373857+00:00
-- url     : https://prove2.me/submissions/cd8bc286-62ee-4101-9ebc-d8a6c3620832

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B235
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCanonicalSlice_model_source_of_length_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedNarrow_reference_comparison_geometry_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedCanonicalSlice_bounded_ambient_s2
import Theorems.Thm_OAI_Erdos3_containedSupportedProgressionLaw_residue_eq_s2
import Theorems.Thm_OAI_Erdos3_goodKernelUniformCandidate_spec_s2
import Theorems.Thm_OAI_Erdos3_physicalL1Source_error_le_exp_of_precision_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OneCubePrincipalSliceRiemann
namespace OAI

section

namespace Erdos3
open scoped Classical

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)

omit [DecidableEq α] in
theorem principalProgressionSlice_parameters [DecidableEq α]
    (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ)) :
    ∀ i, 0 < principalProgressionSliceWidth (α := α) B h L H step i ∧
      δ / 2 ≤ |principalProgressionSliceWidth (α := α) B h L H step i| ∧
      |principalProgressionSliceCenter (α := α) B h L c i| +
        |principalProgressionSliceWidth (α := α) B h L H step i| ≤ 1 := by
  intro i
  let j : PrincipalTupleIndex B h := ⟨i.1, i.2.1, i.2.2.1⟩
  have hg := progression_slice_endpoint_geometry (c j) (hL j) (hstep j) (hH j) hδ
    (hsubset j) (hdense j)
  have hp : 0 < (step j : ℝ) * ((H j : ℝ) - 1) / L j := (half_pos hδ).trans_le hg.2.1
  refine ⟨hp, ?_, ?_⟩
  · change δ / 2 ≤ |(step j : ℝ) * ((H j : ℝ) - 1) / L j|
    rw [abs_of_pos hp]
    exact hg.2.1
  · change |if i.2.2.2 = none then (c j : ℝ) / L j else 0| +
      |(step j : ℝ) * ((H j : ℝ) - 1) / L j| ≤ 1
    split_ifs
    · exact hg.2.2.1
    · simpa only [abs_zero, zero_add] using
        (le_add_of_nonneg_left (abs_nonneg ((c j : ℝ) / L j))).trans hg.2.2.1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedDetectedCanonicalPeriod
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

theorem canonicalSlicedModulus_pos (hs : ∀ i, 0 < stride i)
    (x : G → IntegerScalarCubeBox α L) :
    0 < canonicalSlicedModulus (M := M) selection stride height x := by
  unfold canonicalSlicedModulus
  split_ifs with hx
  · exact residueRefinedPeriod_pos (kernelPeriodCandidate_pos _ _) stride hs
  · norm_num

theorem canonicalSlicedModulus_le_exp {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hM : (M : ℝ) ≤ Real.exp P) (hs : ∀ i, (stride i : ℝ) ≤ Real.exp Q)
    (x : G → IntegerScalarCubeBox α L) :
    (canonicalSlicedModulus (M := M) selection stride height x : ℝ) ≤
      Real.exp ((height + 1 : ℕ) * P + Fintype.card X * Q) := by
  unfold canonicalSlicedModulus
  split_ifs with hx
  · exact residueRefinedPeriod_exp_bound _ stride
      (kernelPeriodCandidate_le_exp hM (height + 1) _) hs
  · exact_mod_cast Real.one_le_exp (add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) hP) (mul_nonneg (Nat.cast_nonneg _) hQ))

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
theorem allocatedCanonicalSlice_constructed_model_source_s2_oai
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
  obtain ⟨surrogate, hLs, hCs, happrox⟩ := exists_allocatedCanonicalSlice_bounded_ambient_s2
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
    exact containedSupportedProgressionLaw_residue_eq_s2 B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S)
      hH₀ hsubset₀ modulus r₀ hcell y y₀ hy hy₀.ne'
  have hwhole : principalResidueLabel refined (wholeReference r) = r := rfl
  have hspatialPeriod : integerScalarLattice (Unit ⊕ Fin dim) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection) := by
    rw [hspatialCanonical, hperiodCanonical]
    exact (goodKernelUniformCandidate_spec_s2.{0,_,0} selection x hgood m).1 _
  obtain ⟨hrows, hscale, hH1⟩ := allocatedNarrow_reference_comparison_geometry_s2 B U basis S
    (fun _ => 0) x (wholeReference r) N stride hN hstridepos hW hτ hξn1 hsizePhysical hρ8 hρshift
  have hcost := physicalL1Source_error_le_exp_of_precision_s2 dim X selection hPphysical hMk hMkPhysical
    hPeriodPhysical hDimPhysical hGPhysical hXPhysical
    (by exact_mod_cast Nat.succ_le_of_lt S.positive : (1 : ℝ) ≤ S.value) hW hDPhysical hWL
    hprecision hηprecision hεprecision htprecision
  exact allocatedCanonicalSlice_model_source_of_length_s2
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

theorem solution.{uJ, uQ, uX, u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedCanonicalSlice_constructed_model_source_s2_oai.{uJ, uQ, uX, u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.allocatedCanonicalSlice_constructed_model_source_s2_oai.{uJ, uQ, uX, u_1, u_2, u_3, u_4}
