-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_constructed_finite_source_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:21:43.513997+00:00
-- url     : https://prove2.me/submissions/97af5c9c-1f57-4ad0-bace-cfb816d5e41f

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B235
import Definitions.Def_OAIE3v2B236
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCanonicalSlice_constructed_model_source_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedCanonicalSlice_accurate_source_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalSliceConstructedFiniteSource
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
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
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
local notation "jetHaar" => Measure.pi (fun j =>
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype dim (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin dim) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

include hcanonical μrows hR hσ hMk hgood hP hMkP hRP hRi hσi hcount in

theorem exists_allocatedCanonicalSlice_constructed_finite_source_s2_oai
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
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp baseAmbient)
    (Qgrid : ℝ≥0) (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U basis S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U basis S a).1 (allocatedGridIntegerAxis B U basis S a).2) : ℝ) + 1) ≤ Qgrid)
    {δg : ℝ} (hδg : 0 < δg)
    (hdenseg : ∀ tg, δg * allocatedPrincipalSides B U basis S tg ≤ (H₀ tg : ℝ))
    (Tg : ℕ) (hQTg : (((Fintype.card (Fin dim) + 1) * modulus : ℕ) : ℝ) / δg ≤ Tg)
    (hstepAll : ∀ tg, 0 < step₀ tg)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition) (Pg : ℝ) (hPg : 1 ≤ Pg)
    (hcP : scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) Ag 1 0 modulus ≤ Pg)
    (hstrideGrid : ∀ tg, ((step₀ tg * modulus : ℕ) : ℝ) ≤ Pg)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg tg pg : ℝ}
    (hDg : 0 ≤ Dg) (hvg : 0 ≤ vg) (hwg : 0 ≤ wg) (htg : 0 ≤ tg) (hpg : 0 ≤ pg)
    (hcube : (Fintype.card (Fin dim) : ℝ) ≤ Dg) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin dim) (j.val + 1)).card : ℝ) ≤ Dg)
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
    :
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin dim))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    let _center := principalProgressionSliceCenter (α := (Fin dim)) activeB activeDegree L c
    let _width := principalProgressionSliceWidth (α := (Fin dim)) activeB activeDegree L H step
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
    ∀ {κ lossTarget Pphysical Dphysical Psample Rrank Sstride εsample ηsample : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → 0 < τ → 0 < mesh →
    allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W →
    (∀ v, ‖test v‖ ≤ 1) →
    κ ≤ ((wholeLaw).complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξn)
      B U basis S X spatialModulus stride wholeReference x hMk selection hgood N hW mesh base cells point test
      (fun y z => (g y z : ℂ)))).re →
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
    let Hsp := trimmedSpatialRootScale τ N stride
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
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
    ηsample ≤ Real.exp (-target) → εsample ≤ Real.exp (-target) →
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m dim)
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m dim)
    let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin dim)) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * ((m + 1 : ℕ) * Pk))
    let Dout := (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ)
    let Eg := Dout * Prho + (target + Fmodel) + 1
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    let LgridLog := fun j : Fin m => fun e : ℝ => slicedGridSiteLog j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) Dg p e
    let Cp := ∑ j, (LgridLog j 0 + Dg * (vg + 1))
    let Eg' := uniformProductAccuracyLog Dg Cp Eg + Dg * (vg + 1) + 1
    let Op := ∑ j, (siteExponentialOutputLog (Fintype.card (Finset (Fin dim))) (LgridLog j Eg') + (Dg + 1) * (vg + 1))
    let Vgrid : ℝ≥0 := ⟨Real.exp Op, Real.exp_nonneg Op⟩
    ∃ e : {a // grid a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)),
      (∀ a, (e a).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op)
        ⟨Real.exp Op, Real.exp_nonneg _⟩ (Real.exp (slicedGridGeometryLog Dg vg wg tg + (Dg + vg + 8)))) ∧
    ∃ k : ℕ, ∃ (a : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → ℂ)
      (f : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)),
          ∑ i, ∑ kg, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
            allocatedProductMaskedIdealCoefficient B U basis S rowSets x y₀ modulus d period a label i) *
            coverSiteCoefficient e kg‖) ≤
          Real.exp ((Dg + p + vg + Fmodel + Prho + Pk + target + Amass) ^ Amass) ∧
        (∃ Lanalytic : ℝ≥0,
          ((Lanalytic * ((period : ℝ≥0) * Vgrid ^ Fintype.card {a // grid a}) : ℝ≥0) : ℝ) ≤
            Real.exp ((Dg + p + vg + Fmodel + Prho + Pk + target + Banalytic + Aanalytic) ^ Aanalytic) ∧
          (period : ℝ) * (Real.exp Op) ^ Fintype.card {a // grid a} ≤
            Real.exp ((Dg + p + vg + Fmodel + Prho + Pk + target + Banalytic + Aanalytic) ^ Aanalytic) ∧
          ∃ analyticFactor : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period))) →
              (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → (∀ a, (e a).Term) → Finset (Fin dim) →
              (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
                ((Σ j, J j) → UnitAddCircle)) → ℂ,
            (∀ label i kg t, LipschitzWith Lanalytic (analyticFactor label i kg t)) ∧
            (∀ label i kg t z, ‖analyticFactor label i kg t z‖ ≤ 1) ∧
            AllocatedModelPhysicalExpansionIdentity B U basis S x y₀ modulus d period siteRadius (zero_lt_one.trans_le hrone) hb o bW e a f poly hmem analyticFactor) ∧
    κ - Real.exp (-lossTarget) ≤
      (∑ t : cells × spatialWindow (α := Fin dim) Hsp 4, (selectedResidueCellWeight stride cells V t.1 : ℂ) *
        allocatedRecenteredResidueWeight (τ := τ) B U basis S X spatialModulus stride wholeReference x hMk selection hgood
          N hW mesh base cells test r t.1 t.2.val *
        (allocatedProductChartIdealApproximation B U basis S rowSets x y₀ modulus d period siteRadius
            (zero_lt_one.trans_le hrone) hb o bW a f (point (allocatedWholeResidueReconstruction B U basis S X spatialModulus stride wholeReference x base r
          t.1.val t.2.val)) *
          allocatedFullGridChartModel B U basis S rowSets d hb o bW e
            (point (allocatedWholeResidueReconstruction B U basis S X spatialModulus stride wholeReference x base r
              t.1.val t.2.val)))).re := by
  let : ∀ j : Fin m, Nonempty (rowSets j) := fun j =>
    ⟨⟨∅, (mem_boundedBooleanJetRows (j.val + 1) ∅).mpr (by simp)⟩⟩
  intro ambientQ ambientBudget center width
  have hrowDegree (j : Fin m) (a : rowSets j) : a.val.card ≤ j.val + 1 :=
    (mem_boundedBooleanJetRows (j.val + 1) a.val).mp a.property
  have hm : 0 < modulus := by
    rw [hcanonical]
    exact canonicalSlicedModulus_pos selection stride₀ m hstride₀ x
  have hmodulus : (modulus : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card X₀ * Qstride) := by
    rw [hcanonical]
    exact canonicalSlicedModulus_le_exp selection stride₀ m hPk hQstride hMkPk hstrideBound x
  have hTmod : 0 ≤ ((m + 1 : ℕ) : ℝ) * Pk + Fintype.card X₀ * Qstride := by positivity
  have hready := allocatedAffineLength_slice_ready (α := Fin dim) (O := selectedRows) B U basis hdimensions hP hPrho hPk htarget hF hTmod
    S hlength H₀ step₀ c₀ hsubset₀ hδ hδF modulus hm hmodulus hstep hdense
  have hw (i) : |center i| + |width i| ≤ 1 :=
    (principalProgressionSlice_parameters activeB activeDegree L H step c positiveLengths
      hstep hready.1 hδ hsubset hdense i).2.2
  have hT0 (j) : 0 ≤ T j :=
    (add_nonneg (partitionedIdealRadius_nonneg (Fin dim) m) zero_le_one).trans (hT j)
  have hσ1 (j) : σ j ≤ 1 := (hσsmall j).trans htone
  have hconstruction :=
    exists_allocatedCanonicalSlice_accurate_source_s2 (dim := dim) (E := Q) B U basis S modulus d period siteRadius
      (zero_lt_one.trans_le hrone) hb o bW hR C hC hchart hsitebudget (ρ grid) center width hσ
      H₀ step₀ c₀ hH₀ hsubset₀ r₀ hcell
      Cforward hforward K hK Qgrid hQgrid (by simpa only [Fintype.card_fin] using hq)
      hδg hdenseg Tg hQTg hstepAll Ag hAg Pg hPg hcP hsP hstrideGrid hBa hBi
      hDg hvg hwg htg hpg hcube hdegree hrowsD htail hblocks hRv hRiGrid hδw hTg hcoeff hPp₀ haxesGrid
  have hconstruction := hconstruction
      hfullAxes (by simpa only [← Nat.card_eq_fintype_card] using hfullOutputs)
  have hconstruction := hconstruction
      hambientCount hprofileBudget hBanalytic hDanalytic hcutoffAnalytic hcoordAnalytic
      hgridAnalytic hrone hσ1 T hT0 hT hsource hradius hσ1 hρ hρ1 hw hPrho hρlog
      hPnum hPk htarget hMk hMkPk hI hn hcoeffEarly hRiEarly hVEarly
  have hconstruction := hconstruction
      x selection hgood stride₀ hstride₀ hcanonical hperiodCanonical hdiv y₀ hy₀
  obtain ⟨e, he, k, hk, hcard, a, f, ha, hf, hLf, hsupp, hcoeffMass, hmassExplicit,
      hmass, hbound, hmeas, hmodelMeas, htrunc, happrox, hphysical⟩ := hconstruction
  intro spatialModulus _ stride N hspatialCanonical refined hmodulusRefined labels wholeReference r
    W τ ξn mesh hW base cells poly hp hmem test point κ lossTarget Pphysical Dphysical Psample Rrank Sstride εsample ηsample
    hstridepos hN hτ hmesh hrootbudget htest hpositive
    hPs hX hframe hdP hSstride hSstrideP hεsample hτP hεsampleP hstride A hsize hrank hRrank
    actual La Ca hLa hCa hηsample hamb hLaP hCaP hAmbientP hjet hηsampleP hactual
    Hsp V hV hZ ρphysical hξn1 hsizePhysical hρ8 hρshift
    hPphysical hMkPhysical hPeriodPhysical hDimPhysical hGPhysical hXPhysical hDPhysical hWL
    hprecision hηprecision hεprecision
    Amass Aanalytic Fmodel Dout Eg p LgridLog Cp Eg' Op Vgrid
  refine ⟨e, ?_, k, a, f, ?_, ?_, ?_⟩
  · simpa only [Op, Eg', Cp, LgridLog, p, Eg, Dout, Fmodel,
      ← Nat.card_eq_fintype_card] using he
  · simpa only [Amass, p, Fmodel, ← Nat.card_eq_fintype_card] using hmass
  · obtain ⟨hLip, hcover, analyticFactor, hLfactor, hfactor, hidentity⟩ := hphysical poly hp hmem
    refine ⟨_, ?_, ?_, analyticFactor, hLfactor, hfactor, hidentity⟩
    · simpa only [Op, Eg', Cp, LgridLog, p, Eg, Dout, Fmodel, Aanalytic,
        Vgrid, ← Nat.card_eq_fintype_card] using hLip
    · simpa only [Op, Eg', Cp, LgridLog, p, Eg, Dout, Fmodel, Aanalytic,
        ← Nat.card_eq_fintype_card] using hcover
  · exact allocatedCanonicalSlice_constructed_model_source_s2
      B U basis hR hσ S rowSets x hMk selection hgood stride₀ hP hMkP hRP hRi hσi hcount
      Q hb o bW d H₀ step₀ c₀ hH₀ hsubset₀ modulus hcanonical r₀ hcell ν μ μrows
      hdimensions hPk hMkPk hPrho htarget hF hQstride hstride₀ hstrideBound hlength
      g hgm hg0 hgi hglaw ρ t htone hs hρ hρ1 hσsmall hstep hδ hδF hdense hq hrowDegree
      y₀ hy₀ T hT hsource C hC hchart hbudget hρlog hη0 hηsmall
      period hperiodCanonical hdiv siteRadius hrone hsitebudget Cforward hforward K hK hradius
      hPbox hVlog hNlog hMlog hbox hvolume hnormalizer hmask hbaseAmbient hvbase hnbase hmbase
      hsites haxes hlabels hKbase hcoords hcutoff hdbase hpbase hrowsAmbient houtputs hheight
      spatialModulus stride N hspatialCanonical hmodulusRefined hW base cells poly hp hmem test
      (fun z => allocatedProductChartIdealApproximation B U basis S rowSets x y₀ modulus d period
        siteRadius (zero_lt_one.trans_le hrone) hb o bW a f z *
          allocatedFullGridChartModel B U basis S rowSets d hb o bW e z)
      hstridepos hN hτ hmesh hrootbudget htest hpositive (Real.exp_nonneg _) happrox
      hPs hX hframe hdP hSstride hSstrideP hεsample hτP hεsampleP hstride hsize hrank hRrank
      actual La Ca hLa hCa hηsample hamb hLaP hCaP hAmbientP hjet hηsampleP hactual
      hV hZ hξn1 hsizePhysical hρ8 hρshift hPphysical hMkPhysical hPeriodPhysical hDimPhysical
      hGPhysical hXPhysical hDPhysical hWL hprecision hηprecision hεprecision le_rfl

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uJ, uQ, uX, u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_constructed_finite_source_s2_oai.{uJ, uQ, uX, u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_constructed_finite_source_s2_oai.{uJ, uQ, uX, u_1, u_2, u_3, u_4}
