-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_l1_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:00:14.835247+00:00
-- url     : https://prove2.me/submissions/6ce44b7e-5301-486a-bdd5-94e139ca7167

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B213
import Definitions.Def_OAIE3v2B217
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineIdeal_profile_integrable_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineWholeProfile_comparison_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCoefficientDeckSample_density_law_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCoveredProfileDensity_integrable_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProgressionCoveredExpectation_density_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedRowSlicedIdeal_measurable_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedWholeMaskedCoveredProfile_measurable_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedPhysicalCoveredDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

theorem standardLatticeClosedQuarterBox_isCompact (J : Type*) [Fintype J] :
    IsCompact (standardLatticeClosedQuarterBox J) := by
  have he : standardLatticeClosedQuarterBox J =
      (PiLp.homeomorph 2 (fun _ : J => ℝ)) ⁻¹'
        Set.Icc (fun _ => -(1 / 4 : ℝ)) (fun _ => (1 / 4 : ℝ)) := by
    ext x
    simp only [standardLatticeClosedQuarterBox, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_Icc, Pi.le_def, abs_le, forall_and]
    rfl
  rw [he]
  exact (PiLp.homeomorph 2 (fun _ : J => ℝ)).isClosedEmbedding.isCompact_preimage isCompact_Icc

theorem standardLatticeClosedQuarterBox_subset_smallBox (J : Type*) [Fintype J] :
    standardLatticeClosedQuarterBox J ⊆ standardLatticeSmallBox J := by
  intro x hx i
  exact (hx i).trans_lt (by norm_num)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedActualProfileControl
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value

theorem allocatedLongJetRealCoordinates_measurable :
    Measurable (allocatedLongJetRealCoordinates B U basis S (O := O)) := by
  apply measurable_pi_iff.mpr
  intro q
  rcases q with ⟨⟨⟨j, i | i⟩, ha⟩, o⟩
  · exact (measurable_pi_apply o).comp
      (show Measurable (fun z : AllocatedLongJetRows B U basis S O =>
        z ⟨⟨j, .inl i⟩, ha⟩) from measurable_pi_apply _)
  · exact (measurable_of_countable
      (fun z : O j → ℤ => (z o : ℝ) / (basisAxisScale (basis j) i : ℝ))).comp
      (show Measurable (fun z : AllocatedLongJetRows B U basis S O =>
        z ⟨⟨j, .inr i⟩, ha⟩) from measurable_pi_apply _)

variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

theorem allocatedLongJetMask_measurable (a : {a // ¬grid a}) :
    Measurable (allocatedLongJetMask B U basis S x rows modulus residue a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact measurable_const
  · change Measurable (allocatedIntegerKernelMask B U basis S x rows j modulus (residue j))
    exact measurable_of_countable _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedLongIntegralMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

theorem allocatedLongProfileDensity_measurable (f : (output → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (allocatedLongProfileDensity B U b S x rows modulus residue f) := by
  have hm : Measurable (fun z : AllocatedLongJetRows B U b S O =>
      ∏ a, allocatedLongJetMask B U b S x rows modulus residue a (z a)) :=
    Finset.measurable_prod _ (fun a _ =>
      (allocatedLongJetMask_measurable B U b S x rows modulus residue a).comp (measurable_pi_apply a))
  exact (hm.mul (hf.comp (allocatedLongJetRealCoordinates_measurable B U b S))).div_const _

end Erdos3.VectorPolynomial

end

end OAI
end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexSampledSquarePerturbation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem complex_model_l1_le_of_bounded_tests {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f μ) (hgi : Integrable g μ) {ε : ℝ}
    (he : ∀ φ : X → ℂ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      ‖(∫ x, f x * φ x ∂μ) - ∫ x, g x * φ x ∂μ‖ ≤ ε) :
    (∫ x, ‖f x - g x‖ ∂μ) ≤ ε := by
  let φ := fun x => (starRingEnd ℂ) (f x - g x) / (‖f x - g x‖ : ℂ)
  have hφ : Measurable φ := (Complex.continuous_conj.measurable.comp (hf.sub hg)).div (hf.sub hg).norm.complex_ofReal
  have hbound (x) : ‖φ x‖ ≤ 1 := by
    dsimp only [φ]
    rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self_le_one _
  have hidentity (x) : (f x - g x) * φ x = (‖f x - g x‖ : ℂ) := by
    dsimp only [φ]
    rw [← mul_div_assoc, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_div]
    by_cases h : ‖f x - g x‖ = 0
    · simp [h]
    · rw [pow_two, mul_div_cancel_right₀ _ h]
  have hif := hfi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hig := hgi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have h := he φ hφ hbound
  rw [← integral_sub hif hig] at h
  simp_rw [← sub_mul, hidentity] at h
  rw [integral_complex_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedFiniteModelComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

omit [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)] [Fintype α] in
theorem allocatedWholeMaskedCoveredProfile_join
    (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U b S))
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O a.val.1) → ℝ) → ℝ) :
    allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
      (principalAxisJoin grid u v) q f =
    allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
      (allocatedLongProfileDensity B U b S x rows q
        (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) q) f) := by
  simp only [allocatedWholeMaskedCoveredProfile, principalAxisRestrict_join_left,
    principalAxisRestrict_join_right]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineRecenteredSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable [∀ j, Nonempty (rowSets j)]
local notation "selectedRows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
variable (x : G → IntegerScalarCubeBox α S.value)
variable (s : ∀ j : Fin m, ↥(rowSets j) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (Subtype.val : rowSets j → Finset α)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := ↥(rowSets j))
  S.positive x (j.val + 1) (Subtype.val : rowSets j → Finset α) (s j) (hA j) (1 / (Mk : ℝ)))
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
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S)
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

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
omit [∀ j, Nonempty (rowSets j)] in
theorem allocatedAffineIdeal_l1_s2_oai
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S) →
  EuclideanJetLayers U selectedRows → ℝ)
    (hgm : ∀ y, Measurable (g y)) (hg0 : ∀ y z, 0 ≤ g y z)
    (hgi : ∀ y, Integrable (g y) ξ)
    (hglaw : ∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
  (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) = realDensityMeasure ξ (g y))
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    (hδ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card α + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (selection : α ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hq : Fintype.card α ≤ m + 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (selectedRows j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ (u : GridTuples) j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ≤ Cmask)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) :
    let center := principalProgressionSliceCenter (α := α) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := α) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, selectedRows a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let _outputResidue := fun (u : GridTuples) j => integerResidueMatrix
      (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    (∫ y, ‖((wholeLaw).mean (fun v => g v y) : ℂ) -
      ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows
        hb o bW d (principalAxisJoin grid u v₀) modulus ideal y) : ℂ)‖ ∂ξ) ≤
      (2 * Real.exp (allocatedJetSupportLog (G := G) B α selectedRows P) + 1)^
        Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) *
        (Fintype.card {a // ¬grid a} * εcoef *
          (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α selectedRows P) + εcoef)^
            Fintype.card {a // ¬grid a}) +
      allocatedAffineSourceReferenceError B U basis S α selectedRows (ρ grid) P η (fun _ => modulus) H ε mesh Cmask
 := by
  intro center width ideal outputResidue
  have hw := principalProgressionSlice_parameters (α := α) activeB activeDegree
    L H step c positiveLengths hstep hH hδ hsubset hdense
  have hidealm : Measurable ideal :=
    allocatedRowSlicedIdeal_measurable_s2 B U basis S rowSets hR (ρ grid) hρ center width
  let profile := fun u y => allocatedWholeMaskedCoveredProfile B U basis hR hσ S x rows
    hb o bW d (principalAxisJoin grid u v₀) modulus ideal y
  have hprofilem (u) : Measurable (profile u) :=
    allocatedWholeMaskedCoveredProfile_measurable_s2 B U basis hR hσ S x rows hb o bW d
      (principalAxisJoin grid u v₀) modulus ideal hidealm
  have hprofilei (u) : Integrable (profile u) ξ := by
    have hfm := allocatedLongProfileDensity_measurable B U basis S x rows
      modulus (outputResidue u) ideal hidealm
    have hfi := allocatedAffineIdeal_profile_integrable_s2 B U basis hR S x rows
      hRP hRi (ρ grid) hρ hρ1 center width (fun i => (hw i).2.2)
      modulus (outputResidue u) hCmask (hmask u)
    have hi := allocatedCoveredProfileDensity_integrable_s2 B U basis hR hσ S x u v₀ rows
      hb o bW d (fun j (_ : selectedRows j) => standardLatticeClosedQuarterBox (J j))
      (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).measurableSet)
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)) ν _ hfm hfi
    simpa only [profile, allocatedWholeMaskedCoveredProfile_join] using hi
  have hmeanm : Measurable (fun y => ((wholeLaw).mean (fun v => g v y) : ℂ)) :=
    (Finset.measurable_sum Finset.univ (fun v _ => (hgm v).const_mul _)).complex_ofReal
  have hmeani : Integrable (fun y => ((wholeLaw).mean (fun v => g v y) : ℂ)) ξ :=
    (integrable_finsetSum Finset.univ (fun v _ => (hgi v).const_mul _)).ofReal
  have hmodelm : Measurable (fun y => ((gridLaw).mean (fun u => profile u y) : ℂ)) :=
    ((gridLaw).mean_measurable _ hprofilem).complex_ofReal
  have hmodeli : Integrable (fun y => ((gridLaw).mean (fun u => profile u y) : ℂ)) ξ :=
    (integrable_finsetSum Finset.univ (fun u _ => (hprofilei u).const_mul _)).ofReal
  apply complex_model_l1_le_of_bounded_tests ξ _ _ hmeanm hmodelm hmeani hmodeli
  intro F hF hFbound
  have hc := allocatedAffineWholeProfile_comparison_s2 B U basis hR hσ S rows x s hA hMk hi
    hP hMkP hRP hRi hσi hcount Q hb o bW d F H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell ν
    ρ t htone hs hρ hρ1 hσsmall hstep hH hδ hdense hm hsize hsmall hε hmesh
    selection hgood hq he hεcoef hεe hlarge hperiod v₀ hv₀ hmesh0 hmesh1 hscaleMesh hCmask hmask
    T hT hsource C hC hchart hbudget hF hFbound
  have hsmallDensity (j) : C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4 := by
    have hT1 : 1 ≤ T j := (le_add_of_nonneg_left (partitionedIdealRadius_nonneg α m)).trans (hT j)
    have hRle : R j ≤ T j * R j := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hT1 (hR j).le
    calc
      _ = C j * (((Fintype.card (I j) : ℝ) + 1) * R j) := mul_assoc _ _ _
      _ ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRle
          (add_nonneg (Nat.cast_nonneg _) zero_le_one)) (hC j)
      _ ≤ _ := hbudget j
  have hdeck := allocatedCoefficientDeckSample_density_law_s2 B U basis hR hσ S Q hb o bW d μ ν
    (fun j => (hσsmall j).trans htone) C hC hchart hsmallDensity
  have hid := allocatedProgressionCoveredExpectation_density_s2 B U basis hR hσ S rows x Q hb o bW d
    H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell μ ν hdeck g hgm hg0 hgi hglaw F hF hFbound
  rw [hid] at hc
  exact hc

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uJ, uQ, u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_l1_s2_oai.{uJ, uQ, u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.allocatedAffineIdeal_l1_s2_oai.{uJ, uQ, u_1, u_2, u_3, u_4}
