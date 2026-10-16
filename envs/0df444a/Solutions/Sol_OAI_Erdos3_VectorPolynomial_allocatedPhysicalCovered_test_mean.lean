-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedPhysicalCovered_test_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T04:46:49.841956+00:00
-- url     : https://prove2.me/submissions/499c2d7a-ef84-4f77-bd32-afe0e4dbcba8

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1384
import Theorems.Thm_OAI_Erdos3_FiniteProbabilityWeights_complexMean_congr_support
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedPhysicalMixedJet_test_mean

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedWholeDeckLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v w : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

theorem allocatedPartitionedJetMatrix_image_eq_of_residue (M : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hvw : principalResidueLabel M v = principalResidueLabel M w) (j : Fin m) :
    (allocatedPartitionedJetMatrix B U b S x u v rows j).mulVecLin.range =
      (allocatedPartitionedJetMatrix B U b S x u w rows j).mulVecLin.range := by
  apply integerMatrixImage_eq_of_residueMatrix _ _ M
  · exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u v rows j)
  · exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u w rows j)
  · apply integerMappedJetMatrix_residue
    exact congrArg principalTupleResidues hvw

theorem allocatedPhysicalDeckJet_law_eq_of_residue
    (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (M : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hvw : principalResidueLabel M v = principalResidueLabel M w) (d : ℕ) [NeZero d] :
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (root v) (dirs v) rows d) =
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
        (coefficientDeckJetMap (root w) (dirs w) rows d) := by
  have hr (j : Fin m) :
      (boundedCoefficientJetMatrix (root v) (dirs v) (j.val + 1) (rows j)).mulVecLin.range =
        (boundedCoefficientJetMatrix (root w) (dirs w) (j.val + 1) (rows j)).mulVecLin.range := by
    rw [← allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j,
      ← allocatedPartitionedJetMatrix_eq_physical B U b S x u w rows j]
    exact allocatedPartitionedJetMatrix_image_eq_of_residue B U b S x u v w rows M hperiod hvw j
  exact uniformPMF_map_hom_eq_of_range_eq _ _
    (coefficientDeckJetMap_range_eq_of_integer_range_eq
      (α := α) (K := LayerSamplerVariables G I n B) (O := O) (B := Q)
      (root v) (dirs v) rows (root w) (dirs w) hr d)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix Classical



end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoveredFixedTest
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem probabilityProduct_finiteMean {X Y T : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (w : FiniteProbabilityWeights T) (f : T → X × Y → ℂ)
    (hf : ∀ t, Measurable (f t)) {C : ℝ} (hb : ∀ t p, ‖f t p‖ ≤ C) :
    (∫ p, w.complexMean (fun t => f t p) ∂μ.prod ν) =
      ∫ x, w.complexMean (fun t => ∫ y, f t (x, y) ∂ν) ∂μ := by
  have hi (t) : Integrable (f t) (μ.prod ν) :=
    Integrable.of_bound (hf t).aestronglyMeasurable C (ae_of_all _ (hb t))
  rw [integral_prod _ (w.complexMean_integrable _ _ hi)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  apply w.integral_complexMean
  intro t
  exact Integrable.of_bound ((hf t).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    C (ae_of_all _ (fun y => hb t (x, y)))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "split" => allocatedCoefficientSplit B U b S
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

variable (φ : (AllocatedFrozenCoefficients B U b S ×
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))) × (∀ j, O j → Q j → ZMod d) → ℂ)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

theorem allocatedPhysicalMixedDeck_test_mean
    (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (M : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hresidue : ∀ v, weights.weight v ≠ 0 → principalResidueLabel M v = principalResidueLabel M v₀)
    (hφ : Measurable φ) {C : ℝ} (hbound : ∀ p, ‖φ p‖ ≤ C) :
    (∫ p, weights.complexMean (fun v =>
      φ (((split p.1).1, canonicalCoefficientJetArrays (root v) (dirs v) rows p.1),
        coefficientDeckJetMap (root v) (dirs v) rows d p.2)) ∂(source).prod (deck).toMeasure) =
      ∫ a₀, ∫ z,
        (weights.mean (fun v => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) : ℂ) *
          allocatedDeckMixedTest B U b S x u v₀ rows Q d φ a₀
            (allocatedMixedJetReconstruct B U b S x u v₀ rows a₀ z) ∂reference ∂frozenSource := by
  let : IsProbabilityMeasure source := allocatedCoefficientSource_probability B U b hR hσ S
  have htest (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
      Measurable (fun p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
        CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d =>
        φ (((split p.1).1, canonicalCoefficientJetArrays (root v) (dirs v) rows p.1),
          coefficientDeckJetMap (root v) (dirs v) rows d p.2)) :=
    hφ.comp ((((split).measurable.comp measurable_fst).fst.prodMk
      ((canonicalCoefficientJetArrays_measurable (root v) (dirs v) rows).comp measurable_fst)).prodMk
        ((measurable_of_finite (coefficientDeckJetMap (B := Q) (root v) (dirs v) rows d)).comp measurable_snd))
  calc
    _ = ∫ a, weights.complexMean (fun v => ∫ r,
        φ (((split a).1, canonicalCoefficientJetArrays (root v) (dirs v) rows a),
          coefficientDeckJetMap (root v) (dirs v) rows d r) ∂(deck).toMeasure) ∂source :=
      probabilityProduct_finiteMean source (deck).toMeasure weights _ htest (fun _ p => hbound _)
    _ = ∫ a, weights.complexMean (fun v => allocatedDeckMixedTest B U b S x u v₀ rows Q d φ
        (split a).1 (canonicalCoefficientJetArrays (root v) (dirs v) rows a)) ∂source := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a
      apply weights.complexMean_congr_support
      intro v hv
      let F := fun e => φ (((split a).1, canonicalCoefficientJetArrays (root v) (dirs v) rows a), e)
      have hlaw := allocatedPhysicalDeckJet_law_eq_of_residue B U b S x u v v₀ rows Q M hperiod
        (hresidue v hv) d
      exact (finitePMF_integral_comp deck (coefficientDeckJetMap (root v) (dirs v) rows d) F).trans
        ((congrArg (fun p : PMF (∀ j, O j → Q j → ZMod d) => ∫ e, F e ∂p.toMeasure) hlaw).trans
          (finitePMF_integral_comp deck (coefficientDeckJetMap (root v₀) (dirs v₀) rows d) F).symm)
    _ = _ := allocatedPhysicalMixedJet_test_mean B U b hR hσ S x u v₀ rows s hA hσ1 weights
      (allocatedDeckMixedTest B U b S x u v₀ rows Q d φ)
      (allocatedDeckMixedTest_measurable B U b S x u v₀ rows Q d φ hφ)
      (allocatedDeckMixedTest_norm_le B U b S x u v₀ rows Q d φ hbound)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "split" => allocatedCoefficientSplit B U b S
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "pullback" => (fun p : (AllocatedFrozenCoefficients B U b S ×
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))) × (∀ j, O j → Q j → ZMod d) =>
  F (Prod.fst (Prod.fst p), coveredJetChart U b hb bW d
    (mixedCoveredJetCoordinates U o d (Prod.snd (Prod.fst p), Prod.snd p))))

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

theorem allocatedPhysicalCovered_test_mean_oai
    (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (M : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hresidue : ∀ v, weights.weight v ≠ 0 → principalResidueLabel M v = principalResidueLabel M v₀)
    (hF : Measurable F) {C : ℝ} (hbound : ∀ p, ‖F p‖ ≤ C) :
    (∫ p, weights.complexMean (fun v => F ((split p.1).1,
      euclideanCoefficientJetMap U (root v) (dirs v) rows
        (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
        ∂(source).prod (deck).toMeasure) =
      ∫ a₀, ∫ z,
        (weights.mean (fun v => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) : ℂ) *
          allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F a₀ z ∂reference ∂frozenSource := by
  have he := allocatedPhysicalMixedDeck_test_mean B U b hR hσ S x u v₀ rows Q d pullback
    s hA hσ1 weights M hperiod hresidue
    (allocatedCoveredPullback_measurable B U b S Q hb o bW d F hF) (fun p => hbound _)
  calc
    _ = ∫ p, weights.complexMean (fun v =>
        pullback (((split p.1).1, canonicalCoefficientJetArrays (root v) (dirs v) rows p.1),
          coefficientDeckJetMap (root v) (dirs v) rows d p.2)) ∂(source).prod (deck).toMeasure := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro p
      apply congrArg weights.complexMean
      funext v
      rw [canonicalCoefficientDeckSample_chart U o (root v) (dirs v) rows b hb bW d]
    _ = _ := he

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedPhysicalCovered_test_mean_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.allocatedPhysicalCovered_test_mean_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
