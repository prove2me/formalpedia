-- Prove2me | solution 1 for MIPStarRE.QPBT.projective_rounding_preserves_postprocessed_consistency_left
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:17:59.570507+00:00
-- url     : https://prove2.me/submissions/42c194fc-53a1-4e10-92d7-41825f7e0395

-- Generated proof for MIPStarRE.QPBT.projective_rounding_preserves_postprocessed_consistency_left.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_consistencyDefect_eq_one_sub_overlap
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_overlap_gap_le_of_opFamilyDistSq
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_postprocess_le
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_trans_le
import Theorems.Thm_MIPStarRE_QPBT_projective_rounding_with_explicit_constant

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

























































































/-- Formalization-only auxiliary lemma for Proposition 4.29: state-dependent
operator-family distance is symmetric. -/
theorem opFamilyDistSq_symm {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ B A ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, map_sub, LinearMap.sub_apply]
  rw [norm_sub_rev]

end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/DistanceTheorems/TensorSupport.lean. -/
/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective





/-- Formalization-only auxiliary lemma for Fact 4.26: products of left and right
placements evaluate as a Kronecker product. -/
theorem placed_product_stateQForm_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A 1 * _root_.MIPStarRE.QPBT.heteroKron 1 B) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A B) := by
  congr 1
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor A B































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/DistanceTheorems/RoundingTransport.lean. -/
/-!
# Projective rounding through outcome postprocessing

Consistent complete POVMs on two possibly different local spaces have projective
roundings on those same spaces. Their consistency with an opposite-player POVM
survives every question-dependent outcome map, with error
`δ + sqrt (220 * δ^(1/4)) + 2 * sqrt (δ + η)` when the original consistency errors
are at most `δ` and `η`. The estimate is independent of both local dimensions and
the number of outcomes.

These are formalization-only auxiliary results for the compression and rounding
argument preceding the polynomial-support argument in `lem:qld-4-7`. They do not
construct the global polynomial-pair measurement.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:135-145`, `lem:ortho`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1288`,
  in the proof of `lem:qld-4-7`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-401`,
  `fact:triangle-for-simeq` and `fact:data-processing`
- Issue Dengnifer/MIPStarRE-QPBT-bak#278
- `audits/2026-09-06_rounding_transport.md`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- Formalization-only question-dependent form of `fact:data-processing`.
Applying the same outcome map to both players at each question cannot increase
their consistency defect. No normalization of the distribution or state is needed. -/
theorem consistencyDefect_postprocess_question_le {X α β ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA)
    (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB) (ψ : EuclideanSpace ℂ (ιA × ιB))
    (f : X → α → β) :
    _root_.MIPStarRE.QPBT.consistencyDefect μ
        (fun x b => _root_.MIPStarRE.QPBT.heteroKron (((A x).postprocess (f x)).effect b) 1)
        (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 (((B x).postprocess (f x)).effect b)) ψ ≤
      _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
  intro x
  simpa only [_root_.MIPStarRE.QPBT.consistencyDefect,
    _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability Unit)] using
    _root_.MIPStarRE.QPBT.consistencyDefect_postprocess_le (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun _ => A x) (fun _ => B x) ψ (f x)

private theorem consistencyDefect_const_eq {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (hμ : μ.IsProbability)
    (A B : α → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.consistencyDefect μ (fun _ => A) (fun _ => B) ψ =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit) (fun _ => A) (fun _ => B) ψ := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability μ hμ,
    _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability Unit)]

private theorem consistencyDefect_placed_eq_one_sub_overlap {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) :
    _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ =
      1 - _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) ((B x).effect a))) := by
  simpa only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne, _root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq] using
    _root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ
      (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (A x)) (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (B x))
      ψ hμ hψ

/-- The overlap estimate converts a same-space squared-distance bound into a
square-root loss in consistency with the unchanged opposite-player POVM. -/
private theorem rounding_consistency_le {ιA ιB α : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [DecidableEq α]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (P A : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB) (δ r : ℝ)
    (hcons : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (A.effect a) 1)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron 1 (B.effect a)) ψ ≤ δ)
    (hdist : _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (P.effect a) 1)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (A.effect a) 1) ψ ≤ r) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (P.effect a) 1)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron 1 (B.effect a)) ψ ≤ δ + Real.sqrt r := by
  letI : Nonempty (ιA × ιB) := by
    by_contra hι
    letI : IsEmpty (ιA × ιB) := not_nonempty_iff.mp hι
    have hzero : ψ = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero] at hψ
    norm_num at hψ
  have hgap := _root_.MIPStarRE.QPBT.DistanceCalculus.overlap_gap_le_of_opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
    (fun _ => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement B) (fun _ => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement A)
    (fun _ => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement P) ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability Unit)
    hψ r (by
      simpa only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne,
        _root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_symm] using hdist)
  rw [consistencyDefect_placed_eq_one_sub_overlap (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
    (fun _ => A) (fun _ => B)
    ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability Unit) hψ] at hcons
  rw [consistencyDefect_placed_eq_one_sub_overlap (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
    (fun _ => P) (fun _ => B)
    ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability Unit) hψ]
  simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at hgap
  change |avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit) (fun _ => ∑ a,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.LIDT.MIPStarRE.LDT.rightTensor (B.effect a) * _root_.LIDT.MIPStarRE.LDT.leftTensor (A.effect a))) -
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit) (fun _ => ∑ a,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.LIDT.MIPStarRE.LDT.rightTensor (B.effect a) * _root_.LIDT.MIPStarRE.LDT.leftTensor (P.effect a)))| ≤ _ at hgap
  simp only [_root_.LIDT.MIPStarRE.LDT.rightTensor_mul_leftTensor_eq_opTensor] at hgap
  dsimp only [_root_.LIDT.MIPStarRE.LDT.opTensor, _root_.MIPStarRE.QPBT.heteroKron] at hgap hcons ⊢
  have hdiff := (le_abs_self _).trans hgap
  linarith















end

end MIPStarRE.QPBT

/-!
# Projective rounding through outcome postprocessing

Consistent complete POVMs on two possibly different local spaces have projective
roundings on those same spaces. Their consistency with an opposite-player POVM
survives every question-dependent outcome map, with error
`δ + sqrt (220 * δ^(1/4)) + 2 * sqrt (δ + η)` when the original consistency errors
are at most `δ` and `η`. The estimate is independent of both local dimensions and
the number of outcomes.

These are formalization-only auxiliary results for the compression and rounding
argument preceding the polynomial-support argument in `lem:qld-4-7`. They do not
construct the global polynomial-pair measurement.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:135-145`, `lem:ortho`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1288`,
  in the proof of `lem:qld-4-7`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-401`,
  `fact:triangle-for-simeq` and `fact:data-processing`
- Issue Dengnifer/MIPStarRE-QPBT-bak#278
- `audits/2026-09-06_rounding_transport.md`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution
    {ιA ιB α : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [DecidableEq α]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB) (δ : ℝ) (hδ : 0 ≤ δ)
    (hcons : _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (A.effect a) 1)
      (fun _ a => _root_.MIPStarRE.QPBT.heteroKron 1 (B.effect a)) ψ ≤ δ) :
    ∃ P : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA, _root_.MIPStarRE.QPBT.Measurement.IsProjective P ∧
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (P.effect a) 1)
        (fun _ a => _root_.MIPStarRE.QPBT.heteroKron (A.effect a) 1) ψ ≤
          220 * Real.rpow δ (1 / 4 : ℝ) ∧
      ∀ {X β : Type*} [Fintype X] [DecidableEq X] [Fintype β] [DecidableEq β]
        (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X), μ.IsProbability → ∀ (f : X → α → β)
        (N : X → _root_.LIDT.MIPStarRE.Quantum.Measurement β ιB) (η : ℝ),
        _root_.MIPStarRE.QPBT.consistencyDefect μ
          (fun x b => _root_.MIPStarRE.QPBT.heteroKron ((A.postprocess (f x)).effect b) 1)
          (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 ((N x).effect b)) ψ ≤ η →
        _root_.MIPStarRE.QPBT.consistencyDefect μ
          (fun x b => _root_.MIPStarRE.QPBT.heteroKron ((P.postprocess (f x)).effect b) 1)
          (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 ((N x).effect b)) ψ ≤
            δ + Real.sqrt (220 * Real.rpow δ (1 / 4 : ℝ)) +
              2 * Real.sqrt (δ + η) := by
  obtain ⟨P, hP, hdist⟩ :=
    _root_.MIPStarRE.QPBT.projective_rounding_with_explicit_constant ψ hψ A B δ hδ hcons
  refine ⟨P, hP, hdist, ?_⟩
  intro X β _ _ _ _ μ hμ f N η hAN
  have hPB := rounding_consistency_le ψ hψ P A B δ _ hcons hdist
  have hABf : _root_.MIPStarRE.QPBT.consistencyDefect μ
      (fun x b => _root_.MIPStarRE.QPBT.heteroKron ((A.postprocess (f x)).effect b) 1)
      (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 ((B.postprocess (f x)).effect b)) ψ ≤ δ := by
    refine (_root_.MIPStarRE.QPBT.consistencyDefect_postprocess_question_le μ
      (fun _ => A) (fun _ => B) ψ f).trans ?_
    rw [consistencyDefect_const_eq μ hμ]
    exact hcons
  have hPBf : _root_.MIPStarRE.QPBT.consistencyDefect μ
      (fun x b => _root_.MIPStarRE.QPBT.heteroKron ((P.postprocess (f x)).effect b) 1)
      (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 ((B.postprocess (f x)).effect b)) ψ ≤
        δ + Real.sqrt (220 * Real.rpow δ (1 / 4 : ℝ)) := by
    refine (_root_.MIPStarRE.QPBT.consistencyDefect_postprocess_question_le μ
      (fun _ => P) (fun _ => B) ψ f).trans ?_
    rw [consistencyDefect_const_eq μ hμ]
    exact hPB
  simpa only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] using _root_.MIPStarRE.QPBT.consistencyDefect_trans_le μ
    (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (P.postprocess (f x)))
    (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (B.postprocess (f x)))
    (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (A.postprocess (f x)))
    (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (N x)) ψ _ δ η hμ hψ hPBf hABf hAN
