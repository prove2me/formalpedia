-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_codeword_fine_le_coarse_add_distinct_families
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:49:11.37578+00:00
-- url     : https://prove2.me/submissions/a9619a4e-38f6-416c-adc1-af39e0220cc2

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_codeword_fine_le_coarse_add_distinct_families.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_defect_eq
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_SandwichProduct_consistencyDefect_placed_eq_avg_point
import Theorems.Thm_MIPStarRE_QPBT_SandwichProduct_diagonal_postprocess_stateQForm_eq_pair_sum
import Theorems.Thm_MIPStarRE_QPBT_avgOver_collision_le

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





























/-- A positive semidefinite operator has nonnegative state quadratic form. This
is the formalization-only order fact `lem:distance-qform-nonnegative`, used for
the nonnegative overlap terms in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) {M : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hM : 0 ≤ M) :
    0 ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  calc
    0 = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ 0 := by simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
    _ ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hM ψ





























































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

/-! # Consistency and commutation of the pasting codeword families

This module records the cross consistency of the coarse second codeword family,
the commutator estimate for the two coarse families, the collision average of
the distinct second codewords, and the comparison of the fine second codeword
family with its coarse-graining.  These are the codeword-family steps of the
proof of `lem:pasting` recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `blueprint/src/chapter/ch12_qpbt_games.tex:960-1050`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

theorem solution
    {X Y₁ Y₂ R₂ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (D : _root_.LIDT.MIPStarRE.LDT.Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₂ opposite : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ι) (ψ : EuclideanSpace ℂ (ι × ι)) (η : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hη : 0 ≤ η)
    (hcoll : ∀ x y₁, 0 < (D.map Prod.fst).weight (x, y₁) →
      ∀ g g' : Γ₂, g ≠ g' →
        (∑ y₂ : Y₂, D.weight ((x, y₁), y₂) *
          if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0) ≤
          η * (D.map Prod.fst).weight (x, y₁)) :
    _root_.MIPStarRE.QPBT.consistencyDefect D
        (fun q g => _root_.MIPStarRE.QPBT.heteroKron ((opposite q.1.1).effect g) 1)
        (fun q g => _root_.MIPStarRE.QPBT.heteroKron 1 ((G₂ q.1.1).effect g)) ψ ≤
      _root_.MIPStarRE.QPBT.consistencyDefect D
        (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron (((opposite q.1.1).postprocess
          (fun g => eval₂ g q.2)).effect a₂) 1)
        (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₂ q.1.1).postprocess
          (fun g => eval₂ g q.2)).effect a₂)) ψ + η := by
  classical
  have hcnn : ∀ (x : X) (g g' : Γ₂), 0 ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
      (_root_.MIPStarRE.QPBT.heteroKron ((opposite x).effect g) ((G₂ x).effect g')) := by
    intro x g g'
    exact _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg ψ (_root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg ((opposite x).pos g) ((G₂ x).pos g'))
  have hfine : ∀ x : X,
      (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron ((opposite x).effect g) ((G₂ x).effect g'))) =
      ‖ψ‖ ^ 2 - ∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron ((opposite x).effect g) ((G₂ x).effect g)) := by
    intro x
    have h := _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ι) (opposite x))
      (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ι) (G₂ x)) ψ
    simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement,
      _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at h
    simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq] at h
    exact h
  have hcoarse : ∀ (x : X) (y₂ : Y₂),
      (∑ r : R₂, ∑ r' : R₂, if r = r' then 0 else _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron (((opposite x).postprocess (fun g => eval₂ g y₂)).effect r)
          (((G₂ x).postprocess (fun g => eval₂ g y₂)).effect r'))) =
      ‖ψ‖ ^ 2 - ∑ r : R₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron (((opposite x).postprocess (fun g => eval₂ g y₂)).effect r)
          (((G₂ x).postprocess (fun g => eval₂ g y₂)).effect r)) := by
    intro x y₂
    have h := _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq
      (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ι)
        ((opposite x).postprocess (fun g => eval₂ g y₂)))
      (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ι)
        ((G₂ x).postprocess (fun g => eval₂ g y₂))) ψ
    simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement,
      _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at h
    simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq] at h
    exact h
  have hsplit : ∀ (x : X) (y₂ : Y₂),
      (∑ g : Γ₂, ∑ g' : Γ₂, if eval₂ g y₂ = eval₂ g' y₂ then _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron ((opposite x).effect g) ((G₂ x).effect g')) else 0) =
      (∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron ((opposite x).effect g) ((G₂ x).effect g))) +
      (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else
        if eval₂ g y₂ = eval₂ g' y₂ then _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
          (_root_.MIPStarRE.QPBT.heteroKron ((opposite x).effect g) ((G₂ x).effect g')) else 0) := by
    intro x y₂
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hterm : ∀ g' : Γ₂,
        (if g = g' then (0 : ℝ) else
          if eval₂ g y₂ = eval₂ g' y₂ then _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
            (_root_.MIPStarRE.QPBT.heteroKron ((opposite x).effect g) ((G₂ x).effect g')) else 0) =
        (if eval₂ g y₂ = eval₂ g' y₂ then _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
            (_root_.MIPStarRE.QPBT.heteroKron ((opposite x).effect g) ((G₂ x).effect g')) else 0) -
        (if g = g' then _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
            (_root_.MIPStarRE.QPBT.heteroKron ((opposite x).effect g) ((G₂ x).effect g')) else 0) := by
      intro g'
      by_cases hg : g = g'
      · subst hg; simp
      · simp [hg]
    rw [Finset.sum_congr rfl (fun g' (_ : g' ∈ Finset.univ) => hterm g'),
      Finset.sum_sub_distrib]
    have hdel : (∑ g' : Γ₂, if g = g' then _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron ((opposite x).effect g) ((G₂ x).effect g')) else 0) =
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((opposite x).effect g) ((G₂ x).effect g)) := by
      simp
    rw [hdel]
    ring
  have hkey : ∀ q : (X × Y₁) × Y₂,
      (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron ((opposite q.1.1).effect g) ((G₂ q.1.1).effect g'))) =
      (∑ r : R₂, ∑ r' : R₂, if r = r' then 0 else _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron (((opposite q.1.1).postprocess (fun g => eval₂ g q.2)).effect r)
          (((G₂ q.1.1).postprocess
            (fun g => eval₂ g q.2)).effect r'))) +
      (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else
        if eval₂ g q.2 = eval₂ g' q.2 then _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
          (_root_.MIPStarRE.QPBT.heteroKron ((opposite q.1.1).effect g) ((G₂ q.1.1).effect g')) else 0) := by
    intro q
    rw [hfine q.1.1, hcoarse q.1.1 q.2,
      _root_.MIPStarRE.QPBT.SandwichProduct.diagonal_postprocess_stateQForm_eq_pair_sum (opposite q.1.1) (G₂ q.1.1) ψ
        (fun g => eval₂ g q.2), hsplit q.1.1 q.2]
    ring
  have hmass : ∀ p : X × Y₁,
      (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron ((opposite p.1).effect g) ((G₂ p.1).effect g'))) ≤ 1 := by
    intro p
    rw [hfine p.1, hψ, one_pow]
    have hnn : 0 ≤ ∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron ((opposite p.1).effect g) ((G₂ p.1).effect g)) :=
      Finset.sum_nonneg fun g _ => hcnn p.1 g g
    linarith
  have havg := _root_.MIPStarRE.QPBT.avgOver_collision_le D eval₂
    (fun p g g' => _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
      (_root_.MIPStarRE.QPBT.heteroKron ((opposite p.1).effect g) ((G₂ p.1).effect g'))) η hD hη
    (fun p g g' => hcnn p.1 g g') hmass hcoll
  rw [_root_.MIPStarRE.QPBT.SandwichProduct.consistencyDefect_placed_eq_avg_point D (fun q => opposite q.1.1)
      (fun q => G₂ q.1.1) ψ,
    _root_.MIPStarRE.QPBT.SandwichProduct.consistencyDefect_placed_eq_avg_point D
      (fun q => (opposite q.1.1).postprocess (fun g => eval₂ g q.2))
      (fun q => (G₂ q.1.1).postprocess (fun g => eval₂ g q.2)) ψ]
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr D _ _ hkey, _root_.LIDT.MIPStarRE.LDT.avgOver_add]
  linarith
