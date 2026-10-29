-- Prove2me | solution 1 for MIPStarRE.QPBT.SandwichProduct.avg_diagonal_postprocess_stateQForm_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:49:11.60599+00:00
-- url     : https://prove2.me/submissions/f79a5c9c-30fc-4164-84e0-9cb320504df6

-- Generated proof for MIPStarRE.QPBT.SandwichProduct.avg_diagonal_postprocess_stateQForm_le.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_defect_eq
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_SandwichProduct_diagonal_postprocess_stateQForm_eq_pair_sum

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
namespace MIPStarRE.QPBT.SandwichProduct
end MIPStarRE.QPBT.SandwichProduct

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

/-! # Quantitative support for sandwiched measurements

This module develops the consistency and operator-distance estimates used
in the quantitative sandwich argument.

## References

Blueprint `lem:ld-sandwich` and `lem:ld-sandwich-measurement`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

open MIPStarRE.QPBT.SandwichProduct

set_option maxHeartbeats 600000 in
-- The collision estimate expands two nested outcome sums at each evaluation point.

theorem solution
    {Y Γ R ιA ιB : Type*}
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype Γ] [DecidableEq Γ] [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (eval : Γ → Y → R) (ε : ℝ)
    (hψ : ‖ψ‖ = 1) (hε : 0 ≤ ε)
    (hcollision : ∀ g g' : Γ, g ≠ g' →
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y)
        (fun y => if eval g y = eval g' y then 1 else 0) ≤ ε) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y =>
      ∑ r : R, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron
          ((A.postprocess (fun g => eval g y)).effect r)
          ((B.postprocess (fun g => eval g y)).effect r))) ≤
      (∑ g : Γ, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect g) (B.effect g))) + ε := by
  classical
  let w : Γ → Γ → ℝ := fun g g' =>
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect g) (B.effect g'))
  have hw (g g' : Γ) : 0 ≤ w g g' := by
    apply _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg
    exact _root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg (A.pos g) (B.pos g')
  have hoffdiag_le_one :
      (∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else w g g') ≤ 1 := by
    let AL := _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ιB) A
    let BR := _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ιA) B
    have hpoint := _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq AL BR ψ
    simp only [AL, BR, _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement,
      _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne] at hpoint
    simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq] at hpoint
    have hdiag : 0 ≤ ∑ g : Γ, w g g :=
      Finset.sum_nonneg fun g _ => hw g g
    change (∑ g : Γ, ∑ g' : Γ, if g = g' then 0 else
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (A.effect g) (B.effect g'))) ≤ 1
    rw [hpoint, hψ]
    norm_num
    exact hdiag
  have hdiagpart :
      (∑ g : Γ, ∑ g' : Γ, if g = g' then w g g' else 0) =
        ∑ g : Γ, w g g := by
    apply Finset.sum_congr rfl
    intro g _
    rw [Fintype.sum_eq_single g]
    · simp
    · intro g' hg'
      simp [Ne.symm hg']
  have hsplit :
      (∑ g : Γ, ∑ g' : Γ,
        if g = g' then w g g' else ε * w g g') =
      (∑ g : Γ, w g g) +
        ε * (∑ g : Γ, ∑ g' : Γ,
          if g = g' then 0 else w g g') := by
    calc
      (∑ g : Γ, ∑ g' : Γ,
          if g = g' then w g g' else ε * w g g') =
          ∑ g : Γ, ∑ g' : Γ,
            ((if g = g' then w g g' else 0) +
              ε * (if g = g' then 0 else w g g')) := by
        apply Finset.sum_congr rfl
        intro g _
        apply Finset.sum_congr rfl
        intro g' _
        by_cases hgg' : g = g' <;> simp [hgg']
      _ = (∑ g : Γ, ∑ g' : Γ,
            if g = g' then w g g' else 0) +
          ε * (∑ g : Γ, ∑ g' : Γ,
            if g = g' then 0 else w g g') := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = _ := by rw [hdiagpart]
  change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y =>
      ∑ r : R, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron
          ((A.postprocess (fun g => eval g y)).effect r)
          ((B.postprocess (fun g => eval g y)).effect r))) ≤
    (∑ g : Γ, w g g) + ε
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y =>
        ∑ r : R, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
          (_root_.MIPStarRE.QPBT.heteroKron
            ((A.postprocess (fun g => eval g y)).effect r)
            ((B.postprocess (fun g => eval g y)).effect r))) =
        ∑ g : Γ, ∑ g' : Γ,
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y =>
            if eval g y = eval g' y then w g g' else 0) := by
      simp_rw [_root_.MIPStarRE.QPBT.SandwichProduct.diagonal_postprocess_stateQForm_eq_pair_sum]
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sum]
      apply Finset.sum_congr rfl
      intro g _
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sum]
    _ ≤ ∑ g : Γ, ∑ g' : Γ,
        if g = g' then w g g' else ε * w g g' := by
      apply Finset.sum_le_sum
      intro g _
      apply Finset.sum_le_sum
      intro g' _
      by_cases hgg' : g = g'
      · subst g'
        simp only [if_pos]
        exact le_of_eq (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const (w g g))
      · rw [if_neg hgg']
        calc
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y =>
              if eval g y = eval g' y then w g g' else 0) =
              _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y) (fun y =>
                (if eval g y = eval g' y then 1 else 0) * w g g') := by
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro y
            by_cases heq : eval g y = eval g' y <;> simp [heq]
          _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y)
              (fun y => if eval g y = eval g' y then 1 else 0) * w g g' :=
            _root_.LIDT.MIPStarRE.LDT.avgOver_mul_const _ _ _
          _ ≤ ε * w g g' :=
            mul_le_mul_of_nonneg_right (hcollision g g' hgg') (hw g g')
    _ = (∑ g : Γ, w g g) +
        ε * (∑ g : Γ, ∑ g' : Γ,
          if g = g' then 0 else w g g') := hsplit
    _ ≤ (∑ g : Γ, w g g) + ε := by
      gcongr
      simpa using mul_le_mul_of_nonneg_left hoffdiag_le_one hε
