-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.avg_sandwich_defect_bound_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:27:40.373169+00:00
-- url     : https://prove2.me/submissions/274360f8-b7e7-4cbc-aa35-79d7c59872aa

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.avg_sandwich_defect_bound_le_explicit.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Points_Commutation
import Definitions.Def_QPBT_QPBT_Combining_Points_Consistency
import Definitions.Def_QPBT_QPBT_ExplicitConstants
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_exp_point_comm_explicit
import Theorems.Thm_MIPStarRE_QPBT_Strategy_value_le_one
import Theorems.Thm_MIPStarRE_QPBT_exp_point_self_cons_explicit

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Observables/WinImplications/AnticommutingObs.lean. -/
/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/











/-! ## From the Magic Square variables to the point observables -/









/-! ## The anticommuting half of the twisted commutation -/



/-- Every strategy value is at most one. This is an alias of the Games-layer
`MIPStarRE.QPBT.Strategy.value_le_one`, which carries the single proof; the name
is kept here so the existing callers of this layer resolve unchanged.
Formalization-only support for `def:tensor-product-value`, blueprint
`ch12_qpbt_games.tex:71-82`. -/
theorem strategy_value_le_one {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) : S.value ≤ 1 :=
  _root_.MIPStarRE.QPBT.Strategy.value_le_one S

















end WinImplications

end

end MIPStarRE.QPBT

/-!
# Self-consistency of the sandwich POVM

The sandwich POVM `R^{x,z}_{a,b} = M^Z_b M^X_a M^Z_b` of
`MIPStarRE/QPBT/Combining/Points/Sandwich.lean` is approximately self-consistent
between opposite register placements.  The source establishes this by a
Cauchy--Schwarz chain (displays `eq:qld-rw-self-cons-1` to
`eq:qld-rw-self-cons-4`); here an exact identity is used instead.  Writing
`P_1, P_2` for the two placements of an operator `P`,
`W_b = (M^Z_b)_1 (M^Z_b)_2`, and `D^W_c = (M^W_c)_1 - (M^W_c)_2`, the
consistency defect of the two placed sandwiches equals
`(1/2) ∑_b ‖D^Z_b ψ‖^2 + (1/2) ∑_{a,b} ‖D^X_a W_b ψ‖^2`,
by two applications of the identity
`∑_c ⟨w, P_c Q_c w⟩ = ‖w‖^2 - (1/2) ∑_c ‖(P_c - Q_c) w‖^2` for projective
measurements.  The second sum is then bounded by the self-consistency of `M^X`
and the commutators on the two placements, since
`D^X_a W_b = W_b D^X_a + (M^Z_b)_2 K^1_{a,b} - (M^Z_b)_1 K^2_{a,b}`, where
`K^i_{a,b}` is the placed commutator of `M^X_a` and `M^Z_b`.

## Main results

* `sandwich_overlap_identity`: the exact expression of the overlap of two
  placed sandwiches.
* `sandwich_defect_pointwise_le`: the pointwise bound on the consistency
  defect of the sandwich for a fixed point pair.
* `ProjectiveSetting.sandwichDefectBound`,
  `ProjectiveSetting.sandwich_offDiagonal_le_sandwichDefectBound`, and
  `ProjectiveSetting.avg_sandwichDefectBound_le`: the bound as a function of
  the point pair, the pointwise estimate, and the average.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:743-790`,
blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex:851-880`
(`lem:qld-4-10`, first step); the identity route is explained in
`docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Quadratic-form identities -/









/-! ## The overlap of two placed sandwiches -/



variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]











/-! ## The bound for the placed sandwiches -/

open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
      (p₁ p₂ : _root_.MIPStarRE.QPBT.Placement), p₁.IsOpposite p₂ →
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P)) (S.sandwichDefectBound p₁ p₂) ≤
        (344 + 3 * _root_.MIPStarRE.QPBT.pauliBaselineTwistedConstant) * (ε + Real.sqrt ε) := by
  intro P ε S p₁ p₂ hopp
  have hC₁ : (1 : ℝ) ≤ 172 := by norm_num
  have hC₂ : (1 : ℝ) ≤ _root_.MIPStarRE.QPBT.pauliBaselineTwistedConstant := by
    simp only [_root_.MIPStarRE.QPBT.pauliBaselineTwistedConstant, _root_.MIPStarRE.QPBT.pauliBaselineCommutatorConstant]
    nlinarith [Real.sqrt_nonneg (344 : ℝ)]
  have hε : (0 : ℝ) ≤ ε := by
    have hv := _root_.MIPStarRE.QPBT.WinImplications.strategy_value_le_one S.toStrategy
    have hw := S.win
    linarith
  have hZ : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P)) (fun xz =>
      ∑ b : _root_.MIPStarRE.QPBT.PauliScalar P, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect b) -
          S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect b)) S.psiHat‖ ^ 2) ≤
      172 * ε := by
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_snd (α := Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
      (fun z => ∑ b : _root_.MIPStarRE.QPBT.PauliScalar P, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .Z z).effect b) -
          S.place p₂ ((S.pointMeasExp p₂.side .Z z).effect b)) S.psiHat‖ ^ 2)]
    exact _root_.MIPStarRE.QPBT.exp_point_self_cons_explicit P ε S p₁ p₂ hopp .Z
  have hX : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P)) (fun xz =>
      ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .X xz.1).effect a) -
          S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect a)) S.psiHat‖ ^ 2) ≤
      172 * ε := by
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_fst (β := Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
      (fun x => ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .X x).effect a) -
          S.place p₂ ((S.pointMeasExp p₂.side .X x).effect a)) S.psiHat‖ ^ 2)]
    exact _root_.MIPStarRE.QPBT.exp_point_self_cons_explicit P ε S p₁ p₂ hopp .X
  have hK₁ := _root_.MIPStarRE.QPBT.ProjectiveSetting.exp_point_comm_explicit P ε S p₁
  have hK₂ := _root_.MIPStarRE.QPBT.ProjectiveSetting.exp_point_comm_explicit P ε S p₂
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq at hK₁ hK₂
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.sandwichDefectBound
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul, _root_.LIDT.MIPStarRE.LDT.avgOver_add,
    _root_.LIDT.MIPStarRE.LDT.avgOver_add]
  have hs : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  nlinarith [hZ, hX, hK₁, hK₂, hs, hε, hC₁, hC₂]
