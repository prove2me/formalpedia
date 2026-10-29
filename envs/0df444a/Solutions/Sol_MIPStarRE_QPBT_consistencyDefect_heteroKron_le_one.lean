-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_heteroKron_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:06:37.04812+00:00
-- url     : https://prove2.me/submissions/182f335b-5583-473b-9d01-27902a31a6c2

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_heteroKron_le_one.
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
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_consistencyDefect_eq_one_sub_overlap

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# The scalar error of the low-degree soundness transport

This module supplies the scalar half of the soundness transport for the
directly indexed low-degree game.  Its content is purely arithmetic: the
auxiliary sampling parameter with which the low individual degree theorem is
applied to a coordinate strategy, the resulting bounds on the three terms of
the LDT error `mainFormalError`, and the absorption of the
simultaneous-measurement estimate into the error function `deltaLd` of
`lem:ld-soundness`.

## Main definitions

* `directLdAuxParameter D = 2560000 m³ d` is the sampling parameter handed to
  `MIPStarRE.LDT.Test.mainFormal`.  It is the multiple of the exponential scale
  `2560000 m²` of `mainFormalError` with quotient `m d`, so that the
  exponential term of the LDT error is exactly `exp (-m d)`.

## Main results

* `directLdAuxParameter_pos` and `four_hundred_mul_le_directLdAuxParameter` are
  the two hypotheses `0 < k` and `400 m d ≤ k` of `mainFormal`, proved from the
  positivity of the dimension and of the degree alone.
* `directLd_test_term_le`, `directLd_field_term_le` and
  `directLd_exponential_term_le` bound the three terms of
  `mainFormalError D.toLDTParameters (directLdAuxParameter D) (3 ε)`: the test
  term by `3 ε^(1/40000)`, the field term by `d q^(-1/40000)`, and the
  exponential term by `2^(-b m d)` for every `0 ≤ b ≤ 1`.
* `exists_directLdTransportConstants` exhibits, for a sandwich constant
  `C₀ ≥ 1`, the explicit universal constants `a = 2500000000 C₀` and
  `b = 1/80000` for which `C₀ k √(mainFormalError + m d / q + ε)` is at most
  `deltaLd a b ε q m d k` in the regime `0 < ε ≤ 1`.
* `one_le_deltaLd_of_one_le_error` and
  `one_le_deltaLd_of_fieldSize_le_degree` bound `deltaLd` below by one in the
  two degenerate regimes `1 ≤ ε` and `q ≤ d`, and
  `consistencyDefect_heteroKron_le_one` bounds every bipartite consistency
  defect on a unit state above by one.  Together they close both degenerate
  regimes, where the conclusion of `lem:ld-soundness` carries no information.

The exponent `b = 1/80000` is half the exponent `1/40000` carried by
`mainFormalError`; the halving is exactly what the square root of the
simultaneous-measurement estimate costs.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:139-167`
* `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean:288-327`
* `MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean:28-36`
* `references/ldt-paper/test_definition.tex:180-202`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

/-! ## The auxiliary sampling parameter -/







/-! ## Elementary positivity of the parameters

The four lemmas below are formalization-only conveniences: they record the
positivity fields of `DirectLdParams` in the real numbers, where all the
scalar estimates of this module take place. -/









/-! ## The three terms of the LDT error -/









/-! ## The transport envelope

The three scalar quantities `ε^b`, `q^(-b)` and `2^(-b m d)` at the transport
exponent `b = 1/80000` are the inner factor of `deltaLd`; the abbreviation
below names their sum. -/









/-! ## The LDT error at the auxiliary sampling parameter -/













/-! ## Absorption into the error function of `lem:ld-soundness` -/





/-! ## The degenerate regimes

In the two regimes `1 ≤ ε` and `q ≤ d` the error function `deltaLd` is at
least one, so the consistency conclusions of `lem:ld-soundness` hold for any
witnesses; the low-degree test carries no information there. -/





/-! ## A coarse universal bound on the consistency defect

The consistency defect compared with `deltaLd` in `lem:ld-soundness` is the
off-diagonal Born mass of a pair of measurement families acting on the two
tensor factors of a unit bipartite state.  Since the joint Born weights are
nonnegative and sum to one, that mass is at most one; combined with the two
lower bounds on `deltaLd` above this closes the regimes `1 ≤ ε` and `q ≤ d`.

The theorem below is formalization-only.  It is a generic statement about
`consistencyDefect` rather than about the low-degree game, and would naturally
live in `MIPStarRE/QPBT/Games/DistanceTheorems.lean`. -/

theorem solution {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (hμ : μ.IsProbability)
    (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1) :
    _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ ≤ 1 := by
  have hEq : _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
      (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ =
      1 - _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a : α,
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
          (_root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1 * _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a))) :=
    _root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ
      (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (A x))
      (fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (B x))
      ψ hμ hψ
  have hnn : 0 ≤ _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a : α,
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1 * _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a))) := by
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg μ _ (fun x => Finset.sum_nonneg (fun a _ => ?_))
    have hprod : _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) *
        _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) ((B x).effect a) =
        _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) ((B x).effect a) := by
      change Matrix.kroneckerMap (fun x1 x2 => x1 * x2) ((A x).effect a)
            (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) *
          Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA)
            ((B x).effect a) =
          Matrix.kroneckerMap (fun x1 x2 => x1 * x2) ((A x).effect a)
            ((B x).effect a)
      rw [← Matrix.mul_kronecker_mul, mul_one, one_mul]
    rw [hprod]
    unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm _root_.MIPStarRE.QPBT.applyOperatorToState _root_.MIPStarRE.QPBT.heteroKron
    exact
      (Matrix.isPositive_toEuclideanLin_iff.mpr
        (Matrix.nonneg_iff_posSemidef.mp
          (_root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg ((A x).pos a) ((B x).pos a)))).re_inner_nonneg_right ψ
  rw [hEq]
  linarith
