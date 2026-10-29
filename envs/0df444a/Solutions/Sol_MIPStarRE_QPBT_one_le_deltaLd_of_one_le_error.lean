-- Prove2me | solution 1 for MIPStarRE.QPBT.one_le_deltaLd_of_one_le_error
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:25:06.437872+00:00
-- url     : https://prove2.me/submissions/e0c5c4b3-d302-4e5c-b117-108aa4ac3b55

-- Generated proof for MIPStarRE.QPBT.one_le_deltaLd_of_one_le_error.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
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
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib

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

theorem solution {a b ε : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b)
    (hε : 1 ≤ ε) {q m d k : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (hk : 1 ≤ k) :
    1 ≤ _root_.MIPStarRE.QPBT.deltaLd a b ε q m d k := by
  have hbase : (1 : ℝ) ≤ ((d * m * k : ℕ) : ℝ) := by
    have hn : 1 ≤ d * m * k := Nat.mul_pos (Nat.mul_pos hd hm) hk
    exact_mod_cast hn
  have hX : (1 : ℝ) ≤ Real.rpow ((d * m * k : ℕ) : ℝ) a := by
    simp only [Real.rpow_eq_pow]
    calc (1 : ℝ) = (1 : ℝ) ^ a := (Real.one_rpow a).symm
      _ ≤ ((d * m * k : ℕ) : ℝ) ^ a := Real.rpow_le_rpow (by norm_num) hbase (by linarith)
  have hY : (1 : ℝ) ≤ Real.rpow ε b := by
    simp only [Real.rpow_eq_pow]
    calc (1 : ℝ) = (1 : ℝ) ^ b := (Real.one_rpow b).symm
      _ ≤ ε ^ b := Real.rpow_le_rpow (by norm_num) hε hb
  have hZ : (0 : ℝ) ≤ Real.rpow (q : ℝ) (-b) := Real.rpow_nonneg (by positivity) _
  have hW : (0 : ℝ) ≤ Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hax : (1 : ℝ) ≤ a * Real.rpow ((d * m * k : ℕ) : ℝ) a := by nlinarith
  have hsum : (1 : ℝ) ≤ Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))) := by linarith
  unfold _root_.MIPStarRE.QPBT.deltaLd
  calc (1 : ℝ) = 1 * 1 := by norm_num
    _ ≤ a * Real.rpow ((d * m * k : ℕ) : ℝ) a *
        (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
          Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ)))) :=
      mul_le_mul hax hsum (by norm_num) (by linarith)
