-- Prove2me | solution 1 for MIPStarRE.QPBT.direct_ld_transport_constants_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:25:06.47493+00:00
-- url     : https://prove2.me/submissions/54e5aaa4-61e2-4434-a3c5-65444a602121

-- Generated proof for MIPStarRE.QPBT.direct_ld_transport_constants_explicit.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Error
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_sqrt_rpow_one_div

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Error.lean. -/
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

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

/-! ## The auxiliary sampling parameter -/







/-! ## Elementary positivity of the parameters

The four lemmas below are formalization-only conveniences: they record the
positivity fields of `DirectLdParams` in the real numbers, where all the
scalar estimates of this module take place. -/

private theorem directLd_one_le_m (D : _root_.MIPStarRE.QPBT.DirectLdParams) : (1 : ℝ) ≤ (D.m : ℝ) := by
  have h : 1 ≤ D.m := D.hm
  exact_mod_cast h

private theorem directLd_one_le_d (D : _root_.MIPStarRE.QPBT.DirectLdParams) : (1 : ℝ) ≤ (D.d : ℝ) := by
  have h : 1 ≤ D.d := D.hd
  exact_mod_cast h

private theorem directLd_one_le_k (D : _root_.MIPStarRE.QPBT.DirectLdParams) : (1 : ℝ) ≤ (D.k : ℝ) := by
  have h : 1 ≤ D.k := D.hk
  exact_mod_cast h

private theorem directLd_one_le_q (D : _root_.MIPStarRE.QPBT.DirectLdParams) : (1 : ℝ) ≤ (D.q : ℝ) := by
  have h : 1 ≤ D.q := D.toLDTParameters.hq
  exact_mod_cast h

/-! ## The three terms of the LDT error -/

/-- With the auxiliary sampling parameter the exponential scale of
`mainFormalError` collapses: the argument of its exponential term is exactly
`m d`.

Formalization-only scalar identity for the error function displayed in
`MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/Definitions.lean:28-36`. -/
theorem directLdAuxParameter_exp_arg (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    (_root_.MIPStarRE.QPBT.directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ))) =
      (D.m : ℝ) * (D.d : ℝ) := by
  have hm : (0 : ℝ) < (D.m : ℝ) := lt_of_lt_of_le zero_lt_one (directLd_one_le_m D)
  have hpow : (0 : ℝ) < (D.m : ℝ) ^ (2 : ℕ) := pow_pos hm 2
  have hne : (2560000 : ℝ) * ((D.m : ℝ) ^ (2 : ℕ)) ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) hpow)
  unfold _root_.MIPStarRE.QPBT.directLdAuxParameter
  push_cast
  rw [div_eq_iff hne]
  ring







/-! ## The transport envelope

The three scalar quantities `ε^b`, `q^(-b)` and `2^(-b m d)` at the transport
exponent `b = 1/80000` are the inner factor of `deltaLd`; the abbreviation
below names their sum. -/



theorem transportEnvelope_rpow_eps_le (D : _root_.MIPStarRE.QPBT.DirectLdParams) (ε : ℝ) :
    Real.rpow ε (1 / 80000) ≤ _root_.MIPStarRE.QPBT.transportEnvelope D ε := by
  have hy : (0 : ℝ) ≤ Real.rpow (D.q : ℝ) (-(1 / 80000)) :=
    Real.rpow_nonneg (by positivity) _
  have hz : (0 : ℝ) ≤ Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  unfold _root_.MIPStarRE.QPBT.transportEnvelope
  linarith

theorem transportEnvelope_rpow_q_le (D : _root_.MIPStarRE.QPBT.DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) :
    Real.rpow (D.q : ℝ) (-(1 / 80000)) ≤ _root_.MIPStarRE.QPBT.transportEnvelope D ε := by
  have hx : (0 : ℝ) ≤ Real.rpow ε (1 / 80000) := Real.rpow_nonneg hε _
  have hz : (0 : ℝ) ≤ Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  unfold _root_.MIPStarRE.QPBT.transportEnvelope
  linarith

theorem transportEnvelope_nonneg (D : _root_.MIPStarRE.QPBT.DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ _root_.MIPStarRE.QPBT.transportEnvelope D ε := by
  have hx : (0 : ℝ) ≤ Real.rpow ε (1 / 80000) := Real.rpow_nonneg hε _
  exact le_trans hx (_root_.MIPStarRE.QPBT.transportEnvelope_rpow_eps_le D ε)

/-! ## The LDT error at the auxiliary sampling parameter -/

/-- The LDT error at the auxiliary sampling parameter, written out in the
parameters of the directly indexed game. -/
private theorem mainFormalError_direct_eq (D : _root_.MIPStarRE.QPBT.DirectLdParams) (ε : ℝ) :
    _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) =
      100000 * ((_root_.MIPStarRE.QPBT.directLdAuxParameter D : ℝ) ^ (2 : ℕ)) * ((D.m : ℝ) ^ (4 : ℕ)) *
        (Real.rpow (3 * ε) (1 / 40000) +
          Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) +
          Real.exp (-((_root_.MIPStarRE.QPBT.directLdAuxParameter D : ℝ) /
            (2560000 * ((D.m : ℝ) ^ (2 : ℕ)))))) := rfl

private theorem directLdEnvelope_nonneg (D : _root_.MIPStarRE.QPBT.DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ Real.rpow (3 * ε) (1 / 40000) +
      Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) +
      Real.exp (-((_root_.MIPStarRE.QPBT.directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ))))) := by
  have h1 : (0 : ℝ) ≤ Real.rpow (3 * ε) (1 / 40000) := Real.rpow_nonneg (by linarith) _
  have h2 : (0 : ℝ) ≤ Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) :=
    Real.rpow_nonneg (by positivity) _
  have h3 : (0 : ℝ) ≤
      Real.exp (-((_root_.MIPStarRE.QPBT.directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ))))) :=
    (Real.exp_pos _).le
  linarith

private theorem mainFormalError_direct_nonneg (D : _root_.MIPStarRE.QPBT.DirectLdParams) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) := by
  rw [mainFormalError_direct_eq]
  exact mul_nonneg (by positivity) (directLdEnvelope_nonneg D hε)

/-- The square root of the polynomial prefactor of the LDT error at the
auxiliary sampling parameter. -/
private theorem sqrt_directLdPrefactor_le (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    Real.sqrt (100000 * ((_root_.MIPStarRE.QPBT.directLdAuxParameter D : ℝ) ^ (2 : ℕ)) * ((D.m : ℝ) ^ (4 : ℕ))) ≤
      820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) := by
  have hm1 := directLd_one_le_m D
  have hd1 := directLd_one_le_d D
  have hK : (_root_.MIPStarRE.QPBT.directLdAuxParameter D : ℝ) = 2560000 * (D.m : ℝ) ^ (3 : ℕ) * (D.d : ℝ) := by
    unfold _root_.MIPStarRE.QPBT.directLdAuxParameter
    push_cast
    ring
  have hX : (0 : ℝ) ≤ (D.m : ℝ) ^ (10 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) := by positivity
  have hC : (0 : ℝ) ≤ 820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) := by positivity
  have hlhs : 100000 * ((_root_.MIPStarRE.QPBT.directLdAuxParameter D : ℝ) ^ (2 : ℕ)) * ((D.m : ℝ) ^ (4 : ℕ)) =
      655360000000000000 * ((D.m : ℝ) ^ (10 : ℕ) * (D.d : ℝ) ^ (2 : ℕ)) := by
    rw [hK]; ring
  have hrhs : (820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ)) ^ (2 : ℕ) =
      672400000000000000 * ((D.m : ℝ) ^ (10 : ℕ) * (D.d : ℝ) ^ (2 : ℕ)) := by ring
  calc Real.sqrt (100000 * ((_root_.MIPStarRE.QPBT.directLdAuxParameter D : ℝ) ^ (2 : ℕ)) * ((D.m : ℝ) ^ (4 : ℕ)))
      ≤ Real.sqrt ((820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ)) ^ (2 : ℕ)) := by
        apply Real.sqrt_le_sqrt
        rw [hlhs, hrhs]
        exact mul_le_mul_of_nonneg_right (by norm_num) hX
    _ = 820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) := Real.sqrt_sq hC

/-- Halving the exponents: the square root of the LDT envelope at the
auxiliary sampling parameter is at most `3 d` times the transport envelope. -/
private theorem sqrt_directLdEnvelope_le (D : _root_.MIPStarRE.QPBT.DirectLdParams) {ε : ℝ} (hε0 : 0 < ε) :
    Real.sqrt (Real.rpow (3 * ε) (1 / 40000) +
        Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) +
        Real.exp (-((_root_.MIPStarRE.QPBT.directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ)))))) ≤
      3 * (D.d : ℝ) * _root_.MIPStarRE.QPBT.transportEnvelope D ε := by
  have hd1 := directLd_one_le_d D
  have hq1 := directLd_one_le_q D
  have h1n : (0 : ℝ) ≤ Real.rpow (3 * ε) (1 / 40000) := Real.rpow_nonneg (by linarith) _
  have h2n : (0 : ℝ) ≤ Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) :=
    Real.rpow_nonneg (by positivity) _
  have h3n : (0 : ℝ) ≤
      Real.exp (-((_root_.MIPStarRE.QPBT.directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ))))) :=
    (Real.exp_pos _).le
  have hb1 : Real.sqrt (Real.rpow (3 * ε) (1 / 40000)) ≤ 3 * Real.rpow ε (1 / 80000) := by
    have e : Real.sqrt (Real.rpow (3 * ε) (1 / 40000)) = Real.rpow (3 * ε) (1 / 80000) := by
      rw [_root_.LIDT.MIPStarRE.LDT.Test.sqrt_rpow_one_div (by linarith : (0 : ℝ) ≤ 3 * ε)
        (by norm_num : (0 : ℝ) < 40000)]
      norm_num
    rw [e]
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow (by norm_num) hε0.le]
    have h3 : (3 : ℝ) ^ ((1 : ℝ) / 80000) ≤ 3 := by
      calc (3 : ℝ) ^ ((1 : ℝ) / 80000) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := Real.rpow_one 3
    exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hε0.le _)
  have hb2 : Real.sqrt (Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000)) ≤
      (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 80000)) := by
    have e : Real.sqrt (Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000)) =
        Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 80000) := by
      rw [_root_.LIDT.MIPStarRE.LDT.Test.sqrt_rpow_one_div (by positivity : (0 : ℝ) ≤ (D.d : ℝ) / (D.q : ℝ))
        (by norm_num : (0 : ℝ) < 40000)]
      norm_num
    rw [e]
    simp only [Real.rpow_eq_pow]
    rw [Real.div_rpow (by linarith) (by linarith), div_eq_mul_inv,
      ← Real.rpow_neg (by linarith : (0 : ℝ) ≤ (D.q : ℝ))]
    have hd : (D.d : ℝ) ^ ((1 : ℝ) / 80000) ≤ (D.d : ℝ) := by
      calc (D.d : ℝ) ^ ((1 : ℝ) / 80000) ≤ (D.d : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
        _ = (D.d : ℝ) := Real.rpow_one _
    exact mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (by linarith) _)
  have hb3 : Real.sqrt
      (Real.exp (-((_root_.MIPStarRE.QPBT.directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ)))))) ≤
      Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) := by
    have hlog : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hmd : (0 : ℝ) ≤ (D.m : ℝ) * (D.d : ℝ) := by positivity
    have hcast : ((D.m * D.d : ℕ) : ℝ) = (D.m : ℝ) * (D.d : ℝ) := by push_cast; ring
    rw [_root_.MIPStarRE.QPBT.directLdAuxParameter_exp_arg D, ← Real.exp_half, hcast]
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hlog hmd]
  have hx := Real.rpow_nonneg hε0.le (1 / 80000 : ℝ)
  have hy := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (D.q : ℝ)) (-(1 / 80000) : ℝ)
  have hz := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
    (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ)))
  have p1 : (0 : ℝ) ≤ ((D.d : ℝ) - 1) * Real.rpow ε (1 / 80000) :=
    mul_nonneg (by linarith) hx
  have p2 : (0 : ℝ) ≤ (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 80000)) :=
    mul_nonneg (by linarith) hy
  have p3 : (0 : ℝ) ≤ (3 * (D.d : ℝ) - 1) *
      Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) := mul_nonneg (by linarith) hz
  calc Real.sqrt (Real.rpow (3 * ε) (1 / 40000) +
        Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000) +
        Real.exp (-((_root_.MIPStarRE.QPBT.directLdAuxParameter D : ℝ) / (2560000 * ((D.m : ℝ) ^ (2 : ℕ))))))
      ≤ Real.sqrt (Real.rpow (3 * ε) (1 / 40000)) +
          Real.sqrt (Real.rpow ((D.d : ℝ) / (D.q : ℝ)) (1 / 40000)) +
          Real.sqrt
            (Real.exp (-((_root_.MIPStarRE.QPBT.directLdAuxParameter D : ℝ) /
              (2560000 * ((D.m : ℝ) ^ (2 : ℕ)))))) :=
        _root_.LIDT.MIPStarRE.LDT.sqrt_add3_le_add3_sqrt h1n h2n h3n
    _ ≤ 3 * Real.rpow ε (1 / 80000) + (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 80000)) +
          Real.rpow 2 (-((1 / 80000) * ((D.m * D.d : ℕ) : ℝ))) := by
        linarith
    _ ≤ 3 * (D.d : ℝ) * _root_.MIPStarRE.QPBT.transportEnvelope D ε := by
        unfold _root_.MIPStarRE.QPBT.transportEnvelope
        nlinarith [p1, p2, p3]

/-- The square root of the whole scalar error of the transport, bounded by an
explicit polynomial in the parameters times the transport envelope. -/
private theorem sqrt_directLdTransportError_le (D : _root_.MIPStarRE.QPBT.DirectLdParams) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
        ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) ≤
      2500000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) * _root_.MIPStarRE.QPBT.transportEnvelope D ε := by
  have hm1 := directLd_one_le_m D
  have hd1 := directLd_one_le_d D
  have hq1 := directLd_one_le_q D
  have hT := _root_.MIPStarRE.QPBT.transportEnvelope_nonneg D hε0.le
  have hE := mainFormalError_direct_nonneg D hε0.le
  have hmdq : (0 : ℝ) ≤ ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) := by positivity
  have hsE : Real.sqrt
      (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε)) ≤
      820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) *
        (3 * (D.d : ℝ) * _root_.MIPStarRE.QPBT.transportEnvelope D ε) := by
    rw [mainFormalError_direct_eq, Real.sqrt_mul (by positivity)]
    exact mul_le_mul (sqrt_directLdPrefactor_le D) (sqrt_directLdEnvelope_le D hε0)
      (Real.sqrt_nonneg _) (by positivity)
  have hsmd : Real.sqrt (((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ)) ≤
      (D.m : ℝ) * (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 80000)) := by
    have hmd1 : (1 : ℝ) ≤ (D.m : ℝ) * (D.d : ℝ) := by nlinarith
    simp only [Real.rpow_eq_pow]
    rw [Real.sqrt_eq_rpow, Real.div_rpow (by linarith) (by linarith), div_eq_mul_inv,
      ← Real.rpow_neg (by linarith : (0 : ℝ) ≤ (D.q : ℝ))]
    have h1 : ((D.m : ℝ) * (D.d : ℝ)) ^ ((1 : ℝ) / 2) ≤ (D.m : ℝ) * (D.d : ℝ) := by
      calc ((D.m : ℝ) * (D.d : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ ((D.m : ℝ) * (D.d : ℝ)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hmd1 (by norm_num)
        _ = (D.m : ℝ) * (D.d : ℝ) := Real.rpow_one _
    have h2 : (D.q : ℝ) ^ (-((1 : ℝ) / 2)) ≤ (D.q : ℝ) ^ (-((1 : ℝ) / 80000)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
    exact mul_le_mul h1 h2 (Real.rpow_nonneg (by linarith) _) (by nlinarith)
  have hsε : Real.sqrt ε ≤ Real.rpow ε (1 / 80000) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)
  have hqT : (D.m : ℝ) * (D.d : ℝ) * Real.rpow (D.q : ℝ) (-(1 / 80000)) ≤
      (D.m : ℝ) * (D.d : ℝ) * _root_.MIPStarRE.QPBT.transportEnvelope D ε :=
    mul_le_mul_of_nonneg_left (_root_.MIPStarRE.QPBT.transportEnvelope_rpow_q_le D hε0.le) (by positivity)
  have hεT : Real.rpow ε (1 / 80000) ≤ 1 * _root_.MIPStarRE.QPBT.transportEnvelope D ε := by
    rw [one_mul]
    exact _root_.MIPStarRE.QPBT.transportEnvelope_rpow_eps_le D ε
  have hP : (D.m : ℝ) * (D.d : ℝ) ≤ (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) := by
    have e1 : (D.m : ℝ) ≤ (D.m : ℝ) ^ (5 : ℕ) := by
      simpa using pow_le_pow_right₀ hm1 (by norm_num : 1 ≤ 5)
    have e2 : (D.d : ℝ) ≤ (D.d : ℝ) ^ (2 : ℕ) := by
      simpa using pow_le_pow_right₀ hd1 (by norm_num : 1 ≤ 2)
    exact mul_le_mul e1 e2 (by linarith) (by positivity)
  have hP1 : (1 : ℝ) ≤ (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) := by
    have e1 : (1 : ℝ) ≤ (D.m : ℝ) ^ (5 : ℕ) := one_le_pow₀ hm1
    have e2 : (1 : ℝ) ≤ (D.d : ℝ) ^ (2 : ℕ) := one_le_pow₀ hd1
    nlinarith
  have hcoef : 2460000000 * ((D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ)) +
      (D.m : ℝ) * (D.d : ℝ) + 1 ≤
      2500000000 * ((D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ)) := by linarith
  have hkey : 820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) *
        (3 * (D.d : ℝ) * _root_.MIPStarRE.QPBT.transportEnvelope D ε) +
      (D.m : ℝ) * (D.d : ℝ) * _root_.MIPStarRE.QPBT.transportEnvelope D ε + 1 * _root_.MIPStarRE.QPBT.transportEnvelope D ε ≤
      2500000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) * _root_.MIPStarRE.QPBT.transportEnvelope D ε := by
    nlinarith [mul_le_mul_of_nonneg_right hcoef hT]
  calc Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
        ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε)
      ≤ Real.sqrt
            (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε)) +
          Real.sqrt (((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ)) + Real.sqrt ε :=
        _root_.LIDT.MIPStarRE.LDT.sqrt_add3_le_add3_sqrt hE hmdq hε0.le
    _ ≤ 820000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) *
            (3 * (D.d : ℝ) * _root_.MIPStarRE.QPBT.transportEnvelope D ε) +
          (D.m : ℝ) * (D.d : ℝ) * _root_.MIPStarRE.QPBT.transportEnvelope D ε + 1 * _root_.MIPStarRE.QPBT.transportEnvelope D ε := by
        linarith
    _ ≤ 2500000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) * _root_.MIPStarRE.QPBT.transportEnvelope D ε :=
        hkey

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

theorem solution (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    1 ≤ 2500000000 * C₀ ∧ 0 < (1 / 80000 : ℝ) ∧ (1 / 80000 : ℝ) ≤ 1 ∧
      ∀ (D : _root_.MIPStarRE.QPBT.DirectLdParams) (ε : ℝ), 0 < ε → ε ≤ 1 →
        C₀ * (D.k : ℝ) *
            Real.sqrt
              (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
                ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) ≤
          _root_.MIPStarRE.QPBT.deltaLd (2500000000 * C₀) (1 / 80000) ε D.q D.m D.d D.k := by
  refine ⟨by linarith, by norm_num, by norm_num, ?_⟩
  intro D ε hε0 hε1
  have hm1 := directLd_one_le_m D
  have hd1 := directLd_one_le_d D
  have hk1 := directLd_one_le_k D
  have hT := _root_.MIPStarRE.QPBT.transportEnvelope_nonneg D hε0.le
  have hdelta : _root_.MIPStarRE.QPBT.deltaLd (2500000000 * C₀) (1 / 80000) ε D.q D.m D.d D.k =
      2500000000 * C₀ * Real.rpow ((D.d * D.m * D.k : ℕ) : ℝ) (2500000000 * C₀) *
        _root_.MIPStarRE.QPBT.transportEnvelope D ε := rfl
  have hbase : (1 : ℝ) ≤ ((D.d * D.m * D.k : ℕ) : ℝ) := by
    have hn : 1 ≤ D.d * D.m * D.k := Nat.mul_pos (Nat.mul_pos D.hd D.hm) D.hk
    exact_mod_cast hn
  have hpow : ((D.d * D.m * D.k : ℕ) : ℝ) ^ (8 : ℕ) ≤
      Real.rpow ((D.d * D.m * D.k : ℕ) : ℝ) (2500000000 * C₀) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast (((D.d * D.m * D.k : ℕ) : ℝ)) 8]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by push_cast; linarith)
  have hmono : (D.k : ℝ) * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) ≤
      ((D.d * D.m * D.k : ℕ) : ℝ) ^ (8 : ℕ) := by
    have e1 : (D.k : ℝ) ≤ (D.k : ℝ) ^ (8 : ℕ) := by
      simpa using pow_le_pow_right₀ hk1 (by norm_num : 1 ≤ 8)
    have e2 : (D.m : ℝ) ^ (5 : ℕ) ≤ (D.m : ℝ) ^ (8 : ℕ) :=
      pow_le_pow_right₀ hm1 (by norm_num)
    have e3 : (D.d : ℝ) ^ (2 : ℕ) ≤ (D.d : ℝ) ^ (8 : ℕ) :=
      pow_le_pow_right₀ hd1 (by norm_num)
    push_cast
    calc (D.k : ℝ) * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ)
        ≤ (D.k : ℝ) ^ (8 : ℕ) * (D.m : ℝ) ^ (8 : ℕ) * (D.d : ℝ) ^ (8 : ℕ) :=
          mul_le_mul (mul_le_mul e1 e2 (by positivity) (by positivity)) e3
            (by positivity) (by positivity)
      _ = ((D.d : ℝ) * (D.m : ℝ) * (D.k : ℝ)) ^ (8 : ℕ) := by ring
  have hstep := sqrt_directLdTransportError_le D hε0 hε1
  rw [hdelta]
  calc C₀ * (D.k : ℝ) *
        Real.sqrt (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
          ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε)
      ≤ C₀ * (D.k : ℝ) *
          (2500000000 * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ) *
            _root_.MIPStarRE.QPBT.transportEnvelope D ε) :=
        mul_le_mul_of_nonneg_left hstep (mul_nonneg (by linarith) (by positivity))
    _ = 2500000000 * C₀ *
          ((D.k : ℝ) * (D.m : ℝ) ^ (5 : ℕ) * (D.d : ℝ) ^ (2 : ℕ)) *
          _root_.MIPStarRE.QPBT.transportEnvelope D ε := by ring
    _ ≤ 2500000000 * C₀ *
          Real.rpow ((D.d * D.m * D.k : ℕ) : ℝ) (2500000000 * C₀) *
          _root_.MIPStarRE.QPBT.transportEnvelope D ε := by
        apply mul_le_mul_of_nonneg_right _ hT
        exact mul_le_mul_of_nonneg_left (le_trans hmono hpow) (by linarith)
