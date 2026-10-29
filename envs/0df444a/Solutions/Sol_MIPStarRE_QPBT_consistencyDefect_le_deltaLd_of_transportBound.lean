-- Prove2me | solution 1 for MIPStarRE.QPBT.consistencyDefect_le_deltaLd_of_transportBound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:10:09.403944+00:00
-- url     : https://prove2.me/submissions/f2247210-4cfd-47dc-929a-58a5137e4908

-- Generated proof for MIPStarRE.QPBT.consistencyDefect_le_deltaLd_of_transportBound.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Error
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_heteroKron_le_one
import Theorems.Thm_MIPStarRE_QPBT_one_le_deltaLd_of_one_le_error

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Soundness for the directly indexed low-degree game

This module proves the quantum soundness statement for the directly indexed
low-degree game, in the form used by the Chapter 15 combining argument: the
polynomial-tuple measurements of `prop:ld-simultaneous-general-k` satisfy the
three consistency relations of `lem:ld-soundness` with the error function
`deltaLd` at the parameters `(q, m, d, k)` of the game.

In the regime `0 < ε ≤ 1` the error carried by
`prop:ld-simultaneous-general-k` — the error of `thm:main-formal` at the
combined parameters of `def:ld-combining-parameters` together with the recovery
loss `(m + k) d / q` — is absorbed into `deltaLd` at the universal constants
`a = 10^23` and `b = 1/80000` by
`exists_directCombinedTransportConstants`.  In the regime `1 ≤ ε` the error
function is at least one, while every bipartite consistency defect on a unit
state is at most one, so the conclusion carries no information there.

## Main statements

* `exists_direct_ld_soundness` — quantum soundness of the directly indexed
  low-degree game, with the error function `deltaLd`.
* `exists_direct_ld_soundness_of_k_eq_one` retains the one-coordinate proof
  used by the seed-indexed soundness transport.

## References

The obligation supports the Chapter 15 combining argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1288`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum





/-! ## Absorbing the error bound from the low individual degree theorem

The specializations below combine three inputs: polynomial-tuple conclusions
whose error is built from `mainFormalError`, the error bound of
`thm:main-formal` at the auxiliary sampling parameter; the absorption
`exists_directLdTransportConstants` of that error into `deltaLd`; and the
coarse bound `consistencyDefect_heteroKron_le_one`, which closes both the
regime `1 ≤ ε` and the regime where the transport argument exceeds one, in
each of which `deltaLd` is already at least one. -/

theorem solution
    {a b C₀ : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (hC₀ : 1 ≤ C₀)
    (habs : ∀ (D : _root_.MIPStarRE.QPBT.DirectLdParams) (ε : ℝ), 0 < ε → ε ≤ 1 →
      C₀ * (D.k : ℝ) *
          Real.sqrt
            (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
              ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) ≤
        _root_.MIPStarRE.QPBT.deltaLd a b ε D.q D.m D.d D.k)
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (ε : ℝ) (hε : 0 < ε)
    {X α ιA ιB : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (hμ : μ.IsProbability)
    (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (hbound : ε ≤ 1 →
      _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
            ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε ≤ 1 →
        _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x c => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect c) 1)
            (fun x c => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect c)) ψ ≤
          C₀ *
            Real.sqrt
              (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
                ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε)) :
    _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x c => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect c) 1)
        (fun x c => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect c)) ψ ≤
      _root_.MIPStarRE.QPBT.deltaLd a b ε D.q D.m D.d D.k := by
  have hle1 : _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x c => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect c) 1)
      (fun x c => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect c)) ψ ≤ 1 :=
    _root_.MIPStarRE.QPBT.consistencyDefect_heteroKron_le_one μ hμ A B ψ hψ
  rcases le_or_gt ε 1 with hε1 | hε1
  · have hk : (1 : ℝ) ≤ (D.k : ℝ) := by exact_mod_cast D.hk
    have hsqrtnn : (0 : ℝ) ≤
        Real.sqrt
          (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
            ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := Real.sqrt_nonneg _
    have hstep : _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x c => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect c) 1)
        (fun x c => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect c)) ψ ≤
        C₀ *
          Real.sqrt
            (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
              ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := by
      rcases le_or_gt
          (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
            ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) 1 with hT1 | hT1
      · exact hbound hε1 hT1
      · have hone : (1 : ℝ) ≤
            Real.sqrt
              (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
                ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := by
          calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
            _ ≤ _ := Real.sqrt_le_sqrt hT1.le
        nlinarith [mul_nonneg (sub_nonneg.mpr hC₀) (sub_nonneg.mpr hone)]
    calc _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x c => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect c) 1)
          (fun x c => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect c)) ψ
        ≤ C₀ *
            Real.sqrt
              (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
                ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) := hstep
      _ ≤ C₀ * (D.k : ℝ) *
            Real.sqrt
              (_root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.toLDTParameters (_root_.MIPStarRE.QPBT.directLdAuxParameter D) (3 * ε) +
                ((D.m : ℝ) * (D.d : ℝ)) / (D.q : ℝ) + ε) :=
          mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right (by linarith) hk) hsqrtnn
      _ ≤ _root_.MIPStarRE.QPBT.deltaLd a b ε D.q D.m D.d D.k := habs D ε hε hε1
  · have hone : (1 : ℝ) ≤ _root_.MIPStarRE.QPBT.deltaLd a b ε D.q D.m D.d D.k :=
      _root_.MIPStarRE.QPBT.one_le_deltaLd_of_one_le_error ha hb.le hε1.le D.hm D.hd D.hk
    linarith
