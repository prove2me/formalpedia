-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_direct_ld_soundness
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:08:27.549393+00:00
-- url     : https://prove2.me/submissions/77962da1-52a7-4215-a6f2-644cdbeb8dd4

-- Generated proof for MIPStarRE.QPBT.exists_direct_ld_soundness.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Parameters
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Error
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_heteroKron_le_one
import Theorems.Thm_MIPStarRE_QPBT_exists_directCombinedTransportConstants
import Theorems.Thm_MIPStarRE_QPBT_exists_directSimultaneousPolynomialMeasurements_combinedError
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

theorem solution :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (D : _root_.MIPStarRE.QPBT.DirectLdParams) (ε : ℝ), 0 < ε →
        ∀ S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D), S.IsProjective → 1 - ε ≤ S.value →
          ∃ GA : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιA,
            ∃ GB : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιB,
              _root_.MIPStarRE.QPBT.consistencyDefect
                  (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
                  (fun u outcome =>
                    _root_.MIPStarRE.QPBT.heteroKron
                      (((S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                        (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome) 1)
                  (fun u outcome =>
                    _root_.MIPStarRE.QPBT.heteroKron 1
                      ((GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome))
                  S.ψ ≤ _root_.MIPStarRE.QPBT.deltaLd a b ε D.q D.m D.d D.k ∧
              _root_.MIPStarRE.QPBT.consistencyDefect
                  (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
                  (fun u outcome =>
                    _root_.MIPStarRE.QPBT.heteroKron
                      ((GA.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome) 1)
                  (fun u outcome =>
                    _root_.MIPStarRE.QPBT.heteroKron 1
                      (((S.B (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                        (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome))
                  S.ψ ≤ _root_.MIPStarRE.QPBT.deltaLd a b ε D.q D.m D.d D.k ∧
              _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
                  (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (GA.effect g) 1)
                  (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (GB.effect g))
                  S.ψ ≤ _root_.MIPStarRE.QPBT.deltaLd a b ε D.q D.m D.d D.k := by
  obtain ⟨a, b, ha, hb0, hb1, habs⟩ := _root_.MIPStarRE.QPBT.exists_directCombinedTransportConstants
  refine ⟨a, b, ha, hb0, hb1, ?_⟩
  intro D ε hε S hS hwin
  obtain ⟨GA, GB, h1, h2, h3⟩ :=
    _root_.MIPStarRE.QPBT.exists_directSimultaneousPolynomialMeasurements_combinedError D S hS ε hwin
  refine ⟨GA, GB, ?_, ?_, ?_⟩
  all_goals by_cases hε1 : ε ≤ 1
  · exact le_trans h1 (habs D ε hε hε1)
  · exact le_trans
      (_root_.MIPStarRE.QPBT.consistencyDefect_heteroKron_le_one _ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) _ _
        S.ψ S.ψ_norm)
      (_root_.MIPStarRE.QPBT.one_le_deltaLd_of_one_le_error ha hb0.le (not_le.mp hε1).le D.hm D.hd D.hk)
  · exact le_trans h2 (habs D ε hε hε1)
  · exact le_trans
      (_root_.MIPStarRE.QPBT.consistencyDefect_heteroKron_le_one _ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) _ _
        S.ψ S.ψ_norm)
      (_root_.MIPStarRE.QPBT.one_le_deltaLd_of_one_le_error ha hb0.le (not_le.mp hε1).le D.hm D.hd D.hk)
  · refine le_trans h3 (le_trans ?_ (habs D ε hε hε1))
    have hloss : (0 : ℝ) ≤ ((D.combined.m * D.d : ℕ) : ℝ) / (D.q : ℝ) := by positivity
    linarith
  · exact le_trans
      (_root_.MIPStarRE.QPBT.consistencyDefect_heteroKron_le_one _ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) _ _
        S.ψ S.ψ_norm)
      (_root_.MIPStarRE.QPBT.one_le_deltaLd_of_one_le_error ha hb0.le (not_le.mp hε1).le D.hm D.hd D.hk)
