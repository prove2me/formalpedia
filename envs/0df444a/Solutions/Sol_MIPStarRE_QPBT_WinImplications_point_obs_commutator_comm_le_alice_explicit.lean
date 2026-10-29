-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_alice_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:49:36.010686+00:00
-- url     : https://prove2.me/submissions/b7dcbefb-dc47-4484-b8f0-63f805c2d639

-- Generated proof for MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_alice_explicit.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_TwistedCommutation
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_pairW_self_consistency_comm_le
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_pointObs_eq_one_sub_two_smul
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_point_obs_commutator_comm_le_explicit
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_win_comm_cons_explicit
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_win_comm_explicit

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/-!
# The phase-signed commutation relation of the point observables

This module assembles the commuting and anticommuting halves into Equation
`eq:pts-obs-commutation` of `lem:qld-win-implications-obs`: on average over a
uniformly random tuple the two point observables commute up to the sign
`(-1)^gamma(omega)`, with error the square root of the test error.

## References

The declarations formalize the first assertion of
`lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-362`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications



/-! ## The unconditional bound on a difference of reflections -/





/-! ## Splitting the uniform average -/









/-! ## The twisted commutation relation -/



/-! ## The commuting half on Alice's factor -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.pauliEdgeNonemptyTwisted

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε), 0 ≤ ε →
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.commTupleDist P) (fun ω =>
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
              S.pointObs .alice .Z ω.2.2.2 ω.2.1) (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) -
            _root_.MIPStarRE.QPBT.heteroKron (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
              S.pointObs .alice .X ω.2.2.1 ω.1) (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB))
          S.toStrategy.ψ‖ ^ 2) ≤
        (1024 * (2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) +
          1024 * Real.sqrt (4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ))) *
            (ε + Real.sqrt ε) := by
  classical
  have hcard : (1 : ℝ) ≤ (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card _root_.MIPStarRE.QPBT.PauliEdge)
  set K : ℝ := 4 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) with hKdef
  have hK : (0 : ℝ) ≤ K := by rw [hKdef]; linarith
  intro P ε S hε
  have hsq : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hmain := _root_.MIPStarRE.QPBT.WinImplications.point_obs_commutator_comm_le_explicit
    (ιL := S.toStrategy.ιA) (ιR := S.toStrategy.ιB)
    (fun ω => S.pointTraceMeas .alice .X ω.1 ω.2.2.1)
    (fun ω => S.pointTraceMeas .alice .Z ω.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .alice .X ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .alice .Z ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .bob .X ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairWMeas .bob .Z ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pairMeas .bob ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
    (fun ω => S.pointObs .alice .X ω.2.2.1 ω.1)
    (fun ω => S.pointObs .alice .Z ω.2.2.2 ω.2.1)
    S.toStrategy.ψ S.toStrategy.ψ_norm (by positivity)
    (fun ω => _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective _ (S.isProjective.2 _) _)
    (fun ω => _root_.MIPStarRE.QPBT.WinImplications.pointObs_eq_one_sub_two_smul S .alice .X ω.2.2.1 ω.1)
    (fun ω => _root_.MIPStarRE.QPBT.WinImplications.pointObs_eq_one_sub_two_smul S .alice .Z ω.2.2.2 ω.2.1)
    (_root_.MIPStarRE.QPBT.WinImplications.win_comm_cons_explicit P ε S hε .X) (_root_.MIPStarRE.QPBT.WinImplications.win_comm_cons_explicit P ε S hε .Z)
    (_root_.MIPStarRE.QPBT.WinImplications.pairW_self_consistency_comm_le S .X) (_root_.MIPStarRE.QPBT.WinImplications.pairW_self_consistency_comm_le S .Z)
    (_root_.MIPStarRE.QPBT.WinImplications.win_comm_explicit P ε S hε .X) (_root_.MIPStarRE.QPBT.WinImplications.win_comm_explicit P ε S hε .Z)
  refine le_trans hmain ?_
  have hKsplit : Real.sqrt (2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε +
      2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε) =
      Real.sqrt K * Real.sqrt ε := by
    rw [show 2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε +
        2 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε = K * ε by
      rw [hKdef]; ring]
    exact Real.sqrt_mul hK ε
  rw [hKsplit]
  nlinarith [Real.sqrt_nonneg K, hε, hsq]
