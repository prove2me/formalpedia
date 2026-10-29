-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T18:18:37.598986+00:00
-- url     : https://prove2.me/submissions/f0bd0b48-ae6f-4ecc-9218-fd9333a74ab3

-- Generated proof for MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProjUnsymmetrization
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_DirectSum
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_qBipartiteMatchMass_roleRegisterProjMeas_arbitrary_eq_average
import Theorems.Thm_LIDT_MIPStarRE_LDT_qBipartiteConsDefect_of_measurements

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.ProjStrat
end LIDT.MIPStarRE.LDT.ProjStrat

namespace LIDT

end LIDT

open LIDT
/-!
# Heterogeneous role-register measurement extraction

This file contains the principal-block extraction used to unsymmetrize a
measurement on the heterogeneous role-register space
`Role × (ιA ⊕ ιB)`.  The Alice extraction is the block indexed by
`(Role.A, Sum.inl _)`; the Bob extraction is the block indexed by
`(Role.B, Sum.inr _)`.

These are the two-space analogues of the same-space extractions in
`MIPStarRE.LDT.Test.Unsymmetrization`.  They preserve POVM completeness, but
they do not assert that arbitrary principal blocks of a projective measurement
remain projective.  As in the paper proof, projectivity is restored later by
the projectivization step.

## References

* `references/ldt-paper/inductive_step.tex`, lines 84--109.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT




open LIDT.MIPStarRE.LDT.ProjStrat

/-! ### Extraction on the constructed role-register measurements -/

/-! ### Trace compression for occupied role-register sectors -/

theorem solution
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (MA : _root_.LIDT.MIPStarRE.LDT.ProjMeas Outcome ιA) (MB : _root_.LIDT.MIPStarRE.LDT.ProjMeas Outcome ιB)
    (G : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome (_root_.LIDT.MIPStarRE.LDT.ProjStrat.RoleRegisterLocal ιA ιB)) :
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmState ψ)
        (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterProjMeas MA MB).toSubMeas G.toSubMeas =
      (_root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas +
        _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas) / 2 := by
  calc
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmState ψ)
        (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterProjMeas MA MB).toSubMeas G.toSubMeas
      = _root_.LIDT.MIPStarRE.LDT.ev (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmState ψ)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op
            (_root_.LIDT.MIPStarRE.LDT.ProjStrat.RoleRegisterLocal ιA ιB × _root_.LIDT.MIPStarRE.LDT.ProjStrat.RoleRegisterLocal ιA ιB)) -
          _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmState ψ)
            (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterProjMeas MA MB).toSubMeas G.toSubMeas := by
            exact _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect_of_measurements (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmState ψ)
              (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterProjMeas MA MB).toMeasurement G
    _ = _root_.LIDT.MIPStarRE.LDT.ev ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB)) -
          _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmState ψ)
            (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterProjMeas MA MB).toSubMeas G.toSubMeas := by
            rw [_root_.LIDT.MIPStarRE.LDT.ev_one_of_isNormalized (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmState ψ)
              (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmState_isNormalized ψ hψ), _root_.LIDT.MIPStarRE.LDT.ev_one_of_isNormalized ψ hψ]
    _ = _root_.LIDT.MIPStarRE.LDT.ev ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB)) -
          ((_root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas +
            _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas) / 2) := by
            rw [_root_.LIDT.MIPStarRE.LDT.ProjStrat.qBipartiteMatchMass_roleRegisterProjMeas_arbitrary_eq_average]
    _ = ((_root_.LIDT.MIPStarRE.LDT.ev ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB)) -
            _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas) +
          (_root_.LIDT.MIPStarRE.LDT.ev ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB)) -
            _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas)) / 2 := by
            ring
    _ = (_root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas +
          _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas) / 2 := by
            rw [← _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect_of_measurements ψ MA.toMeasurement
              (G.extractRoleRegisterBob)]
            rw [← _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect_of_measurements ψ
              (G.extractRoleRegisterAlice) MB.toMeasurement]
