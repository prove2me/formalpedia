-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.gCommStability_sliceSSC
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:54:09.578827+00:00
-- url     : https://prove2.me/submissions/a44d767a-b3d3-47a2-8fb5-df8d5de95eb5

-- Generated proof for MIPStarRE.LDT.Commutativity.gCommStability_sliceSSC.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Section 11 commutativity: pointwise scalar approximation

Pointwise overlap terms `⟨ψ, (I - G^x) ⊗ G^x ψ⟩` controlling both sides of
the `G`-stability estimate, used as the base for the averaged scalar bound.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (G : _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    _root_.LIDT.MIPStarRE.LDT.BipartiteSSCRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
      G
      (zeta / 2) := by
  constructor
  calc
    _root_.LIDT.MIPStarRE.LDT.bipartiteSSCError strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
        G
      = (1 / 2 : _root_.LIDT.MIPStarRE.LDT.Error) *
          _root_.LIDT.MIPStarRE.LDT.sddError strategy.state
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
            (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft G)
            (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight G) := by
            unfold _root_.LIDT.MIPStarRE.LDT.bipartiteSSCError _root_.LIDT.MIPStarRE.LDT.sddError
            rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
              (fun x => _root_.LIDT.MIPStarRE.LDT.qBipartiteSSCDefect strategy.state (G x))
              (fun x =>
                (1 / 2 : _root_.LIDT.MIPStarRE.LDT.Error) *
                  _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
                    ((G x).liftLeft)
                    ((G x).liftRight))]
            · rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
              rfl
            · intro x
              simpa [hG x] using
                _root_.LIDT.MIPStarRE.LDT.Commutativity.qBipartiteSSCDefect_eq_half_qSDD_of_proj
                  strategy.state strategy.permInvState (family.meas x)
    _ ≤ (1 / 2 : _root_.LIDT.MIPStarRE.LDT.Error) * zeta := by
          have hsdd_bound :
              _root_.LIDT.MIPStarRE.LDT.sddError strategy.state
                (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
                (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft G)
                (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight G) ≤ zeta := by
            calc
              _root_.LIDT.MIPStarRE.LDT.sddError strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
                  (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft G)
                  (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight G)
                = _root_.LIDT.MIPStarRE.LDT.sddError strategy.state
                    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
                    (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas family.meas))
                    (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas family.meas)) := by
                      unfold _root_.LIDT.MIPStarRE.LDT.sddError
                      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
                      intro x
                      simp [_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight,
                        _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas, hG x]
              _ ≤ zeta := hself.sliceSelfConsistency.squaredDistanceBound
          have hhalf_nonneg : 0 ≤ (1 / 2 : _root_.LIDT.MIPStarRE.LDT.Error) := by norm_num
          exact mul_le_mul_of_nonneg_left
            hsdd_bound
            hhalf_nonneg
    _ = zeta / 2 := by ring
