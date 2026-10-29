-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:57:21.700428+00:00
-- url     : https://prove2.me/submissions/fc5c193f-d102-4516-b9ff-da79d562380e

-- Generated proof for MIPStarRE.LDT.Commutativity.evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_gCommStability_sliceSSC

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
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι) (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft params family)
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyRight params family)
      zeta := by
  have hsliceSSC :
      _root_.LIDT.MIPStarRE.LDT.BipartiteSSCRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas family.meas)
        (zeta / 2) := by
    change _root_.LIDT.MIPStarRE.LDT.BipartiteSSCRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
      (fun x => (family.meas x).toSubMeas) (zeta / 2)
    exact _root_.LIDT.MIPStarRE.LDT.Commutativity.gCommStability_sliceSSC params strategy zeta family
      (fun x => (family.meas x).toSubMeas) (fun _ => rfl) hself
  have hpost :
      ∀ u : _root_.LIDT.MIPStarRE.LDT.Point params,
        _root_.LIDT.MIPStarRE.LDT.SDDRel strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft
            (fun x => _root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas x).toSubMeas)))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight
            (fun x => _root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas x).toSubMeas)))
          zeta := by
    intro u
    have htmp :=
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.twoNotionsOfSelfConsistencyAfterEvaluation
        strategy.state
        strategy.permInvState
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas family.meas)
        (zeta / 2)
        (fun (_ : _root_.LIDT.MIPStarRE.LDT.Fq params) (g : _root_.LIDT.MIPStarRE.LDT.Polynomial params) => g u)
        hsliceSSC
    refine ⟨?_⟩
    have hbound :
        _root_.LIDT.MIPStarRE.LDT.sddError strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft
            (fun x => _root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas x).toSubMeas)))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight
            (fun x => _root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas x).toSubMeas))) ≤
        2 * (zeta / 2) := by
      simpa [_root_.LIDT.MIPStarRE.LDT.evaluateAt, _root_.LIDT.MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas] using htmp.squaredDistanceBound
    calc
      _root_.LIDT.MIPStarRE.LDT.sddError strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftLeft
            (fun x => _root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas x).toSubMeas)))
          (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.liftRight
            (fun x => _root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas x).toSubMeas)))
        ≤ 2 * (zeta / 2) := hbound
      _ = zeta := by ring
  constructor
  let e := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointNextEquiv params
  let f : _root_.LIDT.MIPStarRE.LDT.Point params → _root_.LIDT.MIPStarRE.LDT.Fq params → _root_.LIDT.MIPStarRE.LDT.Error :=
    fun u x =>
      _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
        (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ι)
          (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas x).toSubMeas)))
        (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ι)
          (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas x).toSubMeas)))
  rw [_root_.LIDT.MIPStarRE.LDT.sddError]
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (fun w =>
          _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft params family w)
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyRight params family w))
      = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Fq params))
          (fun ux => f ux.1 ux.2) := by
          calc
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
                (fun w =>
                  _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
                    (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft params family w)
                    (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyRight params family w))
              = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Fq params))
                  (fun ux =>
                    _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
                      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft params family (e.symm ux))
                      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyRight params family (e.symm ux))) :=
                  _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv e
                    (fun w =>
                      _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
                        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft params family w)
                        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyRight params family w))
            _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params × _root_.LIDT.MIPStarRE.LDT.Fq params))
                  (fun ux => f ux.1 ux.2) := by
                    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
                    intro ux
                    rcases ux with ⟨u, x⟩
                    change _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
                      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft params family (_root_.LIDT.MIPStarRE.LDT.appendPoint params u x))
                      (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyRight params family (_root_.LIDT.MIPStarRE.LDT.appendPoint params u x)) =
                        _root_.LIDT.MIPStarRE.LDT.qSDD strategy.state
                          (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ι)
                            (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas x).toSubMeas)))
                          (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ι)
                            (_root_.LIDT.MIPStarRE.LDT.evaluateAt params u ((family.meas x).toSubMeas)))
                    simp [_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyLeft, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamilyRight,
                      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedPointFamily, _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily.evaluatedAtNextPoint,
                      _root_.LIDT.MIPStarRE.LDT.evaluateAt, _root_.LIDT.MIPStarRE.LDT.truncatePoint_appendPoint, _root_.LIDT.MIPStarRE.LDT.pointHeight_appendPoint]
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
          (fun u => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x => f u x)) := by
            exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod f
    _ ≤ zeta := by
          exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_le_const
            (fun u : _root_.LIDT.MIPStarRE.LDT.Point params =>
              _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params)) (fun x => f u x))
            zeta
            (fun u => (hpost u).squaredDistanceBound)
