-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:15:26.376977+00:00
-- url     : https://prove2.me/submissions/ef36509f-e6c6-47cf-8211-9d9b7b62dc7f

-- Generated proof for MIPStarRE.LDT.CommutativityPoints.sddOpRel_reindex.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_qSDDOp_reindex

namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints

namespace LIDT

end LIDT

open LIDT
/-!
# Section 10 commutativity points: shared helpers core

Shared reindexing and tensor-placement helpers used by the Section 10
commutativity-of-points argument.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators
/-! ## Shared reindexing and tensor-placement helpers -/

theorem solution
    {Question Outcome Outcome' : Type*}
    [Fintype Outcome] [Fintype Outcome']
    (e : Outcome ≃ Outcome')
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (A B : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily Question Outcome ι) (δ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψ 𝒟 A B δ →
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψ 𝒟
        (fun q =>
          ({ outcome := fun a' => (A q).outcome (e.symm a')
             total := (A q).total } : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome' ι))
        (fun q =>
          ({ outcome := fun a' => (B q).outcome (e.symm a')
             total := (B q).total } : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome' ι))
        δ := by
  intro ⟨h⟩
  constructor
  unfold _root_.LIDT.MIPStarRE.LDT.sddErrorOp at *
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
        (fun q =>
          _root_.LIDT.MIPStarRE.LDT.qSDDOp ψ
            ({ outcome := fun a' => (A q).outcome (e.symm a')
               total := (A q).total } : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome' ι)
            ({ outcome := fun a' => (B q).outcome (e.symm a')
               total := (B q).total } : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome' ι))
      = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun q => _root_.LIDT.MIPStarRE.LDT.qSDDOp ψ (A q) (B q)) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
          intro q
          rw [_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.qSDDOp_reindex e ψ (A q) (B q)]
    _ ≤ δ := h
