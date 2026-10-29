-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceCommutation_avg_swap_terms
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:47:24.289874+00:00
-- url     : https://prove2.me/submissions/0e9d1d8f-6a44-4b0f-835a-2fe449615075

-- Generated proof for MIPStarRE.LDT.Commutativity.evaluatedSliceCommutation_avg_swap_terms.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
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
# Section 11 commutativity: evaluated-slice averaged expansion

Averaged evaluated-slice expansion of `qSDDOp` into the four projector terms
`BAB + ABA - BABA - ABAB`, used to reduce the commutation to per-projector
estimates.

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
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι) (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
          _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm params strategy family q ab) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
          _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family q ab) ∧
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
          _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABATerm params strategy family q ab) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
          _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab) := by
  let eQ : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params ≃ _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params := Equiv.prodComm _ _
  let eA : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params ≃ _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params := Equiv.prodComm _ _
  constructor
  · calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm params strategy family q ab)
        = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
            (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
              _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family (eQ q) ab) := by
              apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
              intro q
              calc
                ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
                    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm params strategy family q ab
                  = ∑ ab' : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
                      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm params strategy family q (eA.symm ab') := by
                      exact Fintype.sum_equiv eA
                        (fun ab => _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm params strategy family q ab)
                        (fun ab' => _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm params strategy family q (eA.symm ab'))
                        (by intro ab; simp [eA])
                _ = ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
                      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family (eQ q) ab := by
                      refine Finset.sum_congr rfl ?_
                      intro ab _
                      rcases q with ⟨u, v⟩
                      rcases ab with ⟨a, b⟩
                      simp [eQ, eA, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABTerm, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm]
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
            (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
              _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family q ab) := by
              simpa [eQ] using
                (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv eQ
                  (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
                    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABATerm params strategy family q ab)).symm
  · calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
            _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABATerm params strategy family q ab)
        = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
            (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
              _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family (eQ q) ab) := by
              apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
              intro q
              calc
                ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
                    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABATerm params strategy family q ab
                  = ∑ ab' : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
                      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABATerm params strategy family q (eA.symm ab') := by
                      exact Fintype.sum_equiv eA
                        (fun ab => _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABATerm params strategy family q ab)
                        (fun ab' =>
                          _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABATerm params strategy family q (eA.symm ab'))
                        (by intro ab; simp [eA])
                _ = ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
                      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family (eQ q) ab := by
                      refine Finset.sum_congr rfl ?_
                      intro ab _
                      rcases q with ⟨u, v⟩
                      rcases ab with ⟨a, b⟩
                      simp [eQ, eA, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceBABATerm, _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm]
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
            (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
              _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab) := by
              simpa [eQ] using
                (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv eQ
                  (fun q => ∑ ab : _root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceOutcome params,
                    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABTerm params strategy family q ab)).symm
