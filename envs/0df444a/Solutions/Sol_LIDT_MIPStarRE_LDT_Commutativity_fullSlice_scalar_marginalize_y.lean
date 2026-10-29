-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.fullSlice_scalar_marginalize_y
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:15:26.128298+00:00
-- url     : https://prove2.me/submissions/bcd3ad8d-7e8a-40e7-bc79-3037a712c677

-- Generated proof for MIPStarRE.LDT.Commutativity.fullSlice_scalar_marginalize_y.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
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
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_fullSliceABAB_to_xEvaluatedSliceBABAtensorAvg
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_xEvaluatedFullSliceABABAvg_to_xEvaluatedFullSliceABABtensorAvg
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_xEvaluatedFullSliceABABtensor_to_evaluatedSliceABABAvg
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABAvg

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Commutativity/Main/Auxiliary/ScalarMarginalization.lean. -/
/-!
# Section 11 commutativity: scalar marginalization lemmas

Schwartz–Zippel marginalization helpers (`eq:evaluate-gcom-at-points`,
`eq:gcom4-diff`) used in the final full-slice commutation theorem.

The public lemmas `fullSlice_scalar_marginalize_x` and
`fullSlice_scalar_marginalize_y` are pure scalar inequalities.  Their proofs
compose internal tensor-form comparisons over the tensor averages defined in
`Transport/FullSlice/Averages.lean`, with `closenessOfIP` at cost `√ζ` each.

See `docs/decisions/713-scalar-tensor-decision.md` for the full decision record.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



/-- Triangle inequality with explicit bounds for an intermediate point. -/
private lemma abs_sub_le_of_two_step
    {a b c e₁ e₂ : Error}
    (hab : |a - b| ≤ e₁) (hbc : |b - c| ≤ e₂) :
    |a - c| ≤ e₁ + e₂ :=
  (abs_sub_le a b c).trans (add_le_add hab hbc)

















end MIPStarRE.LDT.Commutativity

end

end LIDT

open LIDT
/-!
# Section 11 commutativity: scalar marginalization lemmas

Schwartz–Zippel marginalization helpers (`eq:evaluate-gcom-at-points`,
`eq:gcom4-diff`) used in the final full-slice commutation theorem.

The public lemmas `fullSlice_scalar_marginalize_x` and
`fullSlice_scalar_marginalize_y` are pure scalar inequalities.  Their proofs
compose internal tensor-form comparisons over the tensor averages defined in
`Transport/FullSlice/Averages.lean`, with `closenessOfIP` at cost `√ζ` each.

See `docs/decisions/713-scalar-tensor-decision.md` for the full decision record.

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
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family -
        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family| ≤
      (2 * ((↑params.m : _root_.LIDT.MIPStarRE.LDT.Error) * ↑params.d / ↑params.q) + 4 * Real.sqrt zeta) := by
  let yClose :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABAvg
      params strategy family zeta hnorm hself
  have hxPrefix :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAB_to_xEvaluatedSliceBABAtensorAvg
      params strategy family zeta hnorm hself
  have htail :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABtensor_to_evaluatedSliceABABAvg
      params strategy family zeta hnorm hself
  have hsecond :=
    _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABAvg_to_xEvaluatedFullSliceABABtensorAvg
      params strategy family zeta hnorm hself
  have hclose := abs_sub_le_of_two_step yClose hsecond
  have hclose_bound :
      |_root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedSliceBABAtensorAvg params strategy family -
          _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABtensorAvg params strategy family| ≤
        2 * Real.sqrt zeta := by
    calc
      |_root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedSliceBABAtensorAvg params strategy family -
          _root_.LIDT.MIPStarRE.LDT.Commutativity.xEvaluatedFullSliceABABtensorAvg params strategy family|
        ≤ Real.sqrt zeta + Real.sqrt zeta := hclose
      _ = 2 * Real.sqrt zeta := by ring
  have hprefix := abs_sub_le_of_two_step hxPrefix hclose_bound
  have h := abs_sub_le_of_two_step hprefix htail
  calc
    |_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family -
        _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family|
      ≤ (((↑params.m : _root_.LIDT.MIPStarRE.LDT.Error) * ↑params.d / ↑params.q + Real.sqrt zeta) +
          2 * Real.sqrt zeta) +
          ((↑params.m : _root_.LIDT.MIPStarRE.LDT.Error) * ↑params.d / ↑params.q + Real.sqrt zeta) := h
    _ = 2 * ((↑params.m : _root_.LIDT.MIPStarRE.LDT.Error) * ↑params.d / ↑params.q) +
          4 * Real.sqrt zeta := by ring
