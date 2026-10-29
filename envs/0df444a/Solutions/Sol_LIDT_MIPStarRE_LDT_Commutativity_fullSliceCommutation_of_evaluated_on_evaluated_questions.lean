-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.fullSliceCommutation_of_evaluated_on_evaluated_questions
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:40:46.548349+00:00
-- url     : https://prove2.me/submissions/68b48be0-0b22-45c6-b773-947bcc9c833f

-- Generated proof for MIPStarRE.LDT.Commutativity.fullSliceCommutation_of_evaluated_on_evaluated_questions.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_fullSliceCommutation_qSDDOp_avg_eq
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_fullSliceProductLeft_to_zero_le_one
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_fullSlice_closenessOfIP_CAB_hEval_sqrt
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_fullSlice_scalar_marginalize_x
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_fullSlice_scalar_marginalize_y
import Theorems.Thm_LIDT_MIPStarRE_LDT_Commutativity_zero_to_fullSliceProductRight_le_one

namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Section 11 commutativity: evaluated-question transport

Core Schwartz–Zippel transport on the evaluated-question space, comparing
full-polynomial and point-evaluated outcomes.

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
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q] (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (family : _root_.LIDT.MIPStarRE.LDT.IdxPolyFamily params ι)
    (gamma zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (hnorm : strategy.state.IsNormalized)
    (hgamma_nonneg : 0 ≤ gamma) (hzeta_nonneg : 0 ≤ zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hEval :
      _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedFromFullSliceProductLeft params strategy family)
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedFromFullSliceProductRight params strategy family)
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError params gamma zeta)) :
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
      (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductLeft params strategy family
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductRight params strategy family
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q))
      (_root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError params gamma zeta) := by
  /-
  Paper reference: `references/ldt-paper/commutativity-G.tex`,
  theorem `thm:com-main`, especially the passage from
  `eq:evaluate-gcom-at-points` to `eq:evaluate-gcom-at-points-part-dos`
  and the final displayed error estimate.

  The paper-faithful transport below passes from the full polynomial products
  down to the evaluated products on the sampled points.

  The paper first reduces to the small-parameter regime
  `γ ≤ 1`, `ζ ≤ 1`, and `d / q ≤ 1`; otherwise `comMainError` is already large
  enough while the unexpanded `sddErrorOp` is trivially bounded.

  In the small-parameter case, the proof uses two Schwartz-Zippel
  marginalizations together with `closenessOfIP` and the evaluated
  commutation estimate obtained from `hEval`, producing the displayed error
  chain that is then absorbed into `comMainError`.
  -/
  -- WLOG: reduce to the small-parameter regime (paper lines 260–276).
  -- When max(γ, ζ, d/q) ≥ 1, comMainError ≥ 30m ≥ 30 while
  -- sddErrorOp ≤ 4 by the sub-measurement bound, so the inequality
  -- holds trivially.
  by_cases hsmall :
      gamma ≤ 1 ∧ zeta ≤ 1 ∧
        (↑params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (↑params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 1
  · -- Small-parameter case: γ, ζ, d/q ≤ 1.
    obtain ⟨hgamma_le, hzeta_le, hdq_le⟩ := hsmall
    -- Step 1: The Schwartz-Zippel transport.
    -- Bound the full-product sddErrorOp by corrections from:
    -- (a) The x switch-sandwich transport (`4√ζ`) and the y scalar
    --     marginalization (`2md/q + 4√ζ`)
    -- (b) The evaluated commutation via the strong `hEval` transport
    --     (≤ √(commDataProcessedGError))
    -- giving total ≤ 16√ζ + 4md/q + 2√(commDataProcessedGError).
    --
    -- Proof sketch:
    -- * Expand qSDDOp into quartic trace terms
    --   (BAB + ABA - BABA - ABAB) using projectivity
    -- * Use BAB = ABA and BABA = ABAB symmetry (swap x↔y, g↔h)
    -- * For each of ABA and ABAB, apply the marginalization chain
    --   to relate full-polynomial sums to evaluated sums
    -- * Use submeasurement bounds (Σ_g G^x_g ≤ I) to control
    --   quartic terms: ABA ≤ 1
    -- * The ABAB term uses hEval through closenessOfIP to obtain
    --   √(commDataProcessedGError)
    have hTransport :
        _root_.LIDT.MIPStarRE.LDT.sddErrorOp strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductLeft params strategy family
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q))
          (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductRight params strategy family
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q)) ≤
        16 * Real.sqrt zeta +
          4 * (↑params.m * ↑params.d / ↑params.q) +
          2 * Real.sqrt
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError params gamma zeta) := by
      -- Compose the four scalar lemmas.  Paper chain:
      -- * `fullSliceCommutation_qSDDOp_avg_eq` rewrites the pulled-back
      --   `sddErrorOp` as `2 · (fullABA − fullABAB)` (paper lines 286-290).
      -- * Triangle on the real line:
      --     `|fullABA − fullABAB|
      --        ≤ |fullABA − evalABA| + |evalABA − evalABAB|
      --          + |evalABAB − fullABAB|`
      -- * `fullSlice_scalar_marginalize_x`: the first-term switch-sandwich
      --   comparison costs `4√ζ`.
      -- * `fullSlice_scalar_marginalize_y`: the paper-faithful second-term
      --   comparison splits into the proved x-prefix `md/q + √ζ`, the proved
      --   line-359 comparison `√ζ`, the proved line-360 comparison `√ζ`, and the proved
      --   y-tail `md/q + √ζ`, for a total of `2md/q + 4√ζ`.
      -- * `fullSlice_closenessOfIP_CAB_hEval_sqrt`: the direct evaluated-side
      --   route gives `|evalABA − evalABAB| ≤ √ν`.
      -- Summing gives `|fullABA − fullABAB| ≤ 8√ζ + 2(md/q) + √ν`,
      -- and multiplying by `2` produces `16√ζ + 4(md/q) + 2√ν`.
      have hExpand :=
        _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceCommutation_qSDDOp_avg_eq params strategy family
      have hMargX :=
        _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSlice_scalar_marginalize_x params strategy family zeta hnorm hself
      have hMargY :=
        _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSlice_scalar_marginalize_y params strategy family zeta hnorm hself
      have hClose :=
        _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSlice_closenessOfIP_CAB_hEval_sqrt params strategy family gamma zeta
          hnorm hEval
      -- Triangle inequality on the three intermediate quantities.
      have hTri :
          |_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family -
              _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family| ≤
            |_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family -
                _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family| +
              |_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family -
                  _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family| +
              |_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family -
                  _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family| := by
        have h1 :
            _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family -
                _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family =
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family -
                  _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family) +
                (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family -
                    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family) +
                (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family -
                    _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family) := by
          ring
        calc
          |_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family -
              _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family|
            = |(_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family -
                  _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family) +
                (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family -
                    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family) +
                (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family -
                    _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family)| := by
                  rw [h1]
          _ ≤ |(_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family -
                  _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family) +
                (_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family -
                    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family)| +
                |_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family -
                    _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family| :=
                abs_add_le _ _
          _ ≤ (|_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family -
                    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family| +
                  |_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family -
                      _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family|) +
                |_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family -
                    _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family| := by
                gcongr
                exact abs_add_le _ _
      -- Symmetry of `abs`: `|evalABAB - fullABAB| = |fullABAB - evalABAB|`.
      have hMargY' :
          |_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family -
              _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family| ≤
            2 * ((↑params.m : _root_.LIDT.MIPStarRE.LDT.Error) * ↑params.d / ↑params.q) +
              4 * Real.sqrt zeta := by
        rw [abs_sub_comm]
        exact hMargY
      -- `sddErrorOp = 2 · (fullABA − fullABAB) ≤ 2 · |fullABA − fullABAB|`.
      have hTwoAbs :
          _root_.LIDT.MIPStarRE.LDT.sddErrorOp strategy.state
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
            (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductLeft params strategy family
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q))
            (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductRight params strategy family
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q)) ≤
          2 *
            |_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family -
                _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family| := by
        rw [hExpand]
        have := le_abs_self
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family -
            _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family)
        linarith
      calc
        _root_.LIDT.MIPStarRE.LDT.sddErrorOp strategy.state
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
            (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductLeft params strategy family
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q))
            (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductRight params strategy family
              (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q))
          ≤ 2 *
              |_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family -
                  _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family| := hTwoAbs
        _ ≤ 2 *
              (|_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABAAvg params strategy family -
                    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family| +
                |_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABAAvg params strategy family -
                    _root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family| +
                |_root_.LIDT.MIPStarRE.LDT.Commutativity.evaluatedSliceABABAvg params strategy family -
                    _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABAvg params strategy family|) := by
              linarith [hTri]
        _ ≤ 2 *
              (4 * Real.sqrt zeta +
                Real.sqrt
                  (_root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError params gamma zeta) +
                (2 * ((↑params.m : _root_.LIDT.MIPStarRE.LDT.Error) * ↑params.d / ↑params.q) +
                  4 * Real.sqrt zeta)) := by
              linarith [hMargX, hMargY', hClose]
        _ = 16 * Real.sqrt zeta +
              4 * (↑params.m * ↑params.d / ↑params.q) +
              2 * Real.sqrt
                (_root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError params gamma zeta) := by ring
    -- Step 2: Error arithmetic (using small-parameter hypotheses).
    -- Show:
    --   16√ζ + 4md/q + 2√(48m(√γ + √ζ))
    --     ≤ 30m(γ^¼ + ζ^¼ + (d/q)^¼)
    --
    -- Key estimates (all require γ, ζ, d/q ≤ 1):
    -- * 2√(48m(√γ + √ζ)) ≤ 2√(48m)(γ^¼ + ζ^¼) ≤ 14m(γ^¼ + ζ^¼)
    --   using √(a+b) ≤ √a + √b and √m ≤ m (for m ≥ 1)
    -- * 16√ζ ≤ 16m·ζ^¼ (ζ ≤ 1 ⇒ ζ^½ ≤ ζ^¼; m ≥ 1)
    -- * 4md/q ≤ 6m(d/q)^¼ (d/q ≤ 1 ⇒ x ≤ x^¼)
    -- * Total: 14m·γ^¼ + 30m·ζ^¼ + 6m·(d/q)^¼
    --         ≤ 30m(γ^¼ + ζ^¼ + (d/q)^¼)
    have hArith :
        16 * Real.sqrt zeta +
          4 * (↑params.m * ↑params.d / ↑params.q) +
          2 * Real.sqrt
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError params gamma zeta) ≤
        _root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError params gamma zeta := by
      unfold _root_.LIDT.MIPStarRE.LDT.Commutativity.commDataProcessedGError _root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError
      -- Useful numerical facts
      have hm_ge : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) :=
        Nat.one_le_cast.mpr (Nat.succ_le_of_lt params.hm)
      have hq_pos : (0 : _root_.LIDT.MIPStarRE.LDT.Error) < ↑params.q :=
        Nat.cast_pos.mpr params.hq
      have hdq_nn : 0 ≤ (↑params.d : _root_.LIDT.MIPStarRE.LDT.Error) / ↑params.q :=
        div_nonneg (Nat.cast_nonneg _) hq_pos.le
      have hg4 : 0 ≤ Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
        Real.rpow_nonneg hgamma_nonneg _
      have hz4 : 0 ≤ Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
        Real.rpow_nonneg hzeta_nonneg _
      have hdq4 : 0 ≤ Real.rpow
          ((↑params.d : _root_.LIDT.MIPStarRE.LDT.Error) / ↑params.q) (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
        Real.rpow_nonneg hdq_nn _
      -- Step 1: sqrt ζ ≤ ζ^(1/4)
      have h_sqrt_z : Real.sqrt zeta ≤
          Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_ge'
          hzeta_nonneg hzeta_le (by norm_num) (by norm_num)
      -- Step 2: d/q ≤ (d/q)^(1/4)
      have h_dq : (↑params.d : _root_.LIDT.MIPStarRE.LDT.Error) / ↑params.q ≤
          Real.rpow ((↑params.d : _root_.LIDT.MIPStarRE.LDT.Error) / ↑params.q)
            (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
        conv_lhs =>
          rw [show (↑params.d : _root_.LIDT.MIPStarRE.LDT.Error) / ↑params.q =
            Real.rpow ((↑params.d : _root_.LIDT.MIPStarRE.LDT.Error) / ↑params.q) 1
            from (Real.rpow_one _).symm]
        exact Real.rpow_le_rpow_of_exponent_ge'
          hdq_nn hdq_le (by norm_num) (by norm_num)
      -- Step 3: (γ^(1/4))² = γ^(1/2) and (ζ^(1/4))² = ζ^(1/2)
      have hg4_sq :
          (Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ) =
            Real.rpow gamma (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
        calc (Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ)
            = (Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) ^
                (2 : _root_.LIDT.MIPStarRE.LDT.Error) := by norm_num
          _ = Real.rpow gamma
                (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error) * 2) := by
              symm; exact Real.rpow_mul hgamma_nonneg _ _
          _ = Real.rpow gamma
                (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
      have hz4_sq :
          (Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ) =
            Real.rpow zeta (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
        calc (Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ)
            = (Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) ^
                (2 : _root_.LIDT.MIPStarRE.LDT.Error) := by norm_num
          _ = Real.rpow zeta
                (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error) * 2) := by
              symm; exact Real.rpow_mul hzeta_nonneg _ _
          _ = Real.rpow zeta
                (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) := by norm_num
      -- Step 4: √(48m(γ^½+ζ^½)) ≤ √(48m)·(γ^¼+ζ^¼)
      -- Using γ^½ = (γ^¼)² and a²+b² ≤ (a+b)²
      have hsqrt_cdpg :
          Real.sqrt (48 * ↑params.m *
            (Real.rpow gamma (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow zeta (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)))) ≤
          Real.sqrt (48 * ↑params.m) *
            (Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
        rw [← hg4_sq, ← hz4_sq]
        have hsq_le :
            (Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ) +
              (Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ) ≤
            (Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) ^
                (2 : ℕ) := by
          nlinarith [hg4, hz4]
        calc Real.sqrt (48 * ↑params.m *
              ((Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) ^
                  (2 : ℕ) +
                (Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) ^
                  (2 : ℕ)))
            ≤ Real.sqrt (48 * ↑params.m *
                (Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                  Real.rpow zeta
                    (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) ^ (2 : ℕ)) := by
              apply Real.sqrt_le_sqrt
              exact mul_le_mul_of_nonneg_left hsq_le
                (by positivity)
          _ = Real.sqrt (48 * ↑params.m) *
                Real.sqrt
                  ((Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                    Real.rpow zeta
                      (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) ^
                    (2 : ℕ)) := by
              rw [Real.sqrt_mul (by positivity)]
          _ = Real.sqrt (48 * ↑params.m) *
                (Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                  Real.rpow zeta
                    (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
              rw [Real.sqrt_sq (by linarith)]
      -- Step 5: 2·√(48m) ≤ 14m (since 192m ≤ 196m²
      --   for m ≥ 1)
      have hsqrt_48m :
          Real.sqrt (48 * ↑params.m) ≤
            7 * ↑params.m := by
        rw [show 7 * (↑params.m : _root_.LIDT.MIPStarRE.LDT.Error) =
          Real.sqrt ((7 * ↑params.m) ^ 2) from
          (Real.sqrt_sq (by linarith)).symm]
        apply Real.sqrt_le_sqrt
        nlinarith [hm_ge]
      -- Combine the three parts
      have hA : 16 * Real.sqrt zeta ≤
          16 * ↑params.m *
            Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
        nlinarith [h_sqrt_z, hm_ge, hz4]
      have hB :
          4 * (↑params.m * ↑params.d / ↑params.q) ≤
          6 * ↑params.m * Real.rpow
            ((↑params.d : _root_.LIDT.MIPStarRE.LDT.Error) / ↑params.q)
            (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
        have hrw :
            ↑params.m * ↑params.d / ↑params.q =
              ↑params.m *
                ((↑params.d : _root_.LIDT.MIPStarRE.LDT.Error) / ↑params.q) := by
          ring
        rw [hrw]
        nlinarith [h_dq, hm_ge, hdq4]
      have hC :
          2 * Real.sqrt (48 * ↑params.m *
            (Real.rpow gamma (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow zeta (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)))) ≤
          14 * ↑params.m *
            (Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow zeta
                (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
        calc 2 * Real.sqrt (48 * ↑params.m *
              (Real.rpow gamma (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                Real.rpow zeta (1 / (2 : _root_.LIDT.MIPStarRE.LDT.Error))))
            ≤ 2 * (Real.sqrt (48 * ↑params.m) *
                (Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                  Real.rpow zeta
                    (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)))) :=
              mul_le_mul_of_nonneg_left hsqrt_cdpg
                (by norm_num)
          _ = 2 * Real.sqrt (48 * ↑params.m) *
                (Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                  Real.rpow zeta
                    (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) := by ring
          _ ≤ 14 * ↑params.m *
                (Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
                  Real.rpow zeta
                    (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
              exact mul_le_mul_of_nonneg_right
                (by linarith [hsqrt_48m])
                (by linarith)
      -- 14m·g4 + 30m·z4 + 6m·dq4 ≤ 30m·(g4+z4+dq4)
      nlinarith [hA, hB, hC, hg4, hz4, hdq4, hm_ge]
    exact ⟨le_trans hTransport hArith⟩
  · -- Large-parameter case: max(γ, ζ, d/q) > 1.
    -- The bound is trivial: sddErrorOp ≤ 4 (by the triangle
    -- inequality for vectors and the sub-measurement property;
    -- paper lines 263–271), while comMainError ≥ 30m ≥ 30 > 4
    -- (since rpow x (1/4) ≥ 1 when x ≥ 1, and m ≥ 1).
    have hleft :=
      _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductLeft_to_zero_le_one params strategy family hnorm
    have hright :=
      _root_.LIDT.MIPStarRE.LDT.Commutativity.zero_to_fullSliceProductRight_le_one params strategy family hnorm
    have hfour :
        _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductLeft params strategy family
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q))
          (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductRight params strategy family
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q))
          4 := by
      have htri :=
        _root_.LIDT.MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
          strategy.state
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
          (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductLeft params strategy family
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q))
          (fun _ => _root_.LIDT.MIPStarRE.LDT.Commutativity.zeroFullSliceOpFamily (ι := ι) params)
          (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductRight params strategy family
            (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q))
          1 1 hleft hright
      refine _root_.LIDT.MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_mono
        strategy.state
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
        (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductLeft params strategy family
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q))
        (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductRight params strategy family
          (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q))
        (2 * (1 + 1)) 4 ?_ htri
      norm_num
    have hcom_ge_four : 4 ≤ _root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError params gamma zeta := by
      unfold _root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError
      have hm_ge : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ (params.m : _root_.LIDT.MIPStarRE.LDT.Error) :=
        Nat.one_le_cast.mpr (Nat.succ_le_of_lt params.hm)
      have hq_pos : (0 : _root_.LIDT.MIPStarRE.LDT.Error) < (params.q : _root_.LIDT.MIPStarRE.LDT.Error) := Nat.cast_pos.mpr params.hq
      have hdq_nonneg : 0 ≤ (params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) :=
        div_nonneg (Nat.cast_nonneg _) hq_pos.le
      have hnotsmall :
          1 < gamma ∨ 1 < zeta ∨ 1 < (params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) := by
        have : ¬ (gamma ≤ 1 ∧ zeta ≤ 1 ∧
            (params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 1) := hsmall
        by_cases hg : gamma ≤ 1
        · by_cases hz : zeta ≤ 1
          · by_cases hdq : (params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 1
            · exact False.elim (this ⟨hg, hz, hdq⟩)
            · exact Or.inr <| Or.inr <| lt_of_not_ge hdq
          · exact Or.inr <| Or.inl <| lt_of_not_ge hz
        · exact Or.inl <| lt_of_not_ge hg
      have hsum_ge_one :
          1 ≤
            Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
        rcases hnotsmall with hg | hz | hdq
        · have hγ : 1 ≤ Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            simpa using Real.one_le_rpow hg.le (show (0 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error) by norm_num)
          have hζnn : 0 ≤ Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := Real.rpow_nonneg hzeta_nonneg _
          have hdqnn :
              0 ≤ Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
            Real.rpow_nonneg hdq_nonneg _
          linarith
        · have hζ : 1 ≤ Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            simpa using Real.one_le_rpow hz.le (show (0 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error) by norm_num)
          have hγnn : 0 ≤ Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := Real.rpow_nonneg hgamma_nonneg _
          have hdqnn :
              0 ≤ Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) :=
            Real.rpow_nonneg hdq_nonneg _
          linarith
        · have hdq' :
              1 ≤ Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := by
            simpa using Real.one_le_rpow hdq.le (show (0 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error) by norm_num)
          have hγnn : 0 ≤ Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := Real.rpow_nonneg hgamma_nonneg _
          have hζnn : 0 ≤ Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) := Real.rpow_nonneg hzeta_nonneg _
          linarith
      calc
        (4 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ 30 := by norm_num
        _ ≤ 30 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) := by nlinarith
        _ ≤ 30 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error) *
            (Real.rpow gamma (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow zeta (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)) +
              Real.rpow (((params.d : _root_.LIDT.MIPStarRE.LDT.Error) / (params.q : _root_.LIDT.MIPStarRE.LDT.Error))) (1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error))) := by
                nlinarith
    exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_mono
      strategy.state
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.EvaluatedSliceQuestion params))
      (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductLeft params strategy family
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q))
      (fun q => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceProductRight params strategy family
        (_root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceQuestionOfEvaluatedSlice params q))
      4 (_root_.LIDT.MIPStarRE.LDT.Commutativity.comMainError params gamma zeta) hcom_ge_four hfour
