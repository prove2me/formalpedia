-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Commutativity.fullSliceCommutation_avg_swap_terms
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:57:21.602721+00:00
-- url     : https://prove2.me/submissions/18d7c66b-2500-4ab3-a267-40e03ffa4f69

-- Generated proof for MIPStarRE.LDT.Commutativity.fullSliceCommutation_avg_swap_terms.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_avgOver_uniform_sum_eq_card_mul_prod

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
# Full-slice averages and index equivalences

Zero-family definition, shared average-reindexing helpers, and averaged scalar
and tensor quantities for the full-slice outcome space, together with
data-reindexing equivalences.

The tensor-form averages are internal to the scalar/tensor comparison recorded
in `docs/decisions/713-scalar-tensor-decision.md`; downstream code should use
the scalar public API.

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
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params))
        (fun q => ∑ gh : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceOutcome params,
          _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABTerm params strategy family q gh) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params))
        (fun q => ∑ gh : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceOutcome params,
          _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABATerm params strategy family q gh) ∧
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params))
        (fun q => ∑ gh : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceOutcome params,
          _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABATerm params strategy family q gh) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params))
        (fun q => ∑ gh : _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceOutcome params,
          _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABTerm params strategy family q gh) := by
  let Q := _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceQuestion params
  let O := _root_.LIDT.MIPStarRE.LDT.Commutativity.FullSliceOutcome params
  let e : (Q × O) ≃ (Q × O) :=
    { toFun := fun z => ((z.1.2, z.1.1), (z.2.2, z.2.1))
      invFun := fun z => ((z.1.2, z.1.1), (z.2.2, z.2.1))
      left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl }
  have hpairBAB :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Q × O))
          (fun z => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABTerm params strategy family z.1 z.2) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Q × O))
          (fun z => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABATerm params strategy family z.1 z.2) := by
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Q × O))
          (fun z => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABTerm params strategy family z.1 z.2)
        = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Q × O))
            (fun z => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABTerm params strategy family (e.symm z).1 (e.symm z).2) := by
              simpa using
                (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv e
                  (fun z : Q × O => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABTerm params strategy family z.1 z.2))
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Q × O))
            (fun z => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABATerm params strategy family z.1 z.2) := by
              apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
              rintro ⟨⟨x, y⟩, ⟨g, h⟩⟩
              simp [e, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABTerm, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABATerm,
                _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceFirstFactor, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceSecondFactor]
  have hpairBABA :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Q × O))
          (fun z => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABATerm params strategy family z.1 z.2) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Q × O))
          (fun z => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABTerm params strategy family z.1 z.2) := by
    calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Q × O))
          (fun z => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABATerm params strategy family z.1 z.2)
        = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Q × O))
            (fun z => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABATerm params strategy family (e.symm z).1 (e.symm z).2) := by
              simpa using
                (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv e
                  (fun z : Q × O => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABATerm params strategy family z.1 z.2))
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Q × O))
            (fun z => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABTerm params strategy family z.1 z.2) := by
              apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
              rintro ⟨⟨x, y⟩, ⟨g, h⟩⟩
              simp [e, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABATerm, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABTerm,
                _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceFirstFactor, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceSecondFactor]
  constructor
  · calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Q)
          (fun q => ∑ gh : O, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABTerm params strategy family q gh)
        = (Fintype.card O : _root_.LIDT.MIPStarRE.LDT.Error) * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Q × O))
            (fun z => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABTerm params strategy family z.1 z.2) := by
              exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_sum_eq_card_mul_prod
                (fun q gh => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABTerm params strategy family q gh)
      _ = (Fintype.card O : _root_.LIDT.MIPStarRE.LDT.Error) * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Q × O))
            (fun z => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABATerm params strategy family z.1 z.2) := by
              rw [hpairBAB]
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Q)
            (fun q => ∑ gh : O, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABATerm params strategy family q gh) := by
              symm
              exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_sum_eq_card_mul_prod
                (fun q gh => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABATerm params strategy family q gh)
  · calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Q)
          (fun q => ∑ gh : O, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABATerm params strategy family q gh)
        = (Fintype.card O : _root_.LIDT.MIPStarRE.LDT.Error) * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Q × O))
            (fun z => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABATerm params strategy family z.1 z.2) := by
              exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_sum_eq_card_mul_prod
                (fun q gh => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceBABATerm params strategy family q gh)
      _ = (Fintype.card O : _root_.LIDT.MIPStarRE.LDT.Error) * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Q × O))
            (fun z => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABTerm params strategy family z.1 z.2) := by
              rw [hpairBABA]
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Q)
            (fun q => ∑ gh : O, _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABTerm params strategy family q gh) := by
              symm
              exact _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_sum_eq_card_mul_prod
                (fun q gh => _root_.LIDT.MIPStarRE.LDT.Commutativity.fullSliceABABTerm params strategy family q gh)
