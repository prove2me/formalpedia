-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.sum_ev_mul_leftBounded_le_of_leftHermitian
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:22:25.40246+00:00
-- url     : https://prove2.me/submissions/6a9e7420-387c-444f-a4a1-801e0d3ca9df

-- Generated proof for MIPStarRE.LDT.Preliminaries.sum_ev_mul_leftBounded_le_of_leftHermitian.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Switch-sandwich gap bounds: Cauchy–Schwarz core

Shared Cauchy–Schwarz contraction used in both the left and middle gap
estimates of the switch-sandwich argument.

## References

- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

theorem solution
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι)
    (LB : _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (X Y : Outcome → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (hLB_herm : LBᴴ = LB)
    (hLB_sq_le_one : LB * LB ≤ 1)
    (hXherm : ∀ a, (X a)ᴴ = X a)
    (hYherm : ∀ a, (Y a)ᴴ = Y a) :
    |∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (X a * (LB * Y a))| ≤
      Real.sqrt (∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (X a * X a)) *
        Real.sqrt (∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ ((Y a)ᴴ * Y a)) := by
  calc
    |∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (X a * (LB * Y a))|
      ≤ ∑ a : Outcome, |_root_.LIDT.MIPStarRE.LDT.ev ψ (X a * (LB * Y a))| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Outcome,
          Real.sqrt (_root_.LIDT.MIPStarRE.LDT.ev ψ (X a * X a)) *
            Real.sqrt (_root_.LIDT.MIPStarRE.LDT.ev ψ (((LB * Y a)ᴴ) * (LB * Y a))) := by
          refine Finset.sum_le_sum ?_
          intro a _
          simpa [hXherm a] using
            _root_.LIDT.MIPStarRE.LDT.ev_abs_mul_le_sqrt ψ (X a) (LB * Y a)
    _ ≤ Real.sqrt
          (∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (X a * X a)) *
        Real.sqrt
          (∑ a : Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψ (((LB * Y a)ᴴ) * (LB * Y a))) := by
          exact
            Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
              (f := fun a => _root_.LIDT.MIPStarRE.LDT.ev ψ (X a * X a))
              (g := fun a => _root_.LIDT.MIPStarRE.LDT.ev ψ (((LB * Y a)ᴴ) * (LB * Y a)))
              (fun a => by
                simpa [hXherm a] using _root_.LIDT.MIPStarRE.LDT.ev_adjoint_self_nonneg ψ ((X a)ᴴ))
              (fun a => by
                exact _root_.LIDT.MIPStarRE.LDT.ev_adjoint_self_nonneg ψ (LB * Y a))
    _ ≤ Real.sqrt
          (∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ (X a * X a)) *
        Real.sqrt
          (∑ a : Outcome, _root_.LIDT.MIPStarRE.LDT.ev ψ ((Y a)ᴴ * Y a)) := by
          apply mul_le_mul
          · exact le_rfl
          · exact Real.sqrt_le_sqrt <| Finset.sum_le_sum fun a _ => by
              have hsand :
                  Y a * (LB * LB) * Y a ≤ Y a * 1 * Y a := by
                exact IsSelfAdjoint.conjugate_le_conjugate hLB_sq_le_one (hYherm a)
              have hev := _root_.LIDT.MIPStarRE.LDT.ev_mono ψ _ _ hsand
              simpa [hLB_herm, hYherm a, Matrix.conjTranspose_mul, mul_assoc] using hev
          · exact Real.sqrt_nonneg _
          · exact Real.sqrt_nonneg _
