-- Prove2me | solution 1 for MIPStarRE.QPBT.ExtendedLineGame.evalCoefficient_ne_imp_directEvalOpt_ne_or_eq_none
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:42:28.649305+00:00
-- url     : https://prove2.me/submissions/49e03c13-4e30-4575-8d6b-daf191758822

-- Generated proof for MIPStarRE.QPBT.ExtendedLineGame.evalCoefficient_ne_imp_directEvalOpt_ne_or_eq_none.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_directEvalOpt_eq_some_iff

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame

/- Source helpers from QPBT/Combining/ExtendedLineGame/ParameterCompletion.lean. -/
/-!
# Parameter evaluation versus completed line evaluation

Completed evaluation of a coefficient vector may return `none`, notably on a
zero-direction line when the represented polynomial is not constant.  A
successful completed readout at the point represented by a parameter agrees
with ordinary coefficient evaluation at that parameter.  Consequently,
parameter-value disagreement is contained in the union of completed-readout
disagreement and the two failure events.

The final theorem lifts this inclusion to the Born weights of two arbitrary
strategy POVMs.  It uses neither projectivity nor a collision estimate.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:230-390`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1402`
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

namespace ExtendedLineGame

/-- A successful completed readout at the point represented by `parameter`
equals coefficient evaluation at `parameter`.  This includes zero directions. -/
theorem evalCoefficient_eq_of_directEvalOpt_affine_eq_some
    {params : _root_.MIPStarRE.QPBT.DirectLdParams} {degree : ℕ}
    (line : _root_.MIPStarRE.QPBT.DirectLineDesc params) (coeffs : _root_.MIPStarRE.QPBT.DirectDegPoly params degree)
    (parameter answer : _root_.MIPStarRE.QPBT.DirectScalarQ params)
    (hread : _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction) coeffs =
      some answer) :
    _root_.MIPStarRE.QPBT.evalCoefficient coeffs parameter = answer := by
  have heval := (_root_.MIPStarRE.QPBT.ExtendedLineGame.directEvalOpt_eq_some_iff line
    (line.base + parameter • line.direction) coeffs answer).mp hread
  exact heval.2 parameter rfl













end ExtendedLineGame

end

end MIPStarRE.QPBT

/-!
# Parameter evaluation versus completed line evaluation

Completed evaluation of a coefficient vector may return `none`, notably on a
zero-direction line when the represented polynomial is not constant.  A
successful completed readout at the point represented by a parameter agrees
with ordinary coefficient evaluation at that parameter.  Consequently,
parameter-value disagreement is contained in the union of completed-readout
disagreement and the two failure events.

The final theorem lifts this inclusion to the Born weights of two arbitrary
strategy POVMs.  It uses neither projectivity nor a collision estimate.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:230-390`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1402`
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



open MIPStarRE.QPBT.ExtendedLineGame

theorem solution
    {params : _root_.MIPStarRE.QPBT.DirectLdParams} {degree : ℕ}
    (line : _root_.MIPStarRE.QPBT.DirectLineDesc params) (coeffsA coeffsB : _root_.MIPStarRE.QPBT.DirectDegPoly params degree)
    (parameter : _root_.MIPStarRE.QPBT.DirectScalarQ params)
    (hne : _root_.MIPStarRE.QPBT.evalCoefficient coeffsA parameter ≠ _root_.MIPStarRE.QPBT.evalCoefficient coeffsB parameter) :
    _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction) coeffsA ≠
        _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction) coeffsB ∨
      _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction) coeffsA = none ∨
      _root_.MIPStarRE.QPBT.directEvalOpt line (line.base + parameter • line.direction) coeffsB = none := by
  generalize hreadA : _root_.MIPStarRE.QPBT.directEvalOpt line
    (line.base + parameter • line.direction) coeffsA = readA
  generalize hreadB : _root_.MIPStarRE.QPBT.directEvalOpt line
    (line.base + parameter • line.direction) coeffsB = readB
  cases readA with
  | none => exact Or.inr (Or.inl rfl)
  | some answerA =>
      cases readB with
      | none => exact Or.inr (Or.inr rfl)
      | some answerB =>
          apply Or.inl
          intro hread
          have hab : answerA = answerB := Option.some.inj hread
          apply hne
          calc
            _root_.MIPStarRE.QPBT.evalCoefficient coeffsA parameter = answerA :=
              _root_.MIPStarRE.QPBT.ExtendedLineGame.evalCoefficient_eq_of_directEvalOpt_affine_eq_some
                line coeffsA parameter answerA hreadA
            _ = answerB := hab
            _ = _root_.MIPStarRE.QPBT.evalCoefficient coeffsB parameter :=
              (_root_.MIPStarRE.QPBT.ExtendedLineGame.evalCoefficient_eq_of_directEvalOpt_affine_eq_some
                line coeffsB parameter answerB hreadB).symm
