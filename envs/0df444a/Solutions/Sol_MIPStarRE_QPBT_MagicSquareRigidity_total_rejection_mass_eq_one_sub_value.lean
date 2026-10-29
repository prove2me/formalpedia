-- Prove2me | solution 1 for MIPStarRE.QPBT.MagicSquareRigidity.total_rejection_mass_eq_one_sub_value
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:27:30.99012+00:00
-- url     : https://prove2.me/submissions/04c8084c-76c7-44ad-9209-3ca180da67bc

-- Generated proof for MIPStarRE.QPBT.MagicSquareRigidity.total_rejection_mass_eq_one_sub_value.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_Relations
import Theorems.Thm_MIPStarRE_QPBT_outcomeWeight_sum_eq_one

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Relations.lean. -/
/-!
# Magic Square value-to-parity relations

This file extracts the elementary probability relations used at the start of
the Magic Square rigidity argument.  A strategy of value at least `1 - ε` has
total rejection mass at most `ε`.  Since the question distribution is
supported on at most 36 directed incidences, the rejection mass at each
incidence is at most `36 * ε`.  This controls malformed answers, consistency
of the two reported bits at every cell, and the parity product on each of the
six row or column constraints.

The arguments apply to arbitrary finite POVMs.  In particular, malformed
answers remain in the event masses when `msBitOrZero` and
`constraintBitOrZero` turn the common answer alphabet into binary outcomes.

## References

The Magic Square game is defined in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`
and blueprint `def:ms-game`.  These relations are the
probabilistic input to the rigidity result cited at paper lines 612-652 from
Coladangelo--Stark, Theorem 6.9.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## The directed incidence distribution -/













/-! ## Rejection mass from the game value -/











/-- Acceptance and rejection partition the conditioned answer mass. -/
theorem acceptance_mass_add_rejection_mass (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) (x y : _root_.MIPStarRE.QPBT.MsType) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.acceptanceMass S x y + _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S x y = 1 := by
  rw [← show (∑ a : _root_.MIPStarRE.QPBT.MsAnswer, ∑ b : _root_.MIPStarRE.QPBT.MsAnswer, _root_.MIPStarRE.QPBT.outcomeWeight S x y a b) = 1 by
    exact _root_.MIPStarRE.QPBT.outcomeWeight_sum_eq_one S x y]
  unfold _root_.MIPStarRE.QPBT.MagicSquareRigidity.acceptanceMass _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass _root_.MIPStarRE.QPBT.outcomeEventWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  cases h : _root_.MIPStarRE.QPBT.msWinPredicate x y a b <;> simp [h]

/-- The strategy value is the average conditioned acceptance mass. -/
theorem strategy_value_eq_acceptance_mass (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) :
    S.value = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty) fun xy =>
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.acceptanceMass S xy.1 xy.2 := by
  unfold _root_.MIPStarRE.QPBT.Strategy.value _root_.MIPStarRE.QPBT.MagicSquareRigidity.acceptanceMass _root_.MIPStarRE.QPBT.outcomeEventWeight _root_.MIPStarRE.QPBT.msGame
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro xy
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  cases h : _root_.MIPStarRE.QPBT.msWinPredicate xy.1 xy.2 a b <;> simp [h]















/-! ## Malformed answers and cell consistency -/























































/-! ## Row and column parity products -/





































end

end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# Magic Square value-to-parity relations

This file extracts the elementary probability relations used at the start of
the Magic Square rigidity argument.  A strategy of value at least `1 - ε` has
total rejection mass at most `ε`.  Since the question distribution is
supported on at most 36 directed incidences, the rejection mass at each
incidence is at most `36 * ε`.  This controls malformed answers, consistency
of the two reported bits at every cell, and the parity product on each of the
six row or column constraints.

The arguments apply to arbitrary finite POVMs.  In particular, malformed
answers remain in the event masses when `msBitOrZero` and
`constraintBitOrZero` turn the common answer alphabet into binary outcomes.

## References

The Magic Square game is defined in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`
and blueprint `def:ms-game`.  These relations are the
probabilistic input to the rigidity result cited at paper lines 612-652 from
Coladangelo--Stark, Theorem 6.9.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum



/-! ## The directed incidence distribution -/













/-! ## Rejection mass from the game value -/

theorem solution (S : _root_.MIPStarRE.QPBT.Strategy _root_.MIPStarRE.QPBT.msGame) :
    _root_.MIPStarRE.QPBT.MagicSquareRigidity.totalRejectionMass S = 1 - S.value := by
  rw [show S.value = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty) (fun xy =>
      _root_.MIPStarRE.QPBT.MagicSquareRigidity.acceptanceMass S xy.1 xy.2) by exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.strategy_value_eq_acceptance_mass S]
  unfold _root_.MIPStarRE.QPBT.MagicSquareRigidity.totalRejectionMass
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty) (fun xy =>
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S xy.1 xy.2) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty) (fun xy =>
          1 - _root_.MIPStarRE.QPBT.MagicSquareRigidity.acceptanceMass S xy.1 xy.2) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      intro xy
      linarith [show _root_.MIPStarRE.QPBT.MagicSquareRigidity.acceptanceMass S xy.1 xy.2 + _root_.MIPStarRE.QPBT.MagicSquareRigidity.rejectionMass S xy.1 xy.2 = 1 by
        exact _root_.MIPStarRE.QPBT.MagicSquareRigidity.acceptance_mass_add_rejection_mass S xy.1 xy.2]
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty) (fun _ => 1) -
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty) (fun xy =>
          _root_.MIPStarRE.QPBT.MagicSquareRigidity.acceptanceMass S xy.1 xy.2) := _root_.LIDT.MIPStarRE.LDT.avgOver_sub _ _ _
    _ = 1 - _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty) (fun xy =>
        _root_.MIPStarRE.QPBT.MagicSquareRigidity.acceptanceMass S xy.1 xy.2) := by
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _ (by
        unfold _root_.MIPStarRE.QPBT.graphDistribution
        apply _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset_isProbability
        refine ⟨(.constraint 0, .var (_root_.MIPStarRE.QPBT.msConstraintVars 0 0)), ?_⟩
        simp [_root_.MIPStarRE.QPBT.msEdges])]
