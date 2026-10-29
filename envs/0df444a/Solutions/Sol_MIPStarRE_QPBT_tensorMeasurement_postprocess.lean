-- Prove2me | solution 1 for MIPStarRE.QPBT.tensorMeasurement_postprocess
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:32:14.369869+00:00
-- url     : https://prove2.me/submissions/69469242-526b-4d80-b1eb-ca450a092d61

-- Generated proof for MIPStarRE.QPBT.tensorMeasurement_postprocess.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Upstream

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-! # State-dependent distance calculus

This module records the consistency and state-dependent distance estimates used
throughout the quantum Pauli basis test. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

The operator-level inequalities they rest on live in
`MIPStarRE.QPBT.Games.DistanceTheorems.Calculus`.

## References

The source results run from blueprint `fact:agreement` through
`lem:close-strategies-have-close-values`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-461` and
`:531-540`. The observable conversion lemmas come from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:95-131`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution
    {FirstOutcome SecondOutcome FirstLabel SecondLabel FirstSpace SecondSpace : Type*}
    [Fintype FirstOutcome] [DecidableEq FirstOutcome]
    [Fintype SecondOutcome] [DecidableEq SecondOutcome]
    [Fintype FirstLabel] [DecidableEq FirstLabel]
    [Fintype SecondLabel] [DecidableEq SecondLabel]
    [Fintype FirstSpace] [DecidableEq FirstSpace]
    [Fintype SecondSpace] [DecidableEq SecondSpace]
    (firstMeas : _root_.LIDT.MIPStarRE.Quantum.Measurement FirstOutcome FirstSpace)
    (secondMeas : _root_.LIDT.MIPStarRE.Quantum.Measurement SecondOutcome SecondSpace)
    (firstMap : FirstOutcome → FirstLabel) (secondMap : SecondOutcome → SecondLabel) :
    _root_.MIPStarRE.QPBT.tensorMeasurement (firstMeas.postprocess firstMap) (secondMeas.postprocess secondMap) =
      (_root_.MIPStarRE.QPBT.tensorMeasurement firstMeas secondMeas).postprocess (Prod.map firstMap secondMap) := by
  apply _root_.LIDT.MIPStarRE.Quantum.Measurement.ext
  intro ⟨firstLabel, secondLabel⟩
  change _root_.MIPStarRE.QPBT.heteroKron
      (∑ first ∈ Finset.univ.filter (fun first => firstMap first = firstLabel),
        firstMeas.effect first)
      (∑ second ∈ Finset.univ.filter (fun second => secondMap second = secondLabel),
        secondMeas.effect second) =
    ∑ outcomes ∈ Finset.univ.filter
        (fun outcomes => Prod.map firstMap secondMap outcomes = (firstLabel, secondLabel)),
      _root_.MIPStarRE.QPBT.heteroKron (firstMeas.effect outcomes.1) (secondMeas.effect outcomes.2)
  rw [_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left]
  simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro first _
  by_cases hfirst : firstMap first = firstLabel <;> simp [hfirst]
