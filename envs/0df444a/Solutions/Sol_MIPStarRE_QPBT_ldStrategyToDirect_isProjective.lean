-- Prove2me | solution 1 for MIPStarRE.QPBT.ldStrategyToDirect_isProjective
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:32:45.094973+00:00
-- url     : https://prove2.me/submissions/2981f253-e114-4506-8221-d26ec4645ee1

-- Generated proof for MIPStarRE.QPBT.ldStrategyToDirect_isProjective.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_SeedFiber
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_blockDiagonalMeasurement_isProjective

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/SeedFiber.lean. -/
/-!
# Seed-fiber dilation for the directly indexed low-degree game

This module dilates a seed-indexed low-degree strategy by a maximally
correlated residue register.  Block-diagonal projective measurements retain
arbitrary dependence on the seed within each `chiIndex` fiber.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Projective block measurements -/





/-- Relabeling a projective matrix measurement preserves projectivity. -/
theorem matrixMeasurementTransport_isProjective
    {alpha beta iota : Type*}
    [Fintype alpha] [Fintype beta] [Fintype iota] [DecidableEq iota]
    (e : alpha ≃ beta) (M : _root_.LIDT.MIPStarRE.Quantum.Measurement alpha iota)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (_root_.MIPStarRE.QPBT.matrixMeasurementTransport e M) :=
  fun b => hM (e.symm b)







/-! ## The correlated residue state -/









/-! ## From the seed-indexed game to the direct game -/















end

end MIPStarRE.QPBT

/-!
# Seed-fiber dilation for the directly indexed low-degree game

This module dilates a seed-indexed low-degree strategy by a maximally
correlated residue register.  Block-diagonal projective measurements retain
arbitrary dependence on the seed within each `chiIndex` fiber.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



/-! ## Projective block measurements -/













/-! ## The correlated residue state -/









/-! ## From the seed-indexed game to the direct game -/

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.ldGame L)) (hS : S.IsProjective) :
    (_root_.MIPStarRE.QPBT.ldStrategyToDirect L S).IsProjective := by
  constructor
  · intro q
    apply _root_.MIPStarRE.QPBT.blockDiagonalMeasurement_isProjective
    intro residue
    apply _root_.MIPStarRE.QPBT.matrixMeasurementTransport_isProjective
    exact hS.1 (_root_.MIPStarRE.QPBT.seededLdQuestion L q residue)
  · intro q
    apply _root_.MIPStarRE.QPBT.blockDiagonalMeasurement_isProjective
    intro residue
    apply _root_.MIPStarRE.QPBT.matrixMeasurementTransport_isProjective
    exact hS.2 (_root_.MIPStarRE.QPBT.seededLdQuestion L q residue)
