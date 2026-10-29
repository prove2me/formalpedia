-- Prove2me | solution 1 for MIPStarRE.QPBT.SubLineWitness.avgOver_conditionalLaw
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:47:23.15019+00:00
-- url     : https://prove2.me/submissions/1e37dca6-37c2-447e-9ba4-a86e06f19c39

-- Generated proof for MIPStarRE.QPBT.SubLineWitness.avgOver_conditionalLaw.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLines_Measurement
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Conditional extended-line measurements

This directly indexed auxiliary construction follows the first consistency
route for combined lines. The question carrier, completed answer alphabet,
and corrected error convention retain their existing meanings.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1118-1246`,
blueprint `lem:qld-4-13-established`.
See `docs/paper-gaps/qpbt_combined-lines-error-term.tex` and
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` for the remaining
comparison with the printed source theorem.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open scoped BigOperators Matrix MatrixOrder ComplexOrder

theorem solution {params : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (sublines : _root_.MIPStarRE.QPBT.SubLineWitness params) (quantity : _root_.MIPStarRE.QPBT.SubLineTriple params → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (sublines.D.map Prod.fst) (fun line =>
      _root_.LIDT.MIPStarRE.LDT.avgOver (sublines.conditionalLaw line) (fun sample => quantity sample.val)) =
        _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D quantity := by
  classical
  simp only [_root_.LIDT.MIPStarRE.LDT.avgOver, _root_.MIPStarRE.QPBT.SubLineWitness.conditionalLaw]
  calc
    (∑ line ∈ (sublines.D.map Prod.fst).support,
        (sublines.D.map Prod.fst).weight line *
          ∑ sample : sublines.Fiber line,
            (sublines.D.weight sample.val / (sublines.D.map Prod.fst).weight line) *
              quantity sample.val) =
        ∑ line ∈ (sublines.D.map Prod.fst).support,
          ∑ sample ∈ sublines.D.support.filter (fun sample => sample.1 = line),
            sublines.D.weight sample * quantity sample := by
      apply Finset.sum_congr rfl
      intro line _
      rw [Finset.mul_sum]
      trans ∑ sample : sublines.Fiber line, sublines.D.weight sample.val * quantity sample.val
      · apply Finset.sum_congr rfl
        intro sample _
        field_simp [(sublines.fiber_mass_pos line).ne']
        exact (div_eq_iff (sublines.fiber_mass_pos line).ne').mpr (by ring)
      · exact Finset.sum_coe_sort
          (sublines.D.support.filter (fun sample => sample.1 = line))
          (fun sample => sublines.D.weight sample * quantity sample)
    _ = ∑ sample ∈ sublines.D.support, sublines.D.weight sample * quantity sample := by
      exact Finset.sum_fiberwise_of_maps_to
        (fun sample hsample => Finset.mem_image.mpr ⟨sample, hsample, rfl⟩) _
