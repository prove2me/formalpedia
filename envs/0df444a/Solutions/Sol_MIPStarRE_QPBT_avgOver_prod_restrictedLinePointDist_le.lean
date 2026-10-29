-- Prove2me | solution 1 for MIPStarRE.QPBT.avgOver_prod_restrictedLinePointDist_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:16:53.065885+00:00
-- url     : https://prove2.me/submissions/59fd1358-502e-425e-9860-d6d2255e6b09

-- Generated proof for MIPStarRE.QPBT.avgOver_prod_restrictedLinePointDist_le.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_avgOver_restrictedLinePointDist_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Error inflation of restricted line-point averages

This module records how a nonnegative average over the line-point distribution
transfers to one restricted component.  The line-point law places weight
`1 / 2` on each of its two kinds and, inside each kind, weight `1 / m` on each
coordinate index, so every restricted component carries mixture weight
`1 / (2 m)` and a nonnegative average inflates by at most `2 m`.

## References

The estimates are items 1 and 2 of blueprint
`lem:restricted-line-mixture-bounds`, formalizing the unlabelled estimates at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement



/-! ## Inflation of a restricted line-point average -/

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (f : ((_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) ×
      (_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))) → ℝ)
    (hf : ∀ sample, 0 ≤ f sample) (kindX kindZ : _root_.MIPStarRE.QPBT.LineKind) (i j : Fin P.m) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kindX i)
        (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kindZ j)) f ≤
      4 * (P.m : ℝ) ^ 2 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.prod
        (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)) f := by
  classical
  have hfactor : (0 : ℝ) ≤ 2 * (P.m : ℝ) := by positivity
  rw [_root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod, _root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod]
  have hinner : ∀ s1 : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P),
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kindZ j) (fun s2 => f (s1, s2)) ≤
        2 * (P.m : ℝ) *
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) (fun s2 => f (s1, s2)) :=
    fun s1 => _root_.MIPStarRE.QPBT.avgOver_restrictedLinePointDist_le
      (fun s2 => f (s1, s2)) (fun s2 => hf (s1, s2)) kindZ j
  calc _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kindX i)
        (fun s1 => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kindZ j)
          (fun s2 => f (s1, s2)))
      ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kindX i)
          (fun s1 => 2 * (P.m : ℝ) *
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) (fun s2 => f (s1, s2))) :=
        _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ hinner
    _ = 2 * (P.m : ℝ) * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kindX i)
          (fun s1 => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
            (fun s2 => f (s1, s2))) := _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul _ _ _
    _ ≤ 2 * (P.m : ℝ) * (2 * (P.m : ℝ) *
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
            (fun s1 => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
              (fun s2 => f (s1, s2)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hfactor
        exact _root_.MIPStarRE.QPBT.avgOver_restrictedLinePointDist_le
          (fun s1 => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
            (fun s2 => f (s1, s2)))
          (fun s1 => _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg _ _ fun s2 => hf (s1, s2)) kindX i
    _ = 4 * (P.m : ℝ) ^ 2 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
          (fun s1 => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams)
            (fun s2 => f (s1, s2))) := by ring
