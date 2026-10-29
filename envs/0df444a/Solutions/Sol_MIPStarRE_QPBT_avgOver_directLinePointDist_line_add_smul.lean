-- Prove2me | solution 1 for MIPStarRE.QPBT.avgOver_directLinePointDist_line_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:12:24.298499+00:00
-- url     : https://prove2.me/submissions/43cf8e20-1847-420d-8f56-7c62c9aecbfc

-- Generated proof for MIPStarRE.QPBT.avgOver_directLinePointDist_line_add_smul.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_avgOver_mix
import Theorems.Thm_MIPStarRE_QPBT_avgOver_uniform_directLdSpace_line_add_smul

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# A uniform point of the extended space from the sub-line law

The first scalar estimate in the combining argument samples an extended line
from the directly indexed sub-line witness and then a uniform affine parameter.
This module records that the resulting extended point is uniform and hence
that its two source coordinate blocks are independent uniform points.
This is an auxiliary law. Transport to the source's seed-indexed extended
distribution remains open, as recorded in
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`.

## References

These statements support `lem:claim-17-1` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`.  The paper uses this sampling
fact at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1159-1166`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (g : (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver ((_root_.MIPStarRE.QPBT.directLinePointDist D).map Prod.fst) (fun line =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun t =>
          g (line.base + t • line.direction))) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) g := by
  classical
  have haxis :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.directALinePointDist D) (fun sample =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun t =>
            g (sample.1.base + t • sample.1.direction))) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) g := by
    rw [_root_.MIPStarRE.QPBT.directALinePointDist, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
    exact _root_.MIPStarRE.QPBT.avgOver_uniform_directLdSpace_line_add_smul D
      (fun w => _root_.MIPStarRE.QPBT.coordinateDirection w.1) g
  have hdiag :
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.directDLinePointDist D) (fun sample =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun t =>
            g (sample.1.base + t • sample.1.direction))) =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) g := by
    rw [_root_.MIPStarRE.QPBT.directDLinePointDist, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
    exact _root_.MIPStarRE.QPBT.avgOver_uniform_directLdSpace_line_add_smul D
      (fun w => _root_.MIPStarRE.QPBT.directPrefixProjection w.1 w.2) g
  rw [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map, _root_.MIPStarRE.QPBT.directLinePointDist,
    _root_.MIPStarRE.QPBT.WinImplications.avgOver_mix, haxis, hdiag]
  ring
