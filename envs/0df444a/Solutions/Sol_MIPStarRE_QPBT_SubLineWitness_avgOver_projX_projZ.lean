-- Prove2me | solution 1 for MIPStarRE.QPBT.SubLineWitness.avgOver_projX_projZ
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:16:02.577991+00:00
-- url     : https://prove2.me/submissions/cf35dd76-c9d5-4a05-937d-b98ad4caeda5

-- Generated proof for MIPStarRE.QPBT.SubLineWitness.avgOver_projX_projZ.
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
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineTransport
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_avgOver_directLinePointDist_line_add_smul
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_map_projX_projZ
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_prod

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineTransport.lean. -/
/-!
# Uniformity under the identification of the two scalar fields

The extended line of the sub-line construction lives over the scalar field of
the directly indexed extended game, while the two source lines live over the
scalar field of the Pauli basis test.  The two fields are identified
coordinatewise by a field isomorphism, so that identification is a bijection
of the coordinate spaces and therefore carries uniform laws to uniform laws.
This module records that transport for a whole extended point and for the two
source blocks of an extended point, and it records the resampling rule that
reading a function at the point of a uniformly random affine parameter on the
line through the canonical representative of a uniformly random point is the
same as reading that function at a uniformly random point.

## References

The statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate blocks are those of `def:combine-map`, blueprint lines
445--480, paper lines 970--989.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The identification of the two scalar fields as a bijection -/









/-! ## Transport of the uniform laws -/





/-- The two source blocks of a uniformly random extended point, read in the
source scalar field, are independent and uniformly random.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_projX_projZ_pauli (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)).map
        (fun u => (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P u),
          _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P u))) =
      _root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) := by
  classical
  have hfun :
      (fun u : Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd =>
          (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P u), _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P u))) =
        fun u => (Equiv.prodCongr (_root_.MIPStarRE.QPBT.directBlockToPauliEquiv P)
          (_root_.MIPStarRE.QPBT.directBlockToPauliEquiv P)) (_root_.MIPStarRE.QPBT.projX u, _root_.MIPStarRE.QPBT.projZ u) := rfl
  rw [hfun, ← _root_.MIPStarRE.QPBT.Distribution.map_map _ (fun u => (_root_.MIPStarRE.QPBT.projX u, _root_.MIPStarRE.QPBT.projZ u)),
    _root_.MIPStarRE.QPBT.uniformDistribution_map_projX_projZ, ← _root_.MIPStarRE.QPBT.uniformDistribution_prod,
    _root_.MIPStarRE.QPBT.uniformDistribution_map_equiv, _root_.MIPStarRE.QPBT.uniformDistribution_prod]

/-! ## Resampling a uniform point along a line -/



end

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

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (sublines : _root_.MIPStarRE.QPBT.SubLineWitness P)
    (f : ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (fun sample =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
          (fun t =>
            f (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
                (sample.1.base + t • sample.1.direction)),
              _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
                (sample.1.base + t • sample.1.direction))))) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
        ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))) f := by
  classical
  have hmarginal :
      _root_.LIDT.MIPStarRE.LDT.avgOver sublines.D (fun sample =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
            (fun t => f (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
                (sample.1.base + t • sample.1.direction)),
              _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
                (sample.1.base + t • sample.1.direction))))) =
        _root_.LIDT.MIPStarRE.LDT.avgOver ((_root_.MIPStarRE.QPBT.directLinePointDist P.extendedDirectLd).map Prod.fst)
          (fun line =>
            _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
              (fun t => f (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
                  (line.base + t • line.direction)),
                _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
                  (line.base + t • line.direction))))) := by
    rw [← sublines.extended_marginal, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
  refine hmarginal.trans ?_
  refine (_root_.MIPStarRE.QPBT.avgOver_directLinePointDist_line_add_smul P.extendedDirectLd
    (fun u => f (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P u),
      _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P u)))).trans ?_
  rw [_root_.MIPStarRE.QPBT.uniformDistribution_prod, ← _root_.MIPStarRE.QPBT.uniformDistribution_map_projX_projZ_pauli,
    _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
