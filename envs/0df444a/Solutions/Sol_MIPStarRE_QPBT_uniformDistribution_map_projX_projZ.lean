-- Prove2me | solution 1 for MIPStarRE.QPBT.uniformDistribution_map_projX_projZ
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:28:22.178299+00:00
-- url     : https://prove2.me/submissions/89f03c29-1423-4482-aca8-324cee9b42d5

-- Generated proof for MIPStarRE.QPBT.uniformDistribution_map_projX_projZ.
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
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineExtended
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_prod

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineExtended.lean. -/
/-!
# Coordinate blocks of an extended point and of an extended direct sample

This module records the block decomposition used by the sampling procedure of
the sub-line lemma on the extended dimension.  A point of the extended space
is the tuple consisting of its two source point blocks and its two scalar
coordinates, and this decomposition is a bijection carrying the uniform law to
the uniform law; in particular the two source blocks of a uniform extended
point are independent and uniform.  The decomposition is linear, so it
commutes with the affine parameterization of a line, and it commutes with the
canonical identification of the extended scalar field with the source scalar
field.  The stored coordinate index of an extended direct sample splits along
the same three coordinate ranges.

## References

The decompositions support `lem:qld-sublines` in
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

/-! ## Linearity of the coordinate blocks -/









/-! ## The coordinate blocks of an extended point -/



/-- The first block of the decomposition is the `X` block. -/
theorem extendedPointBlockEquiv_projX (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (u : Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    (_root_.MIPStarRE.QPBT.extendedPointBlockEquiv P u).1.1 = _root_.MIPStarRE.QPBT.projX u := by
  funext i
  rfl

/-- The second block of the decomposition is the `Z` block. -/
theorem extendedPointBlockEquiv_projZ (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (u : Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) :
    (_root_.MIPStarRE.QPBT.extendedPointBlockEquiv P u).1.2 = _root_.MIPStarRE.QPBT.projZ u := by
  funext i
  rfl





/-- The block decomposition of an extended point carries the uniform law to
the uniform law.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_extendedPointBlockEquiv (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)).map
        (_root_.MIPStarRE.QPBT.extendedPointBlockEquiv P) =
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution
        (((Fin P.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) ×
            (Fin P.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)) ×
          (Fin 2 → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)) :=
  _root_.MIPStarRE.QPBT.uniformDistribution_map_equiv _



/-! ## Transport to the source scalar field -/





/-! ## The blocks of an extended direct sample -/



/-! ## Compatibility data read off the coordinate blocks -/





end

end MIPStarRE.QPBT

/-!
# Coordinate blocks of an extended point and of an extended direct sample

This module records the block decomposition used by the sampling procedure of
the sub-line lemma on the extended dimension.  A point of the extended space
is the tuple consisting of its two source point blocks and its two scalar
coordinates, and this decomposition is a bijection carrying the uniform law to
the uniform law; in particular the two source blocks of a uniform extended
point are independent and uniform.  The decomposition is linear, so it
commutes with the affine parameterization of a line, and it commutes with the
canonical identification of the extended scalar field with the source scalar
field.  The stored coordinate index of an extended direct sample splits along
the same three coordinate ranges.

## References

The decompositions support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate blocks are those of `def:combine-map`, blueprint lines
445--480, paper lines 970--989.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! ## Linearity of the coordinate blocks -/









/-! ## The coordinate blocks of an extended point -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)).map
        (fun u => (_root_.MIPStarRE.QPBT.projX u, _root_.MIPStarRE.QPBT.projZ u)) =
      _root_.MIPStarRE.QPBT.Distribution.prod
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)) := by
  have hfun :
      (fun u : Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd =>
          (_root_.MIPStarRE.QPBT.projX u, _root_.MIPStarRE.QPBT.projZ u)) =
        fun u => (_root_.MIPStarRE.QPBT.extendedPointBlockEquiv P u).1 := by
    funext u
    rw [Prod.ext_iff]
    exact ⟨(_root_.MIPStarRE.QPBT.extendedPointBlockEquiv_projX P u).symm,
      (_root_.MIPStarRE.QPBT.extendedPointBlockEquiv_projZ P u).symm⟩
  rw [hfun, ← _root_.MIPStarRE.QPBT.Distribution.map_map _ (_root_.MIPStarRE.QPBT.extendedPointBlockEquiv P) Prod.fst,
    _root_.MIPStarRE.QPBT.uniformDistribution_map_extendedPointBlockEquiv,
    _root_.MIPStarRE.QPBT.uniformDistribution_map_fst, _root_.MIPStarRE.QPBT.uniformDistribution_prod]
