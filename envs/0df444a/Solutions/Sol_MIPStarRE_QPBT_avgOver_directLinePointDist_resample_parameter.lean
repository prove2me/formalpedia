-- Prove2me | solution 1 for MIPStarRE.QPBT.avgOver_directLinePointDist_resample_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:28:21.836994+00:00
-- url     : https://prove2.me/submissions/9b0790f6-ee89-49c3-97ac-6be9ed46b243

-- Generated proof for MIPStarRE.QPBT.avgOver_directLinePointDist_resample_parameter.
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
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Questions
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_map_lineRepMap_add_smul
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_prod

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Combining/DirectLowDegree/Geometry.lean. -/
/-!
# Geometry for the directly indexed low-degree game

This module defines the parameters, line carrier, and line-point distributions
for the directly indexed low-degree game.

## References

The line-point distributions originate in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`.
The directly indexed repair is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section









instance instNonemptyFinM_1 (D : _root_.MIPStarRE.QPBT.DirectLdParams) : Nonempty (Fin D.m) := ⟨D.firstIndex⟩



















/-! ## Finite direct-line carrier -/

















































end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineUniform.lean. -/
/-!
# Uniform points of a line and the blocks of a coordinate direction

This module records the two elementary geometric inputs of the sampling
procedure of the sub-line lemma. First, for independent uniform inputs `u` in
the ambient coordinate space and `t` in the scalar field, the point
`lineRepMap v u + t • v` is uniform. This map on ambient-point--parameter pairs
has fibers of size `q`: for nonzero `v`, `u` varies over a coset of the span of
`v`, while its canonical representative and `t` are fixed; for zero `v`, `u`
is fixed and `t` is free. In averaged form this is the resampling identity used
by the line-point samplers: a quantity of the canonical representative and of
the point may equivalently be averaged over the point and an independent
uniform affine parameter along the direction. Second, the two coordinate
blocks of an elementary coordinate direction of the extended space are the
corresponding elementary direction of the source space in the block that
carries the coordinate, and zero in the other block and at the two scalar
coordinates.

## References

The two statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The canonical representative map is blueprint
`def:line-representative`; the coordinate blocks are those of
blueprint `def:combine-map`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The canonical representative for the zero direction -/



/-! ## Uniform points of a line -/



/-! ## Resampling a uniform point along its canonical line -/

/-- Finite-average form of the parameterization above: a uniformly random
point may be replaced by a fresh uniform affine parameter on the line through
its canonical representative, while the representative itself is kept in the
sampled value.  The zero direction is included, since the parameterization
has constant fibers there too.  This formalization-only identity is the
common core of the axis and diagonal line-point resampling identities used at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`;
the canonical representative map is blueprint `def:line-representative`. -/
theorem avgOver_uniform_lineRepMap_resample_parameter {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] {m : ℕ} (v : Fin m → K)
    (value : (Fin m → K) → (Fin m → K) → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin m → K))
        (fun point => value (_root_.MIPStarRE.QPBT.lineRepMap v point) point) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin m → K)) (fun point =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K) (fun param =>
          value (_root_.MIPStarRE.QPBT.lineRepMap v point) (_root_.MIPStarRE.QPBT.lineRepMap v point + param • v))) := by
  have hmap := _root_.MIPStarRE.QPBT.uniformDistribution_map_lineRepMap_add_smul v
  have havg := congrArg (fun dist => _root_.LIDT.MIPStarRE.LDT.avgOver dist
    (fun point => value (_root_.MIPStarRE.QPBT.lineRepMap v point) point)) hmap
  rw [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map, _root_.MIPStarRE.QPBT.uniformDistribution_prod,
    _root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod] at havg
  simpa only [_root_.MIPStarRE.QPBT.lineRepMap_add_smul, _root_.MIPStarRE.QPBT.lineRepMap_apply_self] using havg.symm

/-! ## Injectivity of the two block embeddings -/





/-! ## The blocks of an elementary coordinate direction -/

















/-! ## The coordinates occupied by the two blocks -/









/-! ## The blocks of a point of an extended line -/







/-! ## Incidence of the blocks of an extended line -/







end

end MIPStarRE.QPBT

/-!
# Consistency of the extended-line measurements

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

theorem solution (params : _root_.MIPStarRE.QPBT.DirectLdParams)
    (quantity : _root_.MIPStarRE.QPBT.DirectLineDesc params × (Fin params.m → _root_.MIPStarRE.QPBT.DirectScalarQ params) → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.directLinePointDist params) quantity =
      _root_.LIDT.MIPStarRE.LDT.avgOver ((_root_.MIPStarRE.QPBT.directLinePointDist params).map Prod.fst) (fun line =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ params)) (fun parameter =>
          quantity (line, line.base + parameter • line.direction))) := by
  classical
  rw [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map, _root_.MIPStarRE.QPBT.directLinePointDist, _root_.MIPStarRE.QPBT.avgOver_mix, _root_.MIPStarRE.QPBT.avgOver_mix]
  congr 1
  · congr 1
    unfold _root_.MIPStarRE.QPBT.directALinePointDist
    simp only [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
    rw [← _root_.MIPStarRE.QPBT.uniformDistribution_map_equiv (_root_.MIPStarRE.QPBT.directLdSpaceIndexEquiv params).symm]
    simp only [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map, _root_.MIPStarRE.QPBT.uniformDistribution_prod,
      _root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod]
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro index
    conv_lhs => rw [_root_.LIDT.MIPStarRE.LDT.avgOver_comm]
    conv_rhs => rw [_root_.LIDT.MIPStarRE.LDT.avgOver_comm]
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro direction
    simpa only [_root_.MIPStarRE.QPBT.directLdSpaceIndexEquiv, Equiv.coe_fn_symm_mk, _root_.MIPStarRE.QPBT.directALineDescOf,
      _root_.MIPStarRE.QPBT.DirectLineDesc.base, _root_.MIPStarRE.QPBT.DirectLineDesc.direction, _root_.MIPStarRE.QPBT.lineRepMap_apply_self] using
      _root_.MIPStarRE.QPBT.avgOver_uniform_lineRepMap_resample_parameter (_root_.MIPStarRE.QPBT.coordinateDirection index)
        (fun base point => quantity
          (.axis (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.coordinateDirection index) base) index
            (_root_.MIPStarRE.QPBT.lineRepMap_apply_self _ _), point))
  · congr 1
    unfold _root_.MIPStarRE.QPBT.directDLinePointDist
    simp only [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
    rw [← _root_.MIPStarRE.QPBT.uniformDistribution_map_equiv (_root_.MIPStarRE.QPBT.directLdSpaceIndexEquiv params).symm]
    simp only [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map, _root_.MIPStarRE.QPBT.uniformDistribution_prod,
      _root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod]
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro index
    conv_lhs => rw [_root_.LIDT.MIPStarRE.LDT.avgOver_comm]
    conv_rhs => rw [_root_.LIDT.MIPStarRE.LDT.avgOver_comm]
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
    intro direction
    simpa only [_root_.MIPStarRE.QPBT.directLdSpaceIndexEquiv, Equiv.coe_fn_symm_mk, _root_.MIPStarRE.QPBT.directDLineDescOf,
      _root_.MIPStarRE.QPBT.DirectLineDesc.base, _root_.MIPStarRE.QPBT.DirectLineDesc.direction, _root_.MIPStarRE.QPBT.lineRepMap_apply_self] using
      _root_.MIPStarRE.QPBT.avgOver_uniform_lineRepMap_resample_parameter (_root_.MIPStarRE.QPBT.directPrefixProjection index direction)
        (fun base point => quantity
          (.diagonal (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.directPrefixProjection index direction) base) index
            (_root_.MIPStarRE.QPBT.directPrefixProjection index direction) (_root_.MIPStarRE.QPBT.lineRepMap_apply_self _ _)
            (by intro coordinate hbefore; simp [_root_.MIPStarRE.QPBT.directPrefixProjection, hbefore]), point))
