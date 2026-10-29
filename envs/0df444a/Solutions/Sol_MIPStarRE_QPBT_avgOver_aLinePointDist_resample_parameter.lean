-- Prove2me | solution 1 for MIPStarRE.QPBT.avgOver_aLinePointDist_resample_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:28:22.030062+00:00
-- url     : https://prove2.me/submissions/5570e566-c276-4c66-87b8-15e514955376

-- Generated proof for MIPStarRE.QPBT.avgOver_aLinePointDist_resample_parameter.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Questions
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineBlocks
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_map_lineRepMap_add_smul
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_prod

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineSupport.lean. -/
/-!
# Generating laws of the restricted line-point distributions

This module rewrites the two restricted line-point laws of
`def:ith-restricted-line` as push-forwards of a single uniformly sampled
low-degree vector conditioned on the coordinate-index fiber of its retained
scalar seed.  In that form the point block, the seed and the direction block
of the sampled vector are visibly the independent generating data of the
restricted law, which is the description used by the sampling procedure of the
sub-line lemma: there the projected pairs are built either from a direction
block inherited from the extended line or from freshly sampled data, and each
is asserted to follow a restricted law.

## References

The generating descriptions support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws themselves are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The coordinate-index event on a single uniform vector -/







/-! ## Canonical representatives are unchanged by the conditioning maps -/

/-- Two axis-line descriptions with the same seed and the same base agree:
the stored proof of `def:line-representative` invariance is a proposition and
carries no further data.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem lineDesc_axis_congr {L : _root_.MIPStarRE.QPBT.LdParams}
    {b b' : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L} {s : _root_.MIPStarRE.QPBT.ScalarQ L} (h : b = b')
    (hb : _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.chiIndex L s)) b = b)
    (hb' : _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.chiIndex L s)) b' = b') :
    _root_.MIPStarRE.QPBT.LineDesc.axis b s hb = _root_.MIPStarRE.QPBT.LineDesc.axis b' s hb' := by
  subst h
  rfl



/-- The axis-line decoder is unchanged by the axis conditioning map: the
canonical representative of `def:line-representative` is idempotent, so
decoding the conditioned vector and decoding the original vector agree.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem aLineDescOf_ldALineCL (L : _root_.MIPStarRE.QPBT.LdParams) (z : _root_.MIPStarRE.QPBT.LdSpace L) :
    _root_.MIPStarRE.QPBT.aLineDescOf L (_root_.MIPStarRE.QPBT.ldALineCL L z) = _root_.MIPStarRE.QPBT.aLineDescOf L z :=
  _root_.MIPStarRE.QPBT.lineDesc_axis_congr (_root_.MIPStarRE.QPBT.lineRepMap_apply_self _ _) _ _



/-! ## Generating laws of the restricted line-point distributions -/





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
# Axis line-point parameter resampling

This module records that a uniformly sampled point on an axis-parallel line
may be resampled by an independent uniform affine parameter without changing
the joint line-point expectation.

## References

The resampling is used at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:955`; the
axis line-point law is `def:line-point-dist` at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams)
    (value : (_root_.MIPStarRE.QPBT.LineDesc L × (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)) → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.aLinePointDist L) value =
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.aLinePointDist L) (fun sample =>
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ScalarQ L)) (fun param =>
        value (sample.1, sample.1.base + param • sample.1.direction))) := by
  classical
  unfold _root_.MIPStarRE.QPBT.aLinePointDist _root_.MIPStarRE.QPBT.clDistribution
  simp only [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map, _root_.MIPStarRE.QPBT.aLineDescOf_ldALineCL]
  have hblock := _root_.MIPStarRE.QPBT.uniformDistribution_map_equiv (_root_.MIPStarRE.QPBT.ldSpaceBlockEquiv L).symm
  rw [← hblock]
  simp only [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
  rw [_root_.MIPStarRE.QPBT.uniformDistribution_prod]
  simp only [_root_.MIPStarRE.QPBT.SandwichProduct.avgOver_distribution_prod]
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_comm, _root_.LIDT.MIPStarRE.LDT.avgOver_comm (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))]
  apply congrArg
  funext block
  let direction : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L :=
    _root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.chiIndex L block.1)
  change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)) (fun point =>
      value (_root_.MIPStarRE.QPBT.LineDesc.axis (_root_.MIPStarRE.QPBT.lineRepMap direction point) block.1
        (_root_.MIPStarRE.QPBT.lineRepMap_apply_self direction point), point)) =
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)) (fun point =>
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ScalarQ L)) (fun param =>
        value (_root_.MIPStarRE.QPBT.LineDesc.axis (_root_.MIPStarRE.QPBT.lineRepMap direction point) block.1
          (_root_.MIPStarRE.QPBT.lineRepMap_apply_self direction point),
          _root_.MIPStarRE.QPBT.lineRepMap direction point + param • direction)))
  have haxis := _root_.MIPStarRE.QPBT.avgOver_uniform_lineRepMap_resample_parameter direction
    (fun base point => value (_root_.MIPStarRE.QPBT.LineDesc.axis
      (_root_.MIPStarRE.QPBT.lineRepMap direction base) block.1
      (_root_.MIPStarRE.QPBT.lineRepMap_apply_self _ _), point))
  simpa only [_root_.MIPStarRE.QPBT.lineRepMap_apply_self] using haxis
