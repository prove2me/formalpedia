-- Prove2me | solution 1 for MIPStarRE.QPBT.subLineDist_map_fst
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:34:37.43297+00:00
-- url     : https://prove2.me/submissions/d94882d9-c346-4ca7-a137-3a4f8c0a90ed

-- Generated proof for MIPStarRE.QPBT.subLineDist_map_fst.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineConstruct
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_Distribution_bind_map
import Theorems.Thm_MIPStarRE_QPBT_Distribution_bind_uniform_fin_two
import Theorems.Thm_MIPStarRE_QPBT_subLineBranchDist_map_fst

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/DistributionAux.lean. -/
/-! # Operations on finite distributions

Finite distributions support products, convex mixtures, dependent binds,
normalized restrictions, and push-forwards.  Uniform laws are preserved by
bijections and balanced maps, their product projections are uniform, and
dependent uniform sampling agrees with push-forward from a product.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

















/-! ### Push-forwards of finite and uniform distributions

The results of this section are not named in the paper.  They record the
elementary behaviour of push-forwards of finite distributions, and of uniform
distributions on finite types, that the line-point samplers of the low-degree
game and the identification of question distributions with typed conditionally
linear distributions rely on.
-/





















/-! ## Elementary rewriting of finite distributions -/







/-! ## Reindexing a dependent mixture -/



/-- A dependent mixture depends on the mixed family only on the index
support.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.bind_congr_support {α β : Type*} [DecidableEq β]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν ν' : α → _root_.LIDT.MIPStarRE.LDT.Distribution β)
    (h : ∀ a ∈ μ.support, ν a = ν' a) :
    _root_.MIPStarRE.QPBT.Distribution.bind μ ν = _root_.MIPStarRE.QPBT.Distribution.bind μ ν' := by
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · change μ.support.biUnion (fun a => (ν a).support) =
      μ.support.biUnion (fun a => (ν' a).support)
    exact Finset.biUnion_congr rfl fun a ha => by rw [h a ha]
  · funext b
    exact Finset.sum_congr rfl fun a ha => by rw [h a ha]



/-! ## Associativity of dependent mixtures -/



/-! ## Products with an independent factor -/



/-! ## The equal two-term mixture as a uniform dependent mixture -/



/-! ## Averages of the distribution operations -/







end MIPStarRE.QPBT

/-!
# The sampling procedure of the sub-line lemma

This module carries out the sampling procedure of `lem:qld-sublines`.  A line
kind is drawn from the two kinds, an extended coordinate and an extended point
and direction are drawn uniformly, and two scalar seeds are drawn
independently in the coordinate-index fibers of the two coordinates that the
two source lines must carry.  The sampled triple consists of the axis or
diagonal line of the extended sample together with the two source lines
decoded from the two coordinate blocks of the extended point and direction and
from the two seeds.

The module records the elementary evaluations of that triple, the description
of the support of the resulting law, the three pointwise properties of a
sampled triple -- incidence of the two source blocks, compatibility of the
affine data, and closure of the axis branch -- and the identification of its
extended-line marginal.

## References

The construction is the proof of `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! ## The auxiliary randomness of one branch -/













/-! ## The sampled triple -/













/-! ## Elementary evaluations of the sampled triple -/













/-! ## The support of the sub-line law -/



/-! ## Pointwise properties of a sampled triple -/



















/-! ## Total mass and extended marginal -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (_root_.MIPStarRE.QPBT.subLineDist P).map Prod.fst =
      (_root_.MIPStarRE.QPBT.directLinePointDist P.extendedDirectLd).map Prod.fst := by
  classical
  have haxis : (_root_.MIPStarRE.QPBT.subLineBranchDist P .axis).map Prod.fst =
      (_root_.MIPStarRE.QPBT.directALinePointDist P.extendedDirectLd).map Prod.fst := by
    rw [_root_.MIPStarRE.QPBT.subLineBranchDist_map_fst, _root_.MIPStarRE.QPBT.directALinePointDist, _root_.MIPStarRE.QPBT.Distribution.map_map]
    rfl
  have hdiag : (_root_.MIPStarRE.QPBT.subLineBranchDist P .diagonal).map Prod.fst =
      (_root_.MIPStarRE.QPBT.directDLinePointDist P.extendedDirectLd).map Prod.fst := by
    rw [_root_.MIPStarRE.QPBT.subLineBranchDist_map_fst, _root_.MIPStarRE.QPBT.directDLinePointDist, _root_.MIPStarRE.QPBT.Distribution.map_map]
    rfl
  rw [_root_.MIPStarRE.QPBT.subLineDist, _root_.MIPStarRE.QPBT.Distribution.bind_map, _root_.MIPStarRE.QPBT.directLinePointDist,
    ← _root_.MIPStarRE.QPBT.Distribution.bind_uniform_fin_two, _root_.MIPStarRE.QPBT.Distribution.bind_map]
  refine _root_.MIPStarRE.QPBT.Distribution.bind_congr_support _ _ _ fun c _ => ?_
  fin_cases c
  · exact haxis
  · exact hdiag
