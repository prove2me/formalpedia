-- Prove2me | solution 1 for MIPStarRE.QPBT.subLineBranchDist_map_fst
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:28:21.954531+00:00
-- url     : https://prove2.me/submissions/013778d5-6858-4a68-8383-9554c63ed2d7

-- Generated proof for MIPStarRE.QPBT.subLineBranchDist_map_fst.
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
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineBranch
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineConstruct
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineSeed
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_Distribution_bind_map
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_isProbability
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_map_eq_bind
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_map_fst
import Theorems.Thm_MIPStarRE_QPBT_Distribution_restrict_isProbability
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_prod

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineConstruct.lean. -/
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

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The auxiliary randomness of one branch -/







/-- Every seed law of a source line has total mass one. -/
theorem subLineSeedDist_isProbability (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (i : Fin P.m) :
    (_root_.MIPStarRE.QPBT.subLineSeedDist P i).IsProbability := by
  rw [_root_.MIPStarRE.QPBT.subLineSeedDist]
  exact _root_.MIPStarRE.QPBT.Distribution.restrict_isProbability _ _
    (_root_.MIPStarRE.QPBT.ldSeedIndexEvent_positive P.toLdParams i)





/-! ## The sampled triple -/













/-! ## Elementary evaluations of the sampled triple -/













/-! ## The support of the sub-line law -/



/-! ## Pointwise properties of a sampled triple -/



















/-! ## Total mass and extended marginal -/









end

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

/- Source helpers from QPBT/Games/DistributionMarginals.lean. -/
/-!
# Products, marginals, and restrictions of finite distributions

The finite-distribution push-forward calculus gives corresponding identities
for probability mass functions and for projections transported across finite
equivalences.  These forms are used by the directly indexed low-degree
line-point laws and by the correspondence between the seed-indexed and directly
indexed question distributions. Products can be expressed as dependent mixtures, and
conditioning on an event of one factor preserves the independence of the other.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT





/-! ## Nonemptiness of the support of a probability law -/



/-! ## Push-forward of one factor of a product -/



/-! ## The first marginal of a product -/



/-- Reading a function of the first factor of a product whose second factor is
a probability law is reading it on the first factor.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.prod_map_of_fst {α β γ : Type*} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : _root_.LIDT.MIPStarRE.LDT.Distribution β)
    (hν : ν.IsProbability) (h : α → γ) :
    (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).map (fun w => h w.1) = μ.map h := by
  rw [← _root_.MIPStarRE.QPBT.Distribution.map_map (_root_.MIPStarRE.QPBT.Distribution.prod μ ν) Prod.fst h,
    _root_.MIPStarRE.QPBT.Distribution.prod_map_fst μ ν hν]

/-! ## A product as a dependent mixture -/



/-! ## The support and the weight of a product -/





/-! ## Push-forward along a bijection -/



/-! ## Push-forward of the second factor of a product -/



/-! ## Uniform laws on products -/





/-! ## Conditioning one factor of a product -/







/-! ## Conditioning the first factor of a product -/







/-! ## Restriction of a push-forward -/



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

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind) :
    (_root_.MIPStarRE.QPBT.subLineBranchDist P kind).map Prod.fst =
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)).map
        (_root_.MIPStarRE.QPBT.subLineExtLineOfSample P kind) := by
  classical
  have hstep1 : (_root_.MIPStarRE.QPBT.subLineBranchDist P kind).map Prod.fst =
      _root_.MIPStarRE.QPBT.Distribution.bind (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin (2 * P.m + 2))) fun k =>
        (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.SubLinePointDir P))
            (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
              (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k)))).map
          fun w => _root_.MIPStarRE.QPBT.subLineExtLineOfSample P kind ⟨w.1.1, k, w.1.2⟩ := by
    rw [_root_.MIPStarRE.QPBT.subLineBranchDist, _root_.MIPStarRE.QPBT.Distribution.map_map, _root_.MIPStarRE.QPBT.subLineSamplingDist,
      _root_.MIPStarRE.QPBT.Distribution.bind_map]
    refine _root_.MIPStarRE.QPBT.Distribution.bind_congr_support _ _ _ fun k _ => ?_
    rw [_root_.MIPStarRE.QPBT.Distribution.map_map]
    rfl
  have hstep2 : ∀ k : Fin (2 * P.m + 2),
      (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.SubLinePointDir P))
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
            (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k)))).map
        (fun w => _root_.MIPStarRE.QPBT.subLineExtLineOfSample P kind ⟨w.1.1, k, w.1.2⟩) =
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.SubLinePointDir P)).map
        (fun pd => _root_.MIPStarRE.QPBT.subLineExtLineOfSample P kind ⟨pd.1, k, pd.2⟩) := by
    intro k
    exact _root_.MIPStarRE.QPBT.Distribution.prod_map_of_fst
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.SubLinePointDir P))
      (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
        (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k)))
      (_root_.MIPStarRE.QPBT.Distribution.prod_isProbability
        (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
        (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k))
        (_root_.MIPStarRE.QPBT.subLineSeedDist_isProbability P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
        (_root_.MIPStarRE.QPBT.subLineSeedDist_isProbability P (_root_.MIPStarRE.QPBT.subLineZIndex P k)))
      (fun pd => _root_.MIPStarRE.QPBT.subLineExtLineOfSample P kind ⟨pd.1, k, pd.2⟩)
  have hstep3 :
      _root_.MIPStarRE.QPBT.Distribution.bind (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin (2 * P.m + 2))) (fun k =>
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.SubLinePointDir P)).map
          (fun pd => _root_.MIPStarRE.QPBT.subLineExtLineOfSample P kind ⟨pd.1, k, pd.2⟩)) =
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin (2 * P.m + 2) × _root_.MIPStarRE.QPBT.SubLinePointDir P)).map
        (fun w => _root_.MIPStarRE.QPBT.subLineExtLineOfSample P kind ⟨w.2.1, w.1, w.2.2⟩) := by
    rw [_root_.MIPStarRE.QPBT.uniformDistribution_prod (Fin (2 * P.m + 2)) (_root_.MIPStarRE.QPBT.SubLinePointDir P)]
    exact (_root_.MIPStarRE.QPBT.Distribution.prod_map_eq_bind
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin (2 * P.m + 2)))
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.SubLinePointDir P))
      (fun w => _root_.MIPStarRE.QPBT.subLineExtLineOfSample P kind ⟨w.2.1, w.1, w.2.2⟩)).symm
  have hstep4 :
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin (2 * P.m + 2) × _root_.MIPStarRE.QPBT.SubLinePointDir P)).map
        (fun w => _root_.MIPStarRE.QPBT.subLineExtLineOfSample P kind ⟨w.2.1, w.1, w.2.2⟩) =
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd)).map
        (_root_.MIPStarRE.QPBT.subLineExtLineOfSample P kind) := by
    rw [← _root_.MIPStarRE.QPBT.uniformDistribution_map_equiv (subLineSampleEquiv P),
      _root_.MIPStarRE.QPBT.Distribution.map_map]
    rfl
  rw [hstep1, _root_.MIPStarRE.QPBT.Distribution.bind_congr_support _ _ _ (fun k _ => hstep2 k),
    hstep3, hstep4]
