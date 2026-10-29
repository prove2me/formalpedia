-- Prove2me | solution 1 for MIPStarRE.QPBT.subLineBranchSamplingData_map_joint
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:34:37.828989+00:00
-- url     : https://prove2.me/submissions/560b6b47-47dc-458d-9ec2-8493c22a7df9

-- Generated proof for MIPStarRE.QPBT.subLineBranchSamplingData_map_joint.
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
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineBlocks
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineBranch
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineConstruct
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineSeed
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineTransport
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_Distribution_map_bijective_eq
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_map_eq_bind
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_map_left
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_map_right
import Theorems.Thm_MIPStarRE_QPBT_lineRepMap_projX_subLineExtLine_point
import Theorems.Thm_MIPStarRE_QPBT_lineRepMap_projZ_subLineExtLine_point
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_map_lineRepMap_add_smul
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_map_projX_projZ
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













/-! ## The sampled triple -/













/-! ## Elementary evaluations of the sampled triple -/



/-- The direction of the extended line of a branch is the branch direction. -/
theorem subLineExtLine_direction (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P) :
    (_root_.MIPStarRE.QPBT.subLineExtLine P kind k w).direction =
      _root_.MIPStarRE.QPBT.subLineExtDirection P kind k w.1.2 := by
  cases kind <;> rfl

/-- The base of the extended line of a branch is the canonical representative
of the drawn point in the branch direction. -/
theorem subLineExtLine_base (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P) :
    (_root_.MIPStarRE.QPBT.subLineExtLine P kind k w).base =
      _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k w.1.2) w.1.1 := by
  cases kind <;> rfl







/-! ## The support of the sub-line law -/



/-! ## Pointwise properties of a sampled triple -/



















/-! ## Total mass and extended marginal -/









end

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

/-- Two diagonal-line descriptions with the same seed, the same base and the
same direction agree: the stored proofs of `def:line-representative`
invariance and of the prefix-zero condition are propositions and carry no
further data.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem lineDesc_diagonal_congr {L : _root_.MIPStarRE.QPBT.LdParams}
    {b b' d d' : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L} {s : _root_.MIPStarRE.QPBT.ScalarQ L}
    (hb : b = b') (hd : d = d')
    (h1 : _root_.MIPStarRE.QPBT.lineRepMap d b = b)
    (h2 : ∀ j : Fin L.m, j.val < (_root_.MIPStarRE.QPBT.chiIndex L s).val → d j = 0)
    (h1' : _root_.MIPStarRE.QPBT.lineRepMap d' b' = b')
    (h2' : ∀ j : Fin L.m, j.val < (_root_.MIPStarRE.QPBT.chiIndex L s).val → d' j = 0) :
    _root_.MIPStarRE.QPBT.LineDesc.diagonal b s d h1 h2 = _root_.MIPStarRE.QPBT.LineDesc.diagonal b' s d' h1' h2' := by
  subst hb
  subst hd
  rfl





/-! ## Generating laws of the restricted line-point distributions -/





end

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

/-- Reading a function at the point of a uniformly random affine parameter on
the line through the canonical representative, in a fixed direction, of a
uniformly random point is the same as reading that function at a uniformly
random point.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_map_lineRepMap_add_smul_comp {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] {m : ℕ} {γ : Type*} [DecidableEq γ]
    (v : Fin m → K) (g : (Fin m → K) → γ) :
    (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin m → K))
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution K)).map
        (fun w => g (_root_.MIPStarRE.QPBT.lineRepMap v w.1 + w.2 • v)) =
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin m → K)).map g := by
  classical
  rw [← _root_.MIPStarRE.QPBT.uniformDistribution_prod,
    ← _root_.MIPStarRE.QPBT.Distribution.map_map _ (fun w : (Fin m → K) × K =>
      _root_.MIPStarRE.QPBT.lineRepMap v w.1 + w.2 • v) g,
    _root_.MIPStarRE.QPBT.uniformDistribution_map_lineRepMap_add_smul]

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





/-! ## A product as a dependent mixture -/



/-! ## The support and the weight of a product -/

/-- The support of a product law is the product of the supports.  Blueprint
`def:line-point-dist`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/
theorem Distribution.prod_support {α β : Type*} [DecidableEq α]
    [DecidableEq β] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : _root_.LIDT.MIPStarRE.LDT.Distribution β) :
    (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).support = μ.support ×ˢ ν.support := rfl

/-- The weight of a product law is the product of the weights.  Blueprint
`def:line-point-dist`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/
theorem Distribution.prod_weight {α β : Type*} [DecidableEq α]
    [DecidableEq β] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : _root_.LIDT.MIPStarRE.LDT.Distribution β) (w : α × β) :
    (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).weight w = μ.weight w.1 * ν.weight w.2 := rfl

/-! ## Push-forward along a bijection -/



/-! ## Push-forward of the second factor of a product -/



/-! ## Uniform laws on products -/





/-! ## Conditioning one factor of a product -/







/-! ## Conditioning the first factor of a product -/







/-! ## Restriction of a push-forward -/



end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineSource.lean. -/
/-!
# The projected marginals of the sub-line law

This module identifies the two projected point marginals of the sub-line law
of `lem:qld-sublines` as mixtures of the restricted product laws.  The two
source lines of a sampled triple depend on the drawn extended point only
through the canonical representatives of its two source blocks, and those
representatives are unchanged when the drawn point is replaced by any point of
the extended line; a uniform point of the extended line through a uniform
point is a uniform point, so the drawn point may be replaced throughout by the
point that is finally retained.  The six generating blocks of the resulting
law -- the two source point blocks, the two scalar seeds and the two source
direction blocks -- are then regrouped into the two restricted product laws
carried by the two indices of the branch.

## References

The identification is the last step of the proof of `lem:qld-sublines` in
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

/-! ## Source lines depend on the point block only through its representative -/

/-- Two source lines of the same branch with the same seed and the same source
direction block agree as soon as their point blocks have the same canonical
representative in the direction of that line.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineSourceLine_congr (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (b b' : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (s : _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)
    (d : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (h : _root_.MIPStarRE.QPBT.lineRepMap
        (_root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams s) d) b =
      _root_.MIPStarRE.QPBT.lineRepMap
        (_root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams s) d) b') :
    _root_.MIPStarRE.QPBT.subLineSourceLine P kind b s d = _root_.MIPStarRE.QPBT.subLineSourceLine P kind b' s d := by
  cases kind
  · exact _root_.MIPStarRE.QPBT.lineDesc_axis_congr h _ _
  · exact _root_.MIPStarRE.QPBT.lineDesc_diagonal_congr h rfl _ _ _ _





/-! ## Generating form of the restricted product components -/







/-! ## The joint projected marginal of one branch at one extended coordinate -/



/-! ## The two one-point projected marginals of one branch -/





end

end MIPStarRE.QPBT

/-!
# The projected marginals of the sub-line law

This module identifies the two projected point marginals of the sub-line law
of `lem:qld-sublines` as mixtures of the restricted product laws.  The two
source lines of a sampled triple depend on the drawn extended point only
through the canonical representatives of its two source blocks, and those
representatives are unchanged when the drawn point is replaced by any point of
the extended line; a uniform point of the extended line through a uniform
point is a uniform point, so the drawn point may be replaced throughout by the
point that is finally retained.  The six generating blocks of the resulting
law -- the two source point blocks, the two scalar seeds and the two source
direction blocks -- are then regrouped into the two restricted product laws
carried by the two indices of the branch.

## References

The identification is the last step of the proof of `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! ## Source lines depend on the point block only through its representative -/







/-! ## Generating form of the restricted product components -/







/-! ## The joint projected marginal of one branch at one extended coordinate -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) :
    (_root_.MIPStarRE.QPBT.Distribution.prod
        (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.SubLinePointDir P))
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
            (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k))))
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))).map
      (fun p => ((_root_.MIPStarRE.QPBT.subLineTripleOf P kind k p.1).2,
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
            ((_root_.MIPStarRE.QPBT.subLineTripleOf P kind k p.1).1.base +
              p.2 • (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k p.1).1.direction)),
          _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
            ((_root_.MIPStarRE.QPBT.subLineTripleOf P kind k p.1).1.base +
              p.2 • (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k p.1).1.direction))))) =
      (_root_.MIPStarRE.QPBT.Distribution.prod
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
            (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))))
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
            (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k))
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))))).map
        (fun w => ((_root_.MIPStarRE.QPBT.subLineSourceLine P kind w.1.1 w.1.2.1 w.1.2.2,
          _root_.MIPStarRE.QPBT.subLineSourceLine P kind w.2.1 w.2.2.1 w.2.2.2),
          (w.1.1, w.2.1))) := by
  classical
  have hU : _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.SubLinePointDir P) =
      _root_.MIPStarRE.QPBT.Distribution.prod
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)) :=
    _root_.MIPStarRE.QPBT.uniformDistribution_prod _ _
  have hshuffle :
      _root_.MIPStarRE.QPBT.Distribution.prod
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.SubLinePointDir P))
            (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
              (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k))))
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)) =
      (_root_.MIPStarRE.QPBT.Distribution.prod
          (_root_.MIPStarRE.QPBT.Distribution.prod
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
              (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
            (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
              (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k))))
          (_root_.MIPStarRE.QPBT.Distribution.prod
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
              (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
              (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)))).map
        (fun w => (((w.2.1, w.1.1), w.1.2), w.2.2)) := by
    rw [hU]
    refine (_root_.MIPStarRE.QPBT.Distribution.map_bijective_eq _ _
      (fun w : (((Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) ×
        (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams × _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)) ×
      ((Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) ×
        _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)) => (((w.2.1, w.1.1), w.1.2), w.2.2))
      (fun u : ((((Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) ×
        (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)) ×
        (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams × _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)) ×
      _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) => ((u.1.1.2, u.1.2), (u.1.1.1, u.2)))
      (fun _ => rfl) (fun _ => rfl) ?_ ?_).symm
    · intro a
      constructor
      · intro ha
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp ha
        obtain ⟨h11, h12⟩ := Finset.mem_product.mp h1
        obtain ⟨h21, h22⟩ := Finset.mem_product.mp h2
        exact Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr
            ⟨Finset.mem_product.mpr ⟨h21, h11⟩, h12⟩, h22⟩
      · intro ha
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp ha
        obtain ⟨h11, h12⟩ := Finset.mem_product.mp h1
        obtain ⟨h111, h112⟩ := Finset.mem_product.mp h11
        exact Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨h112, h12⟩,
            Finset.mem_product.mpr ⟨h111, h2⟩⟩
    · intro a
      show _ * (_ * _) * (_ * _) = _ * _ * (_ * _) * _
      ring
  have hpp2 :
      (_root_.MIPStarRE.QPBT.Distribution.prod
          (_root_.MIPStarRE.QPBT.Distribution.prod
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
              (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
            (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
              (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k))))
          (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
            (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))).map
        (fun w => ((_root_.MIPStarRE.QPBT.subLineSourceLine P kind
              (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w.2)) w.1.2.1
              (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.1)),
            _root_.MIPStarRE.QPBT.subLineSourceLine P kind
              (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P w.2)) w.1.2.2
              (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.1))),
          (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w.2),
            _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P w.2)))) =
      (_root_.MIPStarRE.QPBT.Distribution.prod
          (_root_.MIPStarRE.QPBT.Distribution.prod
            (_root_.MIPStarRE.QPBT.Distribution.prod
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))
            (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
              (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k))))
          (_root_.MIPStarRE.QPBT.Distribution.prod
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))).map
        (fun w => ((_root_.MIPStarRE.QPBT.subLineSourceLine P kind w.2.1 w.1.2.1 w.1.1.1,
            _root_.MIPStarRE.QPBT.subLineSourceLine P kind w.2.2 w.1.2.2 w.1.1.2),
          (w.2.1, w.2.2))) := by
    rw [← _root_.MIPStarRE.QPBT.uniformDistribution_map_projX_projZ_pauli,
      _root_.MIPStarRE.QPBT.Distribution.prod_map_left
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
        (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
          (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k)))
        (fun u => (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P u),
          _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P u))),
      _root_.MIPStarRE.QPBT.Distribution.prod_map_right _
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
        (fun u => (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P u),
          _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P u))),
      _root_.MIPStarRE.QPBT.Distribution.prod_map_left _
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)) _,
      _root_.MIPStarRE.QPBT.Distribution.map_map, _root_.MIPStarRE.QPBT.Distribution.map_map]
  have hfinal :
      (_root_.MIPStarRE.QPBT.Distribution.prod
          (_root_.MIPStarRE.QPBT.Distribution.prod
            (_root_.MIPStarRE.QPBT.Distribution.prod
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))
            (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
              (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k))))
          (_root_.MIPStarRE.QPBT.Distribution.prod
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))).map
        (fun w => ((w.2.1, (w.1.2.1, w.1.1.1)),
          (w.2.2, (w.1.2.2, w.1.1.2)))) =
      _root_.MIPStarRE.QPBT.Distribution.prod
        (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))))
        (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k))
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))) := by
    refine _root_.MIPStarRE.QPBT.Distribution.map_bijective_eq _ _
      (fun w : ((((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) ×
        (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams × _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)) ×
      ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))) =>
        ((w.2.1, (w.1.2.1, w.1.1.1)), (w.2.2, (w.1.2.2, w.1.1.2))))
      (fun u : (((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) ×
        (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))) ×
      ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) ×
        (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))) =>
        (((u.1.2.2, u.2.2.2), (u.1.2.1, u.2.2.1)), (u.1.1, u.2.1)))
      (fun _ => rfl) (fun _ => rfl) ?_ ?_
    · intro a
      simp only [_root_.MIPStarRE.QPBT.Distribution.prod_support, Finset.mem_product]
      tauto
    · intro a
      simp only [_root_.MIPStarRE.QPBT.Distribution.prod_weight]
      ring
  rw [hshuffle]
  refine Eq.trans (_root_.MIPStarRE.QPBT.Distribution.map_map _ _ _) ?_
  refine Eq.trans (_root_.MIPStarRE.QPBT.Distribution.prod_map_eq_bind _ _ _) ?_
  refine Eq.trans (_root_.MIPStarRE.QPBT.Distribution.bind_congr_support _ _
    (fun r => (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
        (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)).map
      (fun y => ((_root_.MIPStarRE.QPBT.subLineSourceLine P kind (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P y))
            r.2.1 (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P r.1)),
          _root_.MIPStarRE.QPBT.subLineSourceLine P kind (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P y))
            r.2.2 (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P r.1))),
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P y),
          _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P y))))) ?_) ?_
  · intro r hr
    obtain ⟨-, hseeds⟩ := Finset.mem_product.mp hr
    obtain ⟨hsx, hsz⟩ := Finset.mem_product.mp hseeds
    have hx : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams r.2.1 = _root_.MIPStarRE.QPBT.subLineXIndex P k :=
      (Finset.mem_filter.mp hsx).2
    have hz : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams r.2.2 = _root_.MIPStarRE.QPBT.subLineZIndex P k :=
      (Finset.mem_filter.mp hsz).2
    show (_root_.MIPStarRE.QPBT.Distribution.prod
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))).map
        (fun p => ((_root_.MIPStarRE.QPBT.subLineTripleOf P kind k ((p.1, r.1), r.2)).2,
          (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
              ((_root_.MIPStarRE.QPBT.subLineTripleOf P kind k ((p.1, r.1), r.2)).1.base +
                p.2 • (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k ((p.1, r.1), r.2)).1.direction)),
            _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
              ((_root_.MIPStarRE.QPBT.subLineTripleOf P kind k ((p.1, r.1), r.2)).1.base +
                p.2 •
                  (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k ((p.1, r.1), r.2)).1.direction)))))
      = _
    have hfun :
        (fun p : (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd) ×
            _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd =>
          ((_root_.MIPStarRE.QPBT.subLineTripleOf P kind k ((p.1, r.1), r.2)).2,
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
                ((_root_.MIPStarRE.QPBT.subLineTripleOf P kind k ((p.1, r.1), r.2)).1.base +
                  p.2 •
                    (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k ((p.1, r.1), r.2)).1.direction)),
              _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
                ((_root_.MIPStarRE.QPBT.subLineTripleOf P kind k ((p.1, r.1), r.2)).1.base +
                  p.2 •
                    (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k
                      ((p.1, r.1), r.2)).1.direction))))) =
        fun p => ((_root_.MIPStarRE.QPBT.subLineSourceLine P kind (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
                  (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k r.1) p.1 +
                    p.2 • _root_.MIPStarRE.QPBT.subLineExtDirection P kind k r.1)))
                r.2.1 (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P r.1)),
              _root_.MIPStarRE.QPBT.subLineSourceLine P kind (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
                  (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k r.1) p.1 +
                    p.2 • _root_.MIPStarRE.QPBT.subLineExtDirection P kind k r.1)))
                r.2.2 (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P r.1))),
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
                (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k r.1) p.1 +
                  p.2 • _root_.MIPStarRE.QPBT.subLineExtDirection P kind k r.1)),
              _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
                (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k r.1) p.1 +
                  p.2 • _root_.MIPStarRE.QPBT.subLineExtDirection P kind k r.1)))) := by
      funext p
      have hbase : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k ((p.1, r.1), r.2)).1.base =
          _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k r.1) p.1 :=
        _root_.MIPStarRE.QPBT.subLineExtLine_base P kind k ((p.1, r.1), r.2)
      have hdir : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k ((p.1, r.1), r.2)).1.direction =
          _root_.MIPStarRE.QPBT.subLineExtDirection P kind k r.1 :=
        _root_.MIPStarRE.QPBT.subLineExtLine_direction P kind k ((p.1, r.1), r.2)
      have htriple : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k ((p.1, r.1), r.2)).2 =
          (_root_.MIPStarRE.QPBT.subLineSourceLine P kind (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P p.1)) r.2.1
              (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P r.1)),
            _root_.MIPStarRE.QPBT.subLineSourceLine P kind (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P p.1)) r.2.2
              (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P r.1))) := rfl
      have hcx : _root_.MIPStarRE.QPBT.subLineSourceLine P kind
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P p.1)) r.2.1
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P r.1)) =
          _root_.MIPStarRE.QPBT.subLineSourceLine P kind (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
            (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k r.1) p.1 +
              p.2 • _root_.MIPStarRE.QPBT.subLineExtDirection P kind k r.1))) r.2.1
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P r.1)) := by
        refine _root_.MIPStarRE.QPBT.subLineSourceLine_congr P kind _ _ _ _ ?_
        rw [hx]
        exact (_root_.MIPStarRE.QPBT.lineRepMap_projX_subLineExtLine_point P kind k p.1 r.1 p.2).symm
      have hcz : _root_.MIPStarRE.QPBT.subLineSourceLine P kind
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P p.1)) r.2.2
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P r.1)) =
          _root_.MIPStarRE.QPBT.subLineSourceLine P kind (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
            (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k r.1) p.1 +
              p.2 • _root_.MIPStarRE.QPBT.subLineExtDirection P kind k r.1))) r.2.2
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P r.1)) := by
        refine _root_.MIPStarRE.QPBT.subLineSourceLine_congr P kind _ _ _ _ ?_
        rw [hz]
        exact (_root_.MIPStarRE.QPBT.lineRepMap_projZ_subLineExtLine_point P kind k p.1 r.1 p.2).symm
      rw [hbase, hdir, htriple, hcx, hcz]
    rw [hfun]
    exact _root_.MIPStarRE.QPBT.uniformDistribution_map_lineRepMap_add_smul_comp
      (_root_.MIPStarRE.QPBT.subLineExtDirection P kind k r.1)
      (fun y => ((_root_.MIPStarRE.QPBT.subLineSourceLine P kind (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P y))
            r.2.1 (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P r.1)),
          _root_.MIPStarRE.QPBT.subLineSourceLine P kind (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P y))
            r.2.2 (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P r.1))),
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P y), _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P y))))
  · refine Eq.trans (_root_.MIPStarRE.QPBT.Distribution.prod_map_eq_bind
      (_root_.MIPStarRE.QPBT.Distribution.prod
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
        (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
          (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k))))
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
        (Fin (2 * P.m + 2) → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))
      (fun w => ((_root_.MIPStarRE.QPBT.subLineSourceLine P kind
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w.2)) w.1.2.1
            (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.1)),
          _root_.MIPStarRE.QPBT.subLineSourceLine P kind
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P w.2)) w.1.2.2
            (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.1))),
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w.2),
          _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P w.2))))).symm ?_
    refine Eq.trans hpp2 ?_
    rw [← hfinal]
    exact (_root_.MIPStarRE.QPBT.Distribution.map_map _
      (fun w : ((((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) ×
            (_root_.MIPStarRE.QPBT.ScalarQ P.toLdParams × _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)) ×
          ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))) =>
        ((w.2.1, (w.1.2.1, w.1.1.1)), (w.2.2, (w.1.2.2, w.1.1.2))))
      (fun w => ((_root_.MIPStarRE.QPBT.subLineSourceLine P kind w.1.1 w.1.2.1 w.1.2.2,
          _root_.MIPStarRE.QPBT.subLineSourceLine P kind w.2.1 w.2.2.1 w.2.2.2),
        (w.1.1, w.2.1)))).symm
