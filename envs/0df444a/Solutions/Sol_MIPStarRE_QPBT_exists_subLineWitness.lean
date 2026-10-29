-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_subLineWitness
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:45:51.471628+00:00
-- url     : https://prove2.me/submissions/4b276371-438e-4c73-9f26-de91e5ebea0b

-- Generated proof for MIPStarRE.QPBT.exists_subLineWitness.
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
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineMixture
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineSeed
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_map
import Theorems.Thm_MIPStarRE_QPBT_Distribution_bind_bind
import Theorems.Thm_MIPStarRE_QPBT_Distribution_bind_isProbability
import Theorems.Thm_MIPStarRE_QPBT_Distribution_bind_map
import Theorems.Thm_MIPStarRE_QPBT_Distribution_bind_map_left
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_bind_left
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_isProbability
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_map_left
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_map_right
import Theorems.Thm_MIPStarRE_QPBT_Distribution_restrict_isProbability
import Theorems.Thm_MIPStarRE_QPBT_exists_samplingData_of_mem_subLineDist_support
import Theorems.Thm_MIPStarRE_QPBT_projX_subLineExtDirection_mem_span
import Theorems.Thm_MIPStarRE_QPBT_projZ_subLineExtDirection_mem_span
import Theorems.Thm_MIPStarRE_QPBT_restrict_uniform_prod_fst
import Theorems.Thm_MIPStarRE_QPBT_restrictedALineDist_eq_map_prod
import Theorems.Thm_MIPStarRE_QPBT_restrictedDLineDist_eq_map_prod
import Theorems.Thm_MIPStarRE_QPBT_subLineBranchSamplingData_map_joint
import Theorems.Thm_MIPStarRE_QPBT_subLineDist_map_fst
import Theorems.Thm_MIPStarRE_QPBT_subLineTripleOf_compatibility
import Theorems.Thm_MIPStarRE_QPBT_subLineTripleOf_xBase
import Theorems.Thm_MIPStarRE_QPBT_subLineTripleOf_zBase

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Algebra/Lines.lean. -/
/-!
# Lines and canonical representatives

The classical and Pauli question distributions use affine lines in a finite
coordinate space.  This module keeps the zero-direction case explicit and
provides the canonical projection used for line representatives.

## References

The source-facing nodes are blueprint `def:line`, `prop:line-equiv`, and
`def:line-representative`; the formalization support nodes are blueprint
`lem:line-rep-kernel` and `lem:line-rep-incidence`.
The paper origin is `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:102-174`.

Note: this module contributes declarations to the comparator statement closure
of the QPBT headline theorems, which must elaborate in the same environment as
the Mathlib-only `ChallengeQPBT.lean`.  Keep the full `import Mathlib`; do not
narrow it.  See `docs/comparator.md`, "Environment alignment".
-/

@[expose] public section

namespace MIPStarRE.QPBT

open scoped BigOperators

variable {K : Type*} [Field K]









/--
Changing the base point to another point on a line leaves the line unchanged.
This is blueprint `prop:line-equiv`,
with paper origin `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:128-132`.
-/
theorem linePoints_eq_of_mem {m : ℕ}
    (u v u' : Fin m → K) (h : u' ∈ _root_.MIPStarRE.QPBT.linePoints u v) :
    _root_.MIPStarRE.QPBT.linePoints u v = _root_.MIPStarRE.QPBT.linePoints u' v := by
  obtain ⟨t, rfl⟩ := h
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s - t, by module⟩
  · rintro ⟨s, rfl⟩
    exact ⟨t + s, by module⟩











/- The point-valued companion to `lineRepMap`; Lean-only notation for the
canonical representative in `def:line-representative`. -/








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

/-- The `X` block of a sum of extended points is the sum of the blocks.
Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_add {K : Type*} [AddCommMonoid K] {m : ℕ}
    (u v : Fin (2 * m + 2) → K) :
    _root_.MIPStarRE.QPBT.projX (u + v) = _root_.MIPStarRE.QPBT.projX u + _root_.MIPStarRE.QPBT.projX v := rfl

/-- The `Z` block of a sum of extended points is the sum of the blocks.
Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_add {K : Type*} [AddCommMonoid K] {m : ℕ}
    (u v : Fin (2 * m + 2) → K) :
    _root_.MIPStarRE.QPBT.projZ (u + v) = _root_.MIPStarRE.QPBT.projZ u + _root_.MIPStarRE.QPBT.projZ v := rfl

/-- The `X` block of a scalar multiple of an extended point is the scalar
multiple of the block.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projX_smul {K : Type*} [Monoid K] {m : ℕ} (t : K)
    (u : Fin (2 * m + 2) → K) :
    _root_.MIPStarRE.QPBT.projX (t • u) = t • _root_.MIPStarRE.QPBT.projX u := rfl

/-- The `Z` block of a scalar multiple of an extended point is the scalar
multiple of the block.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem projZ_smul {K : Type*} [Monoid K] {m : ℕ} (t : K)
    (u : Fin (2 * m + 2) → K) :
    _root_.MIPStarRE.QPBT.projZ (t • u) = t • _root_.MIPStarRE.QPBT.projZ u := rfl

/-! ## The coordinate blocks of an extended point -/















/-! ## Transport to the source scalar field -/





/-! ## The blocks of an extended direct sample -/



/-! ## Compatibility data read off the coordinate blocks -/





end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineSeed.lean. -/
/-!
# The two independent blocks of a fresh diagonal direction pair

This module splits the fresh diagonal direction pair of the sub-line sampling
procedure into its two independent blocks.  The coordinate-index event
constrains only the scalar seed of the pair, so conditioning on it leaves the
direction block uniform and independent of the conditioned seed.  The
direction block of a fresh pair is therefore available as an unconstrained
uniform vector, which is what allows the sampling procedure to read it off the
corresponding block of the direction of the sampled extended line.

## References

The block decomposition supports `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate-index event is that of `def:ith-restricted-line`, blueprint
lines 1209--1228, paper lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The coordinate-index event on a scalar seed -/







/-! ## The blocks of a fresh diagonal direction pair -/

/-- A fresh diagonal direction pair at coordinate index `i` is a scalar seed
conditioned on the coordinate-index fiber of `i` together with an independent
uniform direction block.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem freshDiagonalPairDist_eq_prod (L : _root_.MIPStarRE.QPBT.LdParams) (i : Fin L.m) :
    _root_.MIPStarRE.QPBT.freshDiagonalPairDist L i =
      _root_.MIPStarRE.QPBT.Distribution.prod
        (_root_.MIPStarRE.QPBT.Distribution.restrict (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ScalarQ L))
          (_root_.MIPStarRE.QPBT.ldSeedIndexEvent L i) (_root_.MIPStarRE.QPBT.ldSeedIndexEvent_positive L i))
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)) := by
  classical
  unfold _root_.MIPStarRE.QPBT.freshDiagonalPairDist
  exact _root_.MIPStarRE.QPBT.restrict_uniform_prod_fst (_root_.MIPStarRE.QPBT.ldSeedIndexEvent L i)
    (_root_.MIPStarRE.QPBT.ldSeedIndexEvent_positive L i) (_root_.MIPStarRE.QPBT.ldSeedDirEvent_positive L i)



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







/-! ## Generating form of the restricted product components -/

/-- The restricted line-point law of a kind at an index is the law of the
source line of that kind decoded from a uniform point block, a scalar seed in
the coordinate-index fiber of the index and a uniform direction block,
together with that same point block.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem restrictedLinePointDist_eq_map_prod (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (kind : _root_.MIPStarRE.QPBT.LineKind) (i : Fin P.m) :
    _root_.MIPStarRE.QPBT.restrictedLinePointDist P kind i =
      (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P i)
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))).map
        (fun w => (_root_.MIPStarRE.QPBT.subLineSourceLine P kind w.1 w.2.1 w.2.2, w.1)) := by
  cases kind
  · show _root_.MIPStarRE.QPBT.restrictedALineDist P.toLdParams i = _
    rw [_root_.MIPStarRE.QPBT.restrictedALineDist_eq_map_prod, _root_.MIPStarRE.QPBT.freshDiagonalPairDist_eq_prod]
    rfl
  · show _root_.MIPStarRE.QPBT.restrictedDLineDist P.toLdParams i = _
    rw [_root_.MIPStarRE.QPBT.restrictedDLineDist_eq_map_prod, _root_.MIPStarRE.QPBT.freshDiagonalPairDist_eq_prod]
    rfl

/-- The `X` component law of a pair of indices is the law of the two source
lines decoded from two independent restricted blocks, together with the point
block of the first.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineXComponentDist_eq_map_prod (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (kind : _root_.MIPStarRE.QPBT.LineKind) (i j : Fin P.m) :
    _root_.MIPStarRE.QPBT.subLineXComponentDist P (kind, (i, j)) =
      (_root_.MIPStarRE.QPBT.Distribution.prod
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
            (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P i)
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))))
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
            (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P j)
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))))).map
        (fun w => ((_root_.MIPStarRE.QPBT.subLineSourceLine P kind w.1.1 w.1.2.1 w.1.2.2,
          _root_.MIPStarRE.QPBT.subLineSourceLine P kind w.2.1 w.2.2.1 w.2.2.2), w.1.1)) := by
  simp only [_root_.MIPStarRE.QPBT.subLineXComponentDist, _root_.MIPStarRE.QPBT.restrictedLinePointDist_eq_map_prod,
    _root_.MIPStarRE.QPBT.Distribution.map_map]
  rw [_root_.MIPStarRE.QPBT.Distribution.prod_map_left, _root_.MIPStarRE.QPBT.Distribution.prod_map_right,
    _root_.MIPStarRE.QPBT.Distribution.map_map, _root_.MIPStarRE.QPBT.Distribution.map_map]

/-- The `Z` component law of a pair of indices is the law of the two source
lines decoded from two independent restricted blocks, together with the point
block of the second.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineZComponentDist_eq_map_prod (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (kind : _root_.MIPStarRE.QPBT.LineKind) (i j : Fin P.m) :
    _root_.MIPStarRE.QPBT.subLineZComponentDist P (kind, (i, j)) =
      (_root_.MIPStarRE.QPBT.Distribution.prod
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
            (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P i)
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))))
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
            (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P j)
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))))).map
        (fun w => ((_root_.MIPStarRE.QPBT.subLineSourceLine P kind w.1.1 w.1.2.1 w.1.2.2,
          _root_.MIPStarRE.QPBT.subLineSourceLine P kind w.2.1 w.2.2.1 w.2.2.2), w.2.1)) := by
  simp only [_root_.MIPStarRE.QPBT.subLineZComponentDist, _root_.MIPStarRE.QPBT.restrictedLinePointDist_eq_map_prod,
    _root_.MIPStarRE.QPBT.Distribution.map_map]
  rw [_root_.MIPStarRE.QPBT.Distribution.prod_map_left, _root_.MIPStarRE.QPBT.Distribution.prod_map_right,
    _root_.MIPStarRE.QPBT.Distribution.map_map, _root_.MIPStarRE.QPBT.Distribution.map_map]

/-! ## The joint projected marginal of one branch at one extended coordinate -/



/-! ## The two one-point projected marginals of one branch -/

/-- At a fixed line kind and a fixed extended coordinate, the joint law of the
two source lines of a sampled triple together with the source `X` block of a
uniform point of its extended line is the `X` component law of the two indices
of that branch.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchSamplingData_map_projX (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) :
    (_root_.MIPStarRE.QPBT.Distribution.prod
        (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.SubLinePointDir P))
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
            (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k))))
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))).map
      (fun p => ((_root_.MIPStarRE.QPBT.subLineTripleOf P kind k p.1).2,
        _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P
          ((_root_.MIPStarRE.QPBT.subLineTripleOf P kind k p.1).1.base +
            p.2 • (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k p.1).1.direction)))) =
      _root_.MIPStarRE.QPBT.subLineXComponentDist P
        (kind, (_root_.MIPStarRE.QPBT.subLineXIndex P k, _root_.MIPStarRE.QPBT.subLineZIndex P k)) := by
  classical
  have h := congrArg
    (fun D : _root_.LIDT.MIPStarRE.LDT.Distribution ((_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) ×
        ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))) =>
      _root_.LIDT.MIPStarRE.LDT.Distribution.map D (fun z => (z.1, z.2.1)))
    (_root_.MIPStarRE.QPBT.subLineBranchSamplingData_map_joint P kind k)
  simp only [_root_.MIPStarRE.QPBT.Distribution.map_map] at h
  refine Eq.trans h ?_
  exact (_root_.MIPStarRE.QPBT.subLineXComponentDist_eq_map_prod P kind (_root_.MIPStarRE.QPBT.subLineXIndex P k)
    (_root_.MIPStarRE.QPBT.subLineZIndex P k)).symm

/-- At a fixed line kind and a fixed extended coordinate, the joint law of the
two source lines of a sampled triple together with the source `Z` block of a
uniform point of its extended line is the `Z` component law of the two indices
of that branch.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchSamplingData_map_projZ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) :
    (_root_.MIPStarRE.QPBT.Distribution.prod
        (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.SubLinePointDir P))
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
            (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k))))
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd))).map
      (fun p => ((_root_.MIPStarRE.QPBT.subLineTripleOf P kind k p.1).2,
        _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P
          ((_root_.MIPStarRE.QPBT.subLineTripleOf P kind k p.1).1.base +
            p.2 • (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k p.1).1.direction)))) =
      _root_.MIPStarRE.QPBT.subLineZComponentDist P
        (kind, (_root_.MIPStarRE.QPBT.subLineXIndex P k, _root_.MIPStarRE.QPBT.subLineZIndex P k)) := by
  classical
  have h := congrArg
    (fun D : _root_.LIDT.MIPStarRE.LDT.Distribution ((_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × _root_.MIPStarRE.QPBT.LineDesc P.toLdParams) ×
        ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))) =>
      _root_.LIDT.MIPStarRE.LDT.Distribution.map D (fun z => (z.1, z.2.2)))
    (_root_.MIPStarRE.QPBT.subLineBranchSamplingData_map_joint P kind k)
  simp only [_root_.MIPStarRE.QPBT.Distribution.map_map] at h
  refine Eq.trans h ?_
  exact (_root_.MIPStarRE.QPBT.subLineZComponentDist_eq_map_prod P kind (_root_.MIPStarRE.QPBT.subLineXIndex P k)
    (_root_.MIPStarRE.QPBT.subLineZIndex P k)).symm

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



/-! ## Injectivity of the two block embeddings -/





/-! ## The blocks of an elementary coordinate direction -/

















/-! ## The coordinates occupied by the two blocks -/









/-! ## The blocks of a point of an extended line -/

/-- Transporting the extended scalar field to the source scalar field carries
a point of a line to a point of the transported line, since the transport is
a coordinatewise field isomorphism.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem directPointToPauli_mem_linePoints (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    {b d x : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd}
    (hx : x ∈ _root_.MIPStarRE.QPBT.linePoints b d) :
    _root_.MIPStarRE.QPBT.directPointToPauli P x ∈
      _root_.MIPStarRE.QPBT.linePoints (_root_.MIPStarRE.QPBT.directPointToPauli P b) (_root_.MIPStarRE.QPBT.directPointToPauli P d) := by
  obtain ⟨t, rfl⟩ := hx
  refine ⟨_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P t, ?_⟩
  funext i
  change _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (b i + t * d i) =
    _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (b i) +
      _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P t * _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (d i)
  rw [map_add, map_mul]

/-- The `X` block of a point of a line lies on the source line through the
canonical representative of the `X` block of the base, as soon as the `X`
block of the direction is a multiple of the source direction.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projX_mem_linePoints {K : Type*} [Field K] {m : ℕ}
    (b d : Fin (2 * m + 2) → K) (dX : Fin m → K)
    (hd : _root_.MIPStarRE.QPBT.projX d ∈ Submodule.span K ({dX} : Set (Fin m → K)))
    {x : Fin (2 * m + 2) → K} (hx : x ∈ _root_.MIPStarRE.QPBT.linePoints b d) :
    _root_.MIPStarRE.QPBT.projX x ∈ _root_.MIPStarRE.QPBT.linePoints (_root_.MIPStarRE.QPBT.lineRepMap dX (_root_.MIPStarRE.QPBT.projX b)) dX := by
  obtain ⟨t, rfl⟩ := hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hd
  rw [_root_.MIPStarRE.QPBT.linePoints_eq_of_mem _ dX (_root_.MIPStarRE.QPBT.projX b)
    (_root_.MIPStarRE.QPBT.mem_linePoints_lineRepMap dX (_root_.MIPStarRE.QPBT.projX b))]
  refine ⟨t * c, ?_⟩
  rw [_root_.MIPStarRE.QPBT.projX_add, _root_.MIPStarRE.QPBT.projX_smul, ← hc]
  module

/-- The `Z` block of a point of a line lies on the source line through the
canonical representative of the `Z` block of the base, as soon as the `Z`
block of the direction is a multiple of the source direction.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projZ_mem_linePoints {K : Type*} [Field K] {m : ℕ}
    (b d : Fin (2 * m + 2) → K) (dZ : Fin m → K)
    (hd : _root_.MIPStarRE.QPBT.projZ d ∈ Submodule.span K ({dZ} : Set (Fin m → K)))
    {x : Fin (2 * m + 2) → K} (hx : x ∈ _root_.MIPStarRE.QPBT.linePoints b d) :
    _root_.MIPStarRE.QPBT.projZ x ∈ _root_.MIPStarRE.QPBT.linePoints (_root_.MIPStarRE.QPBT.lineRepMap dZ (_root_.MIPStarRE.QPBT.projZ b)) dZ := by
  obtain ⟨t, rfl⟩ := hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hd
  rw [_root_.MIPStarRE.QPBT.linePoints_eq_of_mem _ dZ (_root_.MIPStarRE.QPBT.projZ b)
    (_root_.MIPStarRE.QPBT.mem_linePoints_lineRepMap dZ (_root_.MIPStarRE.QPBT.projZ b))]
  refine ⟨t * c, ?_⟩
  rw [_root_.MIPStarRE.QPBT.projZ_add, _root_.MIPStarRE.QPBT.projZ_smul, ← hc]
  module

/-! ## Incidence of the blocks of an extended line -/



/-- Incidence of the `X` blocks: if a source line has as base the canonical
representative, in its own direction, of the `X` block of the base of an
extended line, and if the `X` block of the direction of the extended line
lies in the span of the source direction, then the `X` block of every point
of the extended line is a point of the source line.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projX_mem_pointSet (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (base dir : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)
    (lineX : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (hbase : lineX.base =
      _root_.MIPStarRE.QPBT.lineRepMap lineX.direction (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P base)))
    (hdir : _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P dir) ∈
      Submodule.span (_root_.MIPStarRE.QPBT.PauliScalar P)
        ({lineX.direction} : Set (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))
    {u : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd}
    (hu : u ∈ _root_.MIPStarRE.QPBT.linePoints base dir) :
    _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P u) ∈ lineX.pointSet := by
  rw [_root_.MIPStarRE.QPBT.LineDesc.pointSet, hbase]
  exact _root_.MIPStarRE.QPBT.projX_mem_linePoints _ _ _ hdir (_root_.MIPStarRE.QPBT.directPointToPauli_mem_linePoints P hu)

/-- Incidence of the `Z` blocks: if a source line has as base the canonical
representative, in its own direction, of the `Z` block of the base of an
extended line, and if the `Z` block of the direction of the extended line
lies in the span of the source direction, then the `Z` block of every point
of the extended line is a point of the source line.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem projZ_mem_pointSet (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (base dir : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd)
    (lineZ : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (hbase : lineZ.base =
      _root_.MIPStarRE.QPBT.lineRepMap lineZ.direction (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P base)))
    (hdir : _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P dir) ∈
      Submodule.span (_root_.MIPStarRE.QPBT.PauliScalar P)
        ({lineZ.direction} : Set (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))
    {u : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd}
    (hu : u ∈ _root_.MIPStarRE.QPBT.linePoints base dir) :
    _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P u) ∈ lineZ.pointSet := by
  rw [_root_.MIPStarRE.QPBT.LineDesc.pointSet, hbase]
  exact _root_.MIPStarRE.QPBT.projZ_mem_linePoints _ _ _ hdir (_root_.MIPStarRE.QPBT.directPointToPauli_mem_linePoints P hu)

end

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



/-- The auxiliary randomness law has total mass one. -/
theorem subLineSamplingDist_isProbability (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (_root_.MIPStarRE.QPBT.subLineSamplingDist P).IsProbability := by
  refine _root_.MIPStarRE.QPBT.Distribution.bind_isProbability _ _
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) fun k _ => ?_
  exact _root_.LIDT.MIPStarRE.LDT.Distribution.IsProbability.map
    (_root_.MIPStarRE.QPBT.Distribution.prod_isProbability _ _ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _)
      (_root_.MIPStarRE.QPBT.Distribution.prod_isProbability _ _ (_root_.MIPStarRE.QPBT.subLineSeedDist_isProbability P _)
        (_root_.MIPStarRE.QPBT.subLineSeedDist_isProbability P _))) _

/-! ## The sampled triple -/













/-! ## Elementary evaluations of the sampled triple -/

/-- The extended line of a branch has the kind of that branch. -/
theorem subLineExtLine_kind (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P) :
    (_root_.MIPStarRE.QPBT.subLineExtLine P kind k w).kind = kind := by
  cases kind <;> rfl

/-- The direction of the extended line of a branch is the branch direction. -/
theorem subLineExtLine_direction (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P) :
    (_root_.MIPStarRE.QPBT.subLineExtLine P kind k w).direction =
      _root_.MIPStarRE.QPBT.subLineExtDirection P kind k w.1.2 := by
  cases kind <;> rfl



/-- A source line of a branch has the kind of that branch. -/
theorem subLineSourceLine_kind (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (b : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (s : _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)
    (d : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (_root_.MIPStarRE.QPBT.subLineSourceLine P kind b s d).kind = kind := by
  cases kind <;> rfl

/-- The direction of a source line of a branch is the branch source direction
at the coordinate index named by its seed. -/
theorem subLineSourceLine_direction (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (b : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (s : _root_.MIPStarRE.QPBT.ScalarQ P.toLdParams)
    (d : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (_root_.MIPStarRE.QPBT.subLineSourceLine P kind b s d).direction =
      _root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams s) d := by
  cases kind <;> rfl



/-! ## The support of the sub-line law -/



/-! ## Pointwise properties of a sampled triple -/

/-- The direction of the source `X` line of a sampled triple is the branch
source direction at the coordinate carried by that line. -/
theorem subLineTripleOf_xDirection (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P)
    (hx : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.1 = _root_.MIPStarRE.QPBT.subLineXIndex P k) :
    (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.direction =
      _root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.subLineXIndex P k)
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.2)) := by
  have h : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.direction =
      _root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.1)
        (_root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.2)) :=
    _root_.MIPStarRE.QPBT.subLineSourceLine_direction P kind _ w.2.1 _
  rw [h, hx]

/-- The direction of the source `Z` line of a sampled triple is the branch
source direction at the coordinate carried by that line. -/
theorem subLineTripleOf_zDirection (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P)
    (hz : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.2 = _root_.MIPStarRE.QPBT.subLineZIndex P k) :
    (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.2.direction =
      _root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.subLineZIndex P k)
        (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.2)) := by
  have h : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.2.direction =
      _root_.MIPStarRE.QPBT.subLineSourceDirection P kind (_root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.2)
        (_root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P w.1.2)) :=
    _root_.MIPStarRE.QPBT.subLineSourceLine_direction P kind _ w.2.2 _
  rw [h, hz]

/-- The `X` block of the direction of the extended line of a sampled triple
lies in the line spanned by the direction of its source `X` line. -/
theorem subLineTripleOf_xSpan (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P)
    (hx : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.1 = _root_.MIPStarRE.QPBT.subLineXIndex P k) :
    _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.direction) ∈
      Submodule.span (_root_.MIPStarRE.QPBT.PauliScalar P)
        ({(_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.direction} :
          Set (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) := by
  have hext : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.direction =
      _root_.MIPStarRE.QPBT.subLineExtDirection P kind k w.1.2 := _root_.MIPStarRE.QPBT.subLineExtLine_direction P kind k w
  rw [_root_.MIPStarRE.QPBT.subLineTripleOf_xDirection P kind k w hx, hext]
  exact _root_.MIPStarRE.QPBT.projX_subLineExtDirection_mem_span P kind k w.1.2

/-- The `Z` block of the direction of the extended line of a sampled triple
lies in the line spanned by the direction of its source `Z` line. -/
theorem subLineTripleOf_zSpan (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P)
    (hz : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.2 = _root_.MIPStarRE.QPBT.subLineZIndex P k) :
    _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.direction) ∈
      Submodule.span (_root_.MIPStarRE.QPBT.PauliScalar P)
        ({(_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.2.direction} :
          Set (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) := by
  have hext : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.direction =
      _root_.MIPStarRE.QPBT.subLineExtDirection P kind k w.1.2 := _root_.MIPStarRE.QPBT.subLineExtLine_direction P kind k w
  rw [_root_.MIPStarRE.QPBT.subLineTripleOf_zDirection P kind k w hz, hext]
  exact _root_.MIPStarRE.QPBT.projZ_subLineExtDirection_mem_span P kind k w.1.2





/-- Every point of the extended line of a sampled triple projects onto both of
its source lines.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineTripleOf_incidence (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P)
    (hx : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.1 = _root_.MIPStarRE.QPBT.subLineXIndex P k)
    (hz : _root_.MIPStarRE.QPBT.chiIndex P.toLdParams w.2.2 = _root_.MIPStarRE.QPBT.subLineZIndex P k)
    {u : Fin P.extendedDirectLd.m → _root_.MIPStarRE.QPBT.DirectScalarQ P.extendedDirectLd}
    (hu : u ∈ (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.pointSet) :
    _root_.MIPStarRE.QPBT.projX (_root_.MIPStarRE.QPBT.directPointToPauli P u) ∈
        (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.pointSet ∧
      _root_.MIPStarRE.QPBT.projZ (_root_.MIPStarRE.QPBT.directPointToPauli P u) ∈
        (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.2.pointSet :=
  ⟨_root_.MIPStarRE.QPBT.projX_mem_pointSet P _ _ _ (_root_.MIPStarRE.QPBT.subLineTripleOf_xBase P kind k w hx)
      (_root_.MIPStarRE.QPBT.subLineTripleOf_xSpan P kind k w hx) hu,
    _root_.MIPStarRE.QPBT.projZ_mem_pointSet P _ _ _ (_root_.MIPStarRE.QPBT.subLineTripleOf_zBase P kind k w hz)
      (_root_.MIPStarRE.QPBT.subLineTripleOf_zSpan P kind k w hz) hu⟩



/-- An extended axis line of a sampled triple has axis-parallel source lines.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineTripleOf_axis_closure (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (k : Fin (2 * P.m + 2)) (w : _root_.MIPStarRE.QPBT.SubLineSamplingData P)
    (haxis : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.kind = .axis) :
    (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.1.kind = .axis ∧
      (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).2.2.kind = .axis := by
  have hkind : kind = .axis := by
    have h : (_root_.MIPStarRE.QPBT.subLineTripleOf P kind k w).1.kind = kind :=
      _root_.MIPStarRE.QPBT.subLineExtLine_kind P kind k w
    rw [← h]
    exact haxis
  subst hkind
  exact ⟨_root_.MIPStarRE.QPBT.subLineSourceLine_kind P .axis _ _ _,
    _root_.MIPStarRE.QPBT.subLineSourceLine_kind P .axis _ _ _⟩

/-! ## Total mass and extended marginal -/

/-- The sub-line law has total mass one. -/
theorem subLineDist_isProbability (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (_root_.MIPStarRE.QPBT.subLineDist P).IsProbability := by
  refine _root_.MIPStarRE.QPBT.Distribution.bind_isProbability _ _
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) fun c _ => ?_
  fin_cases c
  · exact _root_.LIDT.MIPStarRE.LDT.Distribution.IsProbability.map (_root_.MIPStarRE.QPBT.subLineSamplingDist_isProbability P) _
  · exact _root_.LIDT.MIPStarRE.LDT.Distribution.IsProbability.map (_root_.MIPStarRE.QPBT.subLineSamplingDist_isProbability P) _







end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineMixture.lean. -/
/-!
# The projected mixtures of the sub-line law

This module assembles the two projected point marginals of the sub-line law of
`lem:qld-sublines` into mixtures of the restricted product laws.  Drawing a
uniform point of the extended line of a mixture of line laws is the same
mixture of the corresponding uniform-point laws, so the two projected
marginals of the sub-line law are the mixtures, over the drawn kind and the
drawn extended coordinate, of the projected marginals of one branch at one
extended coordinate.  Each of those is the component law of the pair of
indices carried by that branch, so the mixing law is the law of the kind
together with the pair of indices assigned to a uniform extended coordinate.

## References

The assembly is the last step of the proof of `lem:qld-sublines` in
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

/-! ## The uniform point of a mixture of line laws -/

/-- Drawing a uniform point of the extended line of a mixture of line-triple
laws is the corresponding mixture of the uniform-point laws.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLinePointDist_bind (P : _root_.MIPStarRE.QPBT.AdmissibleParams) {α : Type*}
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : α → _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.MIPStarRE.QPBT.SubLineTriple P)) :
    _root_.MIPStarRE.QPBT.subLinePointDist P (_root_.MIPStarRE.QPBT.Distribution.bind μ ν) =
      _root_.MIPStarRE.QPBT.Distribution.bind μ (fun a => _root_.MIPStarRE.QPBT.subLinePointDist P (ν a)) := by
  classical
  unfold _root_.MIPStarRE.QPBT.subLinePointDist
  rw [_root_.MIPStarRE.QPBT.Distribution.prod_bind_left, _root_.MIPStarRE.QPBT.Distribution.bind_map]

/-! ## The projected marginals of one branch at one extended coordinate -/

/-- One branch of the sampling procedure, read at a fixed extended coordinate,
is the law of the triple decoded from the auxiliary randomness of that
coordinate.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_eq_bind (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind) :
    _root_.MIPStarRE.QPBT.subLineBranchDist P kind =
      _root_.MIPStarRE.QPBT.Distribution.bind (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin (2 * P.m + 2))) fun k =>
        (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.SubLinePointDir P))
            (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
              (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k)))).map
          fun w => _root_.MIPStarRE.QPBT.subLineTripleOf P kind k w := by
  classical
  rw [_root_.MIPStarRE.QPBT.subLineBranchDist, _root_.MIPStarRE.QPBT.subLineSamplingDist, _root_.MIPStarRE.QPBT.Distribution.bind_map]
  refine _root_.MIPStarRE.QPBT.Distribution.bind_congr_support _ _ _ fun k _ => ?_
  rw [_root_.MIPStarRE.QPBT.Distribution.map_map]

/-- The `X` marginal of a uniform point of the extended line of one branch at
one extended coordinate is the `X` component law of the pair of indices of
that branch.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_map_subLineXProjection_at (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (kind : _root_.MIPStarRE.QPBT.LineKind) (k : Fin (2 * P.m + 2)) :
    (_root_.MIPStarRE.QPBT.subLinePointDist P
        ((_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.SubLinePointDir P))
            (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
              (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k)))).map
          fun w => _root_.MIPStarRE.QPBT.subLineTripleOf P kind k w)).map _root_.MIPStarRE.QPBT.subLineXProjection =
      _root_.MIPStarRE.QPBT.subLineXComponentDist P
        (kind, (_root_.MIPStarRE.QPBT.subLineXIndex P k, _root_.MIPStarRE.QPBT.subLineZIndex P k)) := by
  classical
  unfold _root_.MIPStarRE.QPBT.subLinePointDist
  rw [_root_.MIPStarRE.QPBT.Distribution.prod_map_left, _root_.MIPStarRE.QPBT.Distribution.map_map, _root_.MIPStarRE.QPBT.Distribution.map_map]
  exact _root_.MIPStarRE.QPBT.subLineBranchSamplingData_map_projX P kind k

/-- The `Z` marginal of a uniform point of the extended line of one branch at
one extended coordinate is the `Z` component law of the pair of indices of
that branch.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_map_subLineZProjection_at (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (kind : _root_.MIPStarRE.QPBT.LineKind) (k : Fin (2 * P.m + 2)) :
    (_root_.MIPStarRE.QPBT.subLinePointDist P
        ((_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.SubLinePointDir P))
            (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineXIndex P k))
              (_root_.MIPStarRE.QPBT.subLineSeedDist P (_root_.MIPStarRE.QPBT.subLineZIndex P k)))).map
          fun w => _root_.MIPStarRE.QPBT.subLineTripleOf P kind k w)).map _root_.MIPStarRE.QPBT.subLineZProjection =
      _root_.MIPStarRE.QPBT.subLineZComponentDist P
        (kind, (_root_.MIPStarRE.QPBT.subLineXIndex P k, _root_.MIPStarRE.QPBT.subLineZIndex P k)) := by
  classical
  unfold _root_.MIPStarRE.QPBT.subLinePointDist
  rw [_root_.MIPStarRE.QPBT.Distribution.prod_map_left, _root_.MIPStarRE.QPBT.Distribution.map_map, _root_.MIPStarRE.QPBT.Distribution.map_map]
  exact _root_.MIPStarRE.QPBT.subLineBranchSamplingData_map_projZ P kind k

/-! ## The mixing law of the two indices -/





/-- The mixing law has total mass one. -/
theorem subLineComponentDist_isProbability (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (_root_.MIPStarRE.QPBT.subLineComponentDist P).IsProbability := by
  refine _root_.MIPStarRE.QPBT.Distribution.bind_isProbability _ _
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) fun c _ => ?_
  fin_cases c
  · exact _root_.LIDT.MIPStarRE.LDT.Distribution.IsProbability.map
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) _
  · exact _root_.LIDT.MIPStarRE.LDT.Distribution.IsProbability.map
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) _

/-! ## The two projected marginals of one branch -/

/-- The `X` marginal of a uniform point of the extended line of one branch is
the mixture, along the pair of source indices of a uniform extended
coordinate, of the `X` component laws.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_map_subLineXProjection (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (kind : _root_.MIPStarRE.QPBT.LineKind) :
    (_root_.MIPStarRE.QPBT.subLinePointDist P (_root_.MIPStarRE.QPBT.subLineBranchDist P kind)).map _root_.MIPStarRE.QPBT.subLineXProjection =
      _root_.MIPStarRE.QPBT.Distribution.bind (_root_.MIPStarRE.QPBT.subLineComponentBranch P kind)
        (_root_.MIPStarRE.QPBT.subLineXComponentDist P) := by
  classical
  rw [_root_.MIPStarRE.QPBT.subLineBranchDist_eq_bind, _root_.MIPStarRE.QPBT.subLinePointDist_bind, _root_.MIPStarRE.QPBT.Distribution.bind_map,
    _root_.MIPStarRE.QPBT.subLineComponentBranch, _root_.MIPStarRE.QPBT.Distribution.bind_map_left]
  refine _root_.MIPStarRE.QPBT.Distribution.bind_congr_support _ _ _ fun k _ => ?_
  exact _root_.MIPStarRE.QPBT.subLineBranchDist_map_subLineXProjection_at P kind k

/-- The `Z` marginal of a uniform point of the extended line of one branch is
the mixture, along the pair of source indices of a uniform extended
coordinate, of the `Z` component laws.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineBranchDist_map_subLineZProjection (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (kind : _root_.MIPStarRE.QPBT.LineKind) :
    (_root_.MIPStarRE.QPBT.subLinePointDist P (_root_.MIPStarRE.QPBT.subLineBranchDist P kind)).map _root_.MIPStarRE.QPBT.subLineZProjection =
      _root_.MIPStarRE.QPBT.Distribution.bind (_root_.MIPStarRE.QPBT.subLineComponentBranch P kind)
        (_root_.MIPStarRE.QPBT.subLineZComponentDist P) := by
  classical
  rw [_root_.MIPStarRE.QPBT.subLineBranchDist_eq_bind, _root_.MIPStarRE.QPBT.subLinePointDist_bind, _root_.MIPStarRE.QPBT.Distribution.bind_map,
    _root_.MIPStarRE.QPBT.subLineComponentBranch, _root_.MIPStarRE.QPBT.Distribution.bind_map_left]
  refine _root_.MIPStarRE.QPBT.Distribution.bind_congr_support _ _ _ fun k _ => ?_
  exact _root_.MIPStarRE.QPBT.subLineBranchDist_map_subLineZProjection_at P kind k

/-! ## The two projected marginals of the sub-line law -/

/-- The `X` point marginal of the sub-line law is the mixture of the `X`
component laws along the mixing law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineDist_map_subLineXProjection (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (_root_.MIPStarRE.QPBT.subLinePointDist P (_root_.MIPStarRE.QPBT.subLineDist P)).map _root_.MIPStarRE.QPBT.subLineXProjection =
      _root_.MIPStarRE.QPBT.Distribution.bind (_root_.MIPStarRE.QPBT.subLineComponentDist P) (_root_.MIPStarRE.QPBT.subLineXComponentDist P) := by
  classical
  rw [_root_.MIPStarRE.QPBT.subLineDist, _root_.MIPStarRE.QPBT.subLinePointDist_bind, _root_.MIPStarRE.QPBT.Distribution.bind_map,
    _root_.MIPStarRE.QPBT.subLineComponentDist, _root_.MIPStarRE.QPBT.Distribution.bind_bind]
  refine _root_.MIPStarRE.QPBT.Distribution.bind_congr_support _ _ _ fun c _ => ?_
  fin_cases c
  · exact _root_.MIPStarRE.QPBT.subLineBranchDist_map_subLineXProjection P .axis
  · exact _root_.MIPStarRE.QPBT.subLineBranchDist_map_subLineXProjection P .diagonal

/-- The `Z` point marginal of the sub-line law is the mixture of the `Z`
component laws along the mixing law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineDist_map_subLineZProjection (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (_root_.MIPStarRE.QPBT.subLinePointDist P (_root_.MIPStarRE.QPBT.subLineDist P)).map _root_.MIPStarRE.QPBT.subLineZProjection =
      _root_.MIPStarRE.QPBT.Distribution.bind (_root_.MIPStarRE.QPBT.subLineComponentDist P) (_root_.MIPStarRE.QPBT.subLineZComponentDist P) := by
  classical
  rw [_root_.MIPStarRE.QPBT.subLineDist, _root_.MIPStarRE.QPBT.subLinePointDist_bind, _root_.MIPStarRE.QPBT.Distribution.bind_map,
    _root_.MIPStarRE.QPBT.subLineComponentDist, _root_.MIPStarRE.QPBT.Distribution.bind_bind]
  refine _root_.MIPStarRE.QPBT.Distribution.bind_congr_support _ _ _ fun c _ => ?_
  fin_cases c
  · exact _root_.MIPStarRE.QPBT.subLineBranchDist_map_subLineZProjection P .axis
  · exact _root_.MIPStarRE.QPBT.subLineBranchDist_map_subLineZProjection P .diagonal

/-- The two one-point projected marginals of the sub-line law are mixtures of
the restricted product laws along one common mixing law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem subLineDist_source_mixture (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    ∃ components : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.MIPStarRE.QPBT.SubLineComponent P),
      components.IsProbability ∧
        (_root_.MIPStarRE.QPBT.subLinePointDist P (_root_.MIPStarRE.QPBT.subLineDist P)).map _root_.MIPStarRE.QPBT.subLineXProjection =
          _root_.MIPStarRE.QPBT.Distribution.bind components (_root_.MIPStarRE.QPBT.subLineXComponentDist P) ∧
        (_root_.MIPStarRE.QPBT.subLinePointDist P (_root_.MIPStarRE.QPBT.subLineDist P)).map _root_.MIPStarRE.QPBT.subLineZProjection =
          _root_.MIPStarRE.QPBT.Distribution.bind components (_root_.MIPStarRE.QPBT.subLineZComponentDist P) :=
  ⟨_root_.MIPStarRE.QPBT.subLineComponentDist P, _root_.MIPStarRE.QPBT.subLineComponentDist_isProbability P,
    _root_.MIPStarRE.QPBT.subLineDist_map_subLineXProjection P,
    _root_.MIPStarRE.QPBT.subLineDist_map_subLineZProjection P⟩

end

end MIPStarRE.QPBT

/-!
# Combined lines and restricted line distributions

This module states the construction of the joint X/Z line measurements, the
mixture and error-inflation estimates for restricted line distributions, and
the sub-line distribution used to combine the two bases.  The extended line
in the sub-line construction uses the directly indexed carrier, so the
sub-line statement is a formalization auxiliary assertion and carries no
divisibility hypothesis at dimension `2 * m + 2`.

## References

The declarations formalize `lem:qld-xz-lines` and
`lem:restricted-line-mixture-bounds` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`; `exists_subLineWitness`
instead supports `lem:qld-sublines` through the directly indexed extended-line
carrier and probability law.  Their paper sources
are `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882-894`
and `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1038-1069`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum



/-! ## Combined line measurements -/






/-! The source-facing declaration below supplies the point witness produced by
`lem:qld-4-10` existentially.  The `_ofPointsWitness` companion above is the
conditional form for a supplied polynomially controlled point family. -/



/-! ## Restricted line distributions -/











/-! ## The sub-line distribution -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    Nonempty (_root_.MIPStarRE.QPBT.SubLineWitness P) := by
  refine ⟨{ D := _root_.MIPStarRE.QPBT.subLineDist P
            isProbability := _root_.MIPStarRE.QPBT.subLineDist_isProbability P
            extended_marginal := _root_.MIPStarRE.QPBT.subLineDist_map_fst P
            incidence := ?_
            compatibility := ?_
            source_mixture := _root_.MIPStarRE.QPBT.subLineDist_source_mixture P
            axis_closure := ?_ }⟩
  · intro sample hsample u hu
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      _root_.MIPStarRE.QPBT.exists_samplingData_of_mem_subLineDist_support P hsample
    exact _root_.MIPStarRE.QPBT.subLineTripleOf_incidence P kind k w hx hz hu
  · intro sample hsample
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      _root_.MIPStarRE.QPBT.exists_samplingData_of_mem_subLineDist_support P hsample
    exact _root_.MIPStarRE.QPBT.subLineTripleOf_compatibility P kind k w hx hz
  · intro sample hsample haxis
    obtain ⟨kind, k, w, hx, hz, rfl⟩ :=
      _root_.MIPStarRE.QPBT.exists_samplingData_of_mem_subLineDist_support P hsample
    exact _root_.MIPStarRE.QPBT.subLineTripleOf_axis_closure P kind k w haxis
