-- Prove2me | solution 1 for MIPStarRE.QPBT.restrict_uniform_ldSeedEvent_map_block
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:38:59.208081+00:00
-- url     : https://prove2.me/submissions/3004ee1b-f730-4ade-a0ed-831994bdaeff

-- Generated proof for MIPStarRE.QPBT.restrict_uniform_ldSeedEvent_map_block.
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
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineBlocks
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineSupport
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_Distribution_restrict_map
import Theorems.Thm_MIPStarRE_QPBT_ldSeedEvent_positive
import Theorems.Thm_MIPStarRE_QPBT_restrict_uniform_prod_snd

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















/-- Formalization-only lemma: the second marginal of the uniform distribution
on a product is uniform.  This is `lem:uniform-product-second-marginal` in
blueprint chapter 13. -/
theorem uniformDistribution_map_snd {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] :
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (α × β)).map Prod.snd = _root_.LIDT.MIPStarRE.LDT.uniformDistribution β := by
  refine _root_.MIPStarRE.QPBT.uniformDistribution_map_of_card_fiber _ (Fintype.card α) fun b => ?_
  have hfilter : ((Finset.univ : Finset (α × β)).filter fun p => p.2 = b)
      = (Finset.univ : Finset α) ×ˢ ({b} : Finset β) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
  rw [hfilter, Finset.card_product]
  simp





/-! ## Elementary rewriting of finite distributions -/







/-! ## Reindexing a dependent mixture -/







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





/-! ## Push-forward along a bijection -/



/-! ## Push-forward of the second factor of a product -/



/-! ## Uniform laws on products -/



/-- Formalization-only auxiliary: the mass of an event depending only on the
second factor is the same under a uniform product law and under the uniform
law of that factor.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_snd_event_mass {α β : Type*} [Fintype α]
    [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β]
    (p : β → Prop) [DecidablePred p] :
    ∑ w ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (α × β)).support.filter (fun w => p w.2),
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (α × β)).weight w =
      ∑ b ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β).support.filter p,
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β).weight b := by
  classical
  rw [_root_.MIPStarRE.QPBT.Distribution.sum_filter_weight_eq_avgOver,
    _root_.MIPStarRE.QPBT.Distribution.sum_filter_weight_eq_avgOver,
    ← _root_.MIPStarRE.QPBT.uniformDistribution_map_snd (α := α) (β := β), _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]

/-! ## Conditioning one factor of a product -/

/-- Formalization-only auxiliary: normalized restriction depends on the
restricted law only through its support and weights.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.restrict_congr {α : Type*} [DecidableEq α]
    {μ ν : _root_.LIDT.MIPStarRE.LDT.Distribution α} (h : μ = ν) (p : α → Prop) [DecidablePred p]
    (hμ : 0 < ∑ a ∈ μ.support.filter p, μ.weight a)
    (hν : 0 < ∑ a ∈ ν.support.filter p, ν.weight a) :
    _root_.MIPStarRE.QPBT.Distribution.restrict μ p hμ = _root_.MIPStarRE.QPBT.Distribution.restrict ν p hν := by
  subst h
  rfl





/-! ## Conditioning the first factor of a product -/







/-! ## Restriction of a push-forward -/



end MIPStarRE.QPBT

/-!
# Independent blocks of the restricted line-point laws

This module isolates the independent generating blocks of the restricted
line-point laws used by the sampling procedure of the sub-line lemma.  A
uniformly sampled low-degree vector splits into a point block and a
seed-direction block; the coordinate-index event constrains only the second
block, so conditioning on it leaves the point block uniform and independent.
The conditioned seed-direction block is the fresh diagonal direction pair of
the sub-line construction, and the uniform mixture of those pairs over the
coordinate index is the unconditioned law.

## References

The generating descriptions support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws themselves are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! ## The block decomposition of an ambient low-degree vector -/











/-! ## Fresh diagonal direction pairs -/







/-! ## Independence of the point block under the coordinate-index event -/

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams) (i : Fin L.m) :
    (_root_.MIPStarRE.QPBT.Distribution.restrict (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)) (_root_.MIPStarRE.QPBT.ldSeedEvent L i)
        (_root_.MIPStarRE.QPBT.ldSeedEvent_positive L i)).map (_root_.MIPStarRE.QPBT.ldSpaceBlockEquiv L) =
      _root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
        (_root_.MIPStarRE.QPBT.freshDiagonalPairDist L i) := by
  classical
  have hequiv := _root_.MIPStarRE.QPBT.uniformDistribution_map_equiv (_root_.MIPStarRE.QPBT.ldSpaceBlockEquiv L)
  have hprod : 0 < ∑ w ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ((Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) ×
          (_root_.MIPStarRE.QPBT.ScalarQ L × (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)))).support.filter
        (fun w => _root_.MIPStarRE.QPBT.ldSeedDirEvent L i w.2),
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ((Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) ×
        (_root_.MIPStarRE.QPBT.ScalarQ L × (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)))).weight w := by
    rw [_root_.MIPStarRE.QPBT.uniformDistribution_snd_event_mass]
    exact _root_.MIPStarRE.QPBT.ldSeedDirEvent_positive L i
  have hposA : 0 < ∑ w ∈ ((_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map
        (_root_.MIPStarRE.QPBT.ldSpaceBlockEquiv L)).support.filter
        (fun w => _root_.MIPStarRE.QPBT.ldSeedDirEvent L i w.2),
      ((_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map
        (_root_.MIPStarRE.QPBT.ldSpaceBlockEquiv L)).weight w := by
    rw [hequiv]
    exact hprod
  rw [← _root_.MIPStarRE.QPBT.Distribution.restrict_map (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L))
      (_root_.MIPStarRE.QPBT.ldSpaceBlockEquiv L) (fun w => _root_.MIPStarRE.QPBT.ldSeedDirEvent L i w.2)
      (_root_.MIPStarRE.QPBT.ldSeedEvent L i) (fun _ => Iff.rfl) hposA (_root_.MIPStarRE.QPBT.ldSeedEvent_positive L i),
    _root_.MIPStarRE.QPBT.Distribution.restrict_congr hequiv (fun w => _root_.MIPStarRE.QPBT.ldSeedDirEvent L i w.2)
      hposA hprod,
    _root_.MIPStarRE.QPBT.restrict_uniform_prod_snd (_root_.MIPStarRE.QPBT.ldSeedDirEvent L i)
      (_root_.MIPStarRE.QPBT.ldSeedDirEvent_positive L i) hprod]
  rfl
