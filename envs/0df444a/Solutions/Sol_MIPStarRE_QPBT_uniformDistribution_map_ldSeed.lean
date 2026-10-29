-- Prove2me | solution 1 for MIPStarRE.QPBT.uniformDistribution_map_ldSeed
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:01:05.521793+00:00
-- url     : https://prove2.me/submissions/074fe090-8388-4331-a47d-a7316536f562

-- Generated proof for MIPStarRE.QPBT.uniformDistribution_map_ldSeed.
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
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
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

/-!
# Low-degree sampling and polynomial measurements

The low-degree question laws have uniform point and coordinate-index marginals,
and every sampled line is incident to its paired point.  Polynomial outcomes
are bounded multivariate polynomials. The soundness theorem using these
definitions is proved in `LowDegreeGameTheorems`.

## References

The principal definition and theorem are blueprint `def:ld-meas` and
`lem:ld-soundness`. Their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287,392-480`.
The dimension-divisibility hypothesis is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum



/-!
### Formalization-only auxiliary facts about the ambient low-degree space
-/

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams) :
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map _root_.MIPStarRE.QPBT.LdSpace.seed =
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ScalarQ L) := by
  have hsplit : (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map (_root_.MIPStarRE.QPBT.ldSpaceSplit L) =
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution (((Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) × _root_.MIPStarRE.QPBT.ScalarQ L) × (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)) :=
    _root_.MIPStarRE.QPBT.uniformDistribution_map_equiv (_root_.MIPStarRE.QPBT.ldSpaceSplit L)
  calc
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map _root_.MIPStarRE.QPBT.LdSpace.seed
        = (((_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map (_root_.MIPStarRE.QPBT.ldSpaceSplit L)).map
            Prod.fst).map Prod.snd := by
          rw [_root_.MIPStarRE.QPBT.Distribution.map_map, _root_.MIPStarRE.QPBT.Distribution.map_map]
          rfl
    _ = ((_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          (((Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) × _root_.MIPStarRE.QPBT.ScalarQ L) × (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))).map
            Prod.fst).map Prod.snd := by rw [hsplit]
    _ = (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ((Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) × _root_.MIPStarRE.QPBT.ScalarQ L)).map Prod.snd := by
          rw [_root_.MIPStarRE.QPBT.uniformDistribution_map_fst]
    _ = _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ScalarQ L) := _root_.MIPStarRE.QPBT.uniformDistribution_map_snd
