-- Prove2me | solution 1 for MIPStarRE.QPBT.restrict_uniform_prod_snd
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:28:22.039559+00:00
-- url     : https://prove2.me/submissions/bca5675f-83d4-4d35-be5b-bcf48be678bd

-- Generated proof for MIPStarRE.QPBT.restrict_uniform_prod_snd.
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
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Theorems.Thm_MIPStarRE_QPBT_Distribution_restrict_prod_snd
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_prod

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
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



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT





/-! ## Nonemptiness of the support of a probability law -/



/-! ## Push-forward of one factor of a product -/



/-! ## The first marginal of a product -/





/-! ## A product as a dependent mixture -/



/-! ## The support and the weight of a product -/





/-! ## Push-forward along a bijection -/



/-! ## Push-forward of the second factor of a product -/



/-! ## Uniform laws on products -/





/-! ## Conditioning one factor of a product -/

theorem solution {α β : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β] (p : β → Prop)
    [DecidablePred p]
    (hpos : 0 < ∑ b ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β).support.filter p,
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β).weight b)
    (hpos' : 0 < ∑ w ∈ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (α × β)).support.filter
        (fun w => p w.2), (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (α × β)).weight w) :
    _root_.MIPStarRE.QPBT.Distribution.restrict (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (α × β)) (fun w => p w.2)
        hpos' =
      _root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α)
        (_root_.MIPStarRE.QPBT.Distribution.restrict (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β) p hpos) := by
  classical
  have hpos'' : 0 < ∑ w ∈ (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α)
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β)).support.filter (fun w => p w.2),
      (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α)
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β)).weight w := by
    rw [← _root_.MIPStarRE.QPBT.uniformDistribution_prod]
    exact hpos'
  rw [_root_.MIPStarRE.QPBT.Distribution.restrict_congr (_root_.MIPStarRE.QPBT.uniformDistribution_prod α β)
    (fun w => p w.2) hpos' hpos'']
  exact _root_.MIPStarRE.QPBT.Distribution.restrict_prod_snd _ _
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability α) p hpos hpos''
