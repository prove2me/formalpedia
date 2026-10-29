-- Prove2me | solution 1 for MIPStarRE.QPBT.uniformDistribution_prod
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:25:35.044267+00:00
-- url     : https://prove2.me/submissions/43653cbb-0f32-4fa2-b509-76becab8a522

-- Generated proof for MIPStarRE.QPBT.uniformDistribution_prod.
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

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
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

theorem solution (α β : Type*) [Fintype α] [DecidableEq α]
    [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β] :
    _root_.LIDT.MIPStarRE.LDT.uniformDistribution (α × β) =
      _root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β) := by
  classical
  have ha : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := α)
  have hb : (Fintype.card β : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := β)
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · show (Finset.univ : Finset (α × β)) =
      (Finset.univ : Finset α).product (Finset.univ : Finset β)
    ext p
    simp
  · funext p
    show (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (α × β)).weight p =
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α).weight p.1 * (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β).weight p.2
    rw [_root_.MIPStarRE.QPBT.uniformDistribution_weight_apply, _root_.MIPStarRE.QPBT.uniformDistribution_weight_apply,
      _root_.MIPStarRE.QPBT.uniformDistribution_weight_apply, Fintype.card_prod]
    push_cast
    field_simp
