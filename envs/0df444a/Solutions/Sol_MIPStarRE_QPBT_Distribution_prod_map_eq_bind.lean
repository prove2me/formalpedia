-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.prod_map_eq_bind
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:23:53.937259+00:00
-- url     : https://prove2.me/submissions/b56e4ead-7d9c-453f-9264-b8f37bd8bb9b

-- Generated proof for MIPStarRE.QPBT.Distribution.prod_map_eq_bind.
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

theorem solution {α β γ : Type*} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : _root_.LIDT.MIPStarRE.LDT.Distribution β)
    (g : α × β → γ) :
    (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).map g =
      _root_.MIPStarRE.QPBT.Distribution.bind μ (fun a => ν.map (fun b => g (a, b))) := by
  classical
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · change (μ.support ×ˢ ν.support).image g =
      μ.support.biUnion (fun a => ν.support.image (fun b => g (a, b)))
    ext c
    simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_product,
      Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, b, ⟨ha, hb⟩, rfl⟩
  · funext c
    change (∑ p ∈ (μ.support ×ˢ ν.support).filter (fun p => g p = c),
        μ.weight p.1 * ν.weight p.2) =
      ∑ a ∈ μ.support, μ.weight a *
        ∑ b ∈ ν.support.filter (fun b => g (a, b) = c), ν.weight b
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : g (a, b) = c
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero]
