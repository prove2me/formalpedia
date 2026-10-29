-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.prod_map_left
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:23:53.797402+00:00
-- url     : https://prove2.me/submissions/b7582222-bafd-42f3-a538-b50a902efb57

-- Generated proof for MIPStarRE.QPBT.Distribution.prod_map_left.
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

theorem solution {α β γ : Type*} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : _root_.LIDT.MIPStarRE.LDT.Distribution β)
    (f : α → γ) :
    _root_.MIPStarRE.QPBT.Distribution.prod (μ.map f) ν =
      (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).map (fun w => (f w.1, w.2)) := by
  classical
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · change (μ.support.image f) ×ˢ ν.support =
      (μ.support ×ˢ ν.support).image (fun w => (f w.1, w.2))
    ext w
    obtain ⟨c, y⟩ := w
    simp only [Finset.mem_product, Finset.mem_image, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hy⟩
      exact ⟨a, y, ⟨ha, hy⟩, rfl, rfl⟩
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hb⟩
  · funext w
    obtain ⟨c, y⟩ := w
    have hfilter :
        (μ.support ×ˢ ν.support).filter (fun p => (f p.1, p.2) = (c, y)) =
          (μ.support.filter (fun a => f a = c)) ×ˢ
            (ν.support.filter (fun b => b = y)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
      tauto
    have hy : ∑ b ∈ ν.support.filter (fun b => b = y), ν.weight b =
        ν.weight y := by
      rw [Finset.filter_eq' ν.support y]
      by_cases hmem : y ∈ ν.support
      · rw [if_pos hmem, Finset.sum_singleton]
      · rw [if_neg hmem, Finset.sum_empty, ν.outsideSupport y hmem]
    change (μ.map f).weight c * ν.weight y =
      ∑ p ∈ (μ.support ×ˢ ν.support).filter (fun p => (f p.1, p.2) = (c, y)),
        μ.weight p.1 * ν.weight p.2
    rw [hfilter, Finset.sum_product,
      Finset.sum_congr rfl
        (fun a _ => (Finset.mul_sum (ν.support.filter (fun b => b = y))
          (fun b => ν.weight b) (μ.weight a)).symm),
      hy, ← Finset.sum_mul]
    rfl
