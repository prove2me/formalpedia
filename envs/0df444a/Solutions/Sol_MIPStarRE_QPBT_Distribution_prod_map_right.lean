-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.prod_map_right
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:23:53.830906+00:00
-- url     : https://prove2.me/submissions/90765bbc-1ade-4bb7-844f-f55748490a3f

-- Generated proof for MIPStarRE.QPBT.Distribution.prod_map_right.
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

theorem solution {α β γ : Type*} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : _root_.LIDT.MIPStarRE.LDT.Distribution β)
    (g : β → γ) :
    _root_.MIPStarRE.QPBT.Distribution.prod μ (ν.map g) =
      (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).map (fun w => (w.1, g w.2)) := by
  classical
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · change μ.support ×ˢ (ν.support.image g) =
      (μ.support ×ˢ ν.support).image (fun w => (w.1, g w.2))
    ext w
    obtain ⟨x, c⟩ := w
    simp only [Finset.mem_product, Finset.mem_image, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨hx, b, hb, rfl⟩
      exact ⟨x, b, ⟨hx, hb⟩, rfl, rfl⟩
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl, rfl⟩
      exact ⟨ha, b, hb, rfl⟩
  · funext w
    obtain ⟨x, c⟩ := w
    have hfilter :
        (μ.support ×ˢ ν.support).filter (fun p => (p.1, g p.2) = (x, c)) =
          (μ.support.filter (fun a => a = x)) ×ˢ
            (ν.support.filter (fun b => g b = c)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
      tauto
    have hx : ∑ a ∈ μ.support.filter (fun a => a = x), μ.weight a =
        μ.weight x := by
      rw [Finset.filter_eq' μ.support x]
      by_cases hmem : x ∈ μ.support
      · rw [if_pos hmem, Finset.sum_singleton]
      · rw [if_neg hmem, Finset.sum_empty, μ.outsideSupport x hmem]
    change μ.weight x * (ν.map g).weight c =
      ∑ p ∈ (μ.support ×ˢ ν.support).filter (fun p => (p.1, g p.2) = (x, c)),
        μ.weight p.1 * ν.weight p.2
    rw [hfilter, Finset.sum_product,
      Finset.sum_congr rfl (fun a _ =>
        (Finset.mul_sum (ν.support.filter (fun b => g b = c))
          (fun b => ν.weight b) (μ.weight a)).symm),
      ← Finset.sum_mul, hx]
    rfl
