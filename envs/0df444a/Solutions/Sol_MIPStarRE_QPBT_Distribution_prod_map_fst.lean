-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.prod_map_fst
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:23:53.739748+00:00
-- url     : https://prove2.me/submissions/f025a2b9-a37a-4f25-9cf8-5e2ce6ea88e2

-- Generated proof for MIPStarRE.QPBT.Distribution.prod_map_fst.
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

/-- A law of total mass one has a nonempty support.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.support_nonempty_of_isProbability {α : Type*}
    {μ : _root_.LIDT.MIPStarRE.LDT.Distribution α} (hμ : μ.IsProbability) : μ.support.Nonempty := by
  rw [← Finset.card_pos]
  by_contra hcard
  have hempty : μ.support = ∅ := by
    rw [← Finset.card_eq_zero]
    omega
  have h1 := hμ.weight_sum_eq_one
  rw [hempty] at h1
  simp at h1

/-! ## Push-forward of one factor of a product -/



/-! ## The first marginal of a product -/





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

theorem solution {α β : Type*} [DecidableEq α] [DecidableEq β]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : _root_.LIDT.MIPStarRE.LDT.Distribution β) (hν : ν.IsProbability) :
    (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).map Prod.fst = μ := by
  classical
  obtain ⟨b₀, hb₀⟩ := _root_.MIPStarRE.QPBT.Distribution.support_nonempty_of_isProbability hν
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · change (μ.support ×ˢ ν.support).image Prod.fst = μ.support
    ext a
    simp only [Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨x, y, ⟨hx, -⟩, rfl⟩
      exact hx
    · intro ha
      exact ⟨a, b₀, ⟨ha, hb₀⟩, rfl⟩
  · funext a
    have hfilter : (μ.support ×ˢ ν.support).filter (fun p => p.1 = a) =
        (μ.support.filter (fun x => x = a)) ×ˢ ν.support := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product]
      tauto
    have ha : ∑ x ∈ μ.support.filter (fun x => x = a), μ.weight x =
        μ.weight a := by
      rw [Finset.filter_eq' μ.support a]
      by_cases hmem : a ∈ μ.support
      · rw [if_pos hmem, Finset.sum_singleton]
      · rw [if_neg hmem, Finset.sum_empty, μ.outsideSupport a hmem]
    change (∑ p ∈ (μ.support ×ˢ ν.support).filter (fun p => p.1 = a),
      μ.weight p.1 * ν.weight p.2) = μ.weight a
    rw [hfilter, Finset.sum_product,
      Finset.sum_congr rfl
        (fun x _ => (Finset.mul_sum ν.support (fun b => ν.weight b)
          (μ.weight x)).symm),
      hν.weight_sum_eq_one]
    simpa using ha
