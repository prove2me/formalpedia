-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.restrict_prod_fst
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:34:37.460133+00:00
-- url     : https://prove2.me/submissions/daab8b84-7a9d-488a-96a7-205ac337b178

-- Generated proof for MIPStarRE.QPBT.Distribution.restrict_prod_fst.
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





/-! ## Conditioning one factor of a product -/







/-! ## Conditioning the first factor of a product -/

theorem solution {α β : Type*} [DecidableEq α]
    [DecidableEq β] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : _root_.LIDT.MIPStarRE.LDT.Distribution β)
    (hν : ν.IsProbability) (p : α → Prop) [DecidablePred p]
    (hpos : 0 < ∑ a ∈ μ.support.filter p, μ.weight a)
    (hpos' : 0 < ∑ w ∈ (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).support.filter
        (fun w => p w.1), (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).weight w) :
    _root_.MIPStarRE.QPBT.Distribution.restrict (_root_.MIPStarRE.QPBT.Distribution.prod μ ν) (fun w => p w.1) hpos' =
      _root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.Distribution.restrict μ p hpos) ν := by
  classical
  have hsupp : (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).support.filter (fun w => p w.1) =
      (μ.support.filter p) ×ˢ ν.support := by
    change (μ.support ×ˢ ν.support).filter (fun w => p w.1) =
      (μ.support.filter p) ×ˢ ν.support
    ext w
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  have hmass : (∑ w ∈ (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).support.filter
        (fun w => p w.1), (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).weight w) =
      ∑ a ∈ μ.support.filter p, μ.weight a := by
    rw [hsupp]
    have h1 : (∑ w ∈ (μ.support.filter p) ×ˢ ν.support,
        (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).weight w) =
        ∑ a ∈ μ.support.filter p, ∑ b ∈ ν.support,
          μ.weight a * ν.weight b := by
      rw [Finset.sum_product]
      rfl
    rw [h1, Finset.sum_congr rfl fun a _ =>
        (Finset.mul_sum ν.support (fun b => ν.weight b) (μ.weight a)).symm,
      hν.weight_sum_eq_one]
    simp
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · change (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).support.filter (fun w => p w.1) =
      (μ.support.filter p) ×ˢ ν.support
    exact hsupp
  · funext w
    change (if p w.1 then (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).weight w /
        ∑ c ∈ (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).support.filter (fun w => p w.1),
          (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).weight c else 0) =
      (if p w.1 then μ.weight w.1 /
        ∑ c ∈ μ.support.filter p, μ.weight c else 0) * ν.weight w.2
    rw [hmass]
    by_cases h : p w.1
    · rw [if_pos h, if_pos h, div_mul_eq_mul_div]
      rfl
    · rw [if_neg h, if_neg h, zero_mul]
