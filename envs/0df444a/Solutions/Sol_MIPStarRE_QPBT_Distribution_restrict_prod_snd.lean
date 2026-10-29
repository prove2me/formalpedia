-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.restrict_prod_snd
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:23:54.148117+00:00
-- url     : https://prove2.me/submissions/4adf94f3-b10e-4bae-a67b-148688b4902e

-- Generated proof for MIPStarRE.QPBT.Distribution.restrict_prod_snd.
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

theorem solution {α β : Type*} [DecidableEq α]
    [DecidableEq β] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : _root_.LIDT.MIPStarRE.LDT.Distribution β)
    (hμ : μ.IsProbability) (p : β → Prop) [DecidablePred p]
    (hpos : 0 < ∑ b ∈ ν.support.filter p, ν.weight b)
    (hpos' : 0 < ∑ w ∈ (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).support.filter
        (fun w => p w.2), (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).weight w) :
    _root_.MIPStarRE.QPBT.Distribution.restrict (_root_.MIPStarRE.QPBT.Distribution.prod μ ν) (fun w => p w.2) hpos' =
      _root_.MIPStarRE.QPBT.Distribution.prod μ (_root_.MIPStarRE.QPBT.Distribution.restrict ν p hpos) := by
  classical
  have hprodsupp : (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).support =
      μ.support ×ˢ ν.support := rfl
  have hsupp : (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).support.filter (fun w => p w.2) =
      μ.support ×ˢ (ν.support.filter p) := by
    rw [hprodsupp]
    ext w
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  have hmass : (∑ w ∈ (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).support.filter
        (fun w => p w.2), (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).weight w) =
      ∑ b ∈ ν.support.filter p, ν.weight b := by
    rw [hsupp]
    have h1 : (∑ w ∈ μ.support ×ˢ (ν.support.filter p),
        (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).weight w) =
        ∑ a ∈ μ.support, ∑ b ∈ ν.support.filter p,
          μ.weight a * ν.weight b := by
      rw [Finset.sum_product]
      rfl
    rw [h1, Finset.sum_congr rfl fun a _ =>
        (Finset.mul_sum (ν.support.filter p) (fun b => ν.weight b)
          (μ.weight a)).symm,
      ← Finset.sum_mul, hμ.weight_sum_eq_one, one_mul]
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · show (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).support.filter (fun w => p w.2) =
      μ.support ×ˢ (ν.support.filter p)
    exact hsupp
  · funext w
    show (if p w.2 then (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).weight w /
        ∑ c ∈ (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).support.filter (fun w => p w.2),
          (_root_.MIPStarRE.QPBT.Distribution.prod μ ν).weight c else 0) =
      μ.weight w.1 * (if p w.2 then ν.weight w.2 /
        ∑ c ∈ ν.support.filter p, ν.weight c else 0)
    rw [hmass]
    by_cases h : p w.2
    · rw [if_pos h, if_pos h]
      show μ.weight w.1 * ν.weight w.2 / _ = _
      rw [mul_div_assoc]
    · rw [if_neg h, if_neg h, mul_zero]
