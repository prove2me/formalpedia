-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.cardRatio_mul_avgOver_filter
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:12:24.081991+00:00
-- url     : https://prove2.me/submissions/7e58be05-ef4e-453a-85b4-f5f689ff658d

-- Generated proof for MIPStarRE.QPBT.WinImplications.cardRatio_mul_avgOver_filter.
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
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/-!
# Averaging lemmas for winning implications

This module derives the finite conditioning and fixed-edge rejection bounds
used by all seven exact winning implications.

## References

The formalization-only averaging and conditioning auxiliaries support items 1–7
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications

theorem solution
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (p : X → Prop) [DecidablePred p] (hp : (Finset.univ.filter p).Nonempty)
    (f : X → ℝ) :
    ((Finset.univ.filter p).card : ℝ) / Fintype.card X *
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset (Finset.univ.filter p)) f =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) (fun x => if p x then f x else 0) := by
  have hcardX : (Fintype.card X : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcardp : ((Finset.univ.filter p).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hp
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver _root_.LIDT.MIPStarRE.LDT.uniformDistribution
  simp only [_root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset_support,
    _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset_weight, Finset.mem_filter, Finset.mem_univ,
    true_and, if_true]
  rw [Finset.card_univ]
  rw [show (∑ x ∈ Finset.univ.filter p,
      (if p x then 1 / ((Finset.univ.filter p).card : ℝ) else 0) * f x) =
      ∑ x ∈ Finset.univ.filter p,
        1 / ((Finset.univ.filter p).card : ℝ) * f x by
    apply Finset.sum_congr rfl
    intro x hx
    simp [(Finset.mem_filter.mp hx).2]]
  rw [show (∑ x ∈ Finset.univ.filter p,
      1 / ((Finset.univ.filter p).card : ℝ) * f x) =
      1 / ((Finset.univ.filter p).card : ℝ) *
        ∑ x ∈ Finset.univ.filter p, f x by
    rw [Finset.mul_sum]]
  rw [show (∑ x ∈ Finset.univ,
      1 / (Fintype.card X : ℝ) * (if p x then f x else 0)) =
      1 / (Fintype.card X : ℝ) * ∑ x ∈ Finset.univ.filter p, f x by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : p x <;> simp [hx]]
  field_simp
