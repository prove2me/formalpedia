-- Prove2me | solution 1 for MIPStarRE.QPBT.collision_bound_of_fiber_averages
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:51:53.465705+00:00
-- url     : https://prove2.me/submissions/9ae196d8-eda3-4bdb-9eac-4e9988559996

-- Generated proof for MIPStarRE.QPBT.collision_bound_of_fiber_averages.
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
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Conditional collision bounds from fiber averages

This module converts an unnormalized collision estimate on every first-question
fiber into the positive-mass conditional collision predicate used by the
pasting theorem.

## References

The conditional collision hypothesis is from `lem:pasting`,
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`. Its use in
the QPBT combining argument occurs at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

theorem solution {X Y₁ Y₂ R₂ Γ₂ : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₂] (dist : _root_.LIDT.MIPStarRE.LDT.Distribution ((X × Y₁) × Y₂))
    (eval₂ : Γ₂ → Y₂ → R₂) (eta : ℝ)
    (hbound : ∀ fixed : X × Y₁, ∀ first second : Γ₂, first ≠ second →
      _root_.LIDT.MIPStarRE.LDT.avgOver dist (fun sample => if sample.1 = fixed then
        (if eval₂ first sample.2 = eval₂ second sample.2 then 1 else 0) else 0) ≤
      eta * _root_.LIDT.MIPStarRE.LDT.avgOver dist (fun sample => if sample.1 = fixed then 1 else 0)) :
    _root_.MIPStarRE.QPBT.HasConditionalCollisionBound dist eval₂ eta := by
  classical
  intro question point _ first second hne
  have havg (value : ((X × Y₁) × Y₂) → ℝ) :
      _root_.LIDT.MIPStarRE.LDT.avgOver dist value = ∑ sample, dist.weight sample * value sample := by
    exact (dist.sum_univ_eq_sum_support _ (fun sample hout => by
      rw [dist.outsideSupport sample hout, zero_mul])).symm
  have hmass : (dist.map Prod.fst).weight (question, point) =
      _root_.LIDT.MIPStarRE.LDT.avgOver dist (fun sample => if sample.1 = (question, point) then 1 else 0) := by
    rw [_root_.LIDT.MIPStarRE.LDT.Distribution.map_weight]
    unfold _root_.LIDT.MIPStarRE.LDT.avgOver
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro sample _
    by_cases hfixed : sample.1 = (question, point) <;> simp [hfixed]
  rw [hmass]
  have h := hbound (question, point) first second hne
  simpa [havg, Fintype.sum_prod_type, mul_ite] using h
