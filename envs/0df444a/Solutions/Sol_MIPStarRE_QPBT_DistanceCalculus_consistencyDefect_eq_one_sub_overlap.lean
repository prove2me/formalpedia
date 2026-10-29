-- Prove2me | solution 1 for MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:02:02.20092+00:00
-- url     : https://prove2.me/submissions/6c2462d1-1e0f-4d90-9937-c4d8c5ef1d27

-- Generated proof for MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_point_defect_eq

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective























































/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): the matrix-vector term in `consistencyDefect` is the state quadratic
form. -/
theorem consistency_term_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm (M.mulVec ψ))).re =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  rfl



































end MIPStarRE.QPBT.DistanceCalculus

/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

theorem solution {X α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (ψ : EuclideanSpace ℂ ι) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) :
    _root_.MIPStarRE.QPBT.consistencyDefect μ (fun x a => (A x).effect a)
        (fun x a => (B x).effect a) ψ =
      1 - _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (B x).effect a)) := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm]
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a, ∑ b, if a = b then 0 else
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (B x).effect b)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ‖ψ‖ ^ 2 - ∑ a,
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (B x).effect a)) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
      intro x
      exact _root_.MIPStarRE.QPBT.DistanceCalculus.point_defect_eq (A x) (B x) ψ
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun _ => ‖ψ‖ ^ 2) - _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a,
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((A x).effect a * (B x).effect a)) :=
      _root_.LIDT.MIPStarRE.LDT.avgOver_sub μ _ _
    _ = _ := by
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability μ hμ, hψ]
      norm_num
