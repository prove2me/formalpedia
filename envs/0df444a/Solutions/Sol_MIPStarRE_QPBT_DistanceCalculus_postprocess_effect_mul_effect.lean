-- Prove2me | solution 1 for MIPStarRE.QPBT.DistanceCalculus.postprocess_effect_mul_effect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:13:59.604991+00:00
-- url     : https://prove2.me/submissions/94e900ac-c6b4-4c99-834c-a28c91b621d7

-- Generated proof for MIPStarRE.QPBT.DistanceCalculus.postprocess_effect_mul_effect.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

theorem solution {ζ α ι : Type*}
    [Fintype ζ] [DecidableEq ζ] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement ζ ι)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : ζ → α) (b : α) (z : ζ) :
    (M.postprocess f).effect b * M.effect z =
      if f z = b then M.effect z else 0 := by
  classical
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_mul]
  calc
    ∑ y ∈ Finset.univ.filter (fun y => f y = b), M.effect y * M.effect z =
        ∑ y ∈ Finset.univ.filter (fun y => f y = b),
          if y = z then M.effect z else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hyz : y = z
      · subst y
        rw [if_pos rfl]
        exact (hM z).isIdempotentElem.eq
      · rw [if_neg hyz]
        exact _root_.MIPStarRE.QPBT.DistanceCalculus.projective_effect_mul_effect_eq_zero M hM hyz
    _ = if f z = b then M.effect z else 0 := by simp
