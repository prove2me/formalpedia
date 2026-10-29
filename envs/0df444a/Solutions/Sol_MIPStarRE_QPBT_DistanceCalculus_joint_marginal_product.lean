-- Prove2me | solution 1 for MIPStarRE.QPBT.DistanceCalculus.joint_marginal_product
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:18:24.129566+00:00
-- url     : https://prove2.me/submissions/c9db0d38-d4fd-4de4-a227-4adf9ce2e993

-- Generated proof for MIPStarRE.QPBT.DistanceCalculus.joint_marginal_product.
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
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_postprocess_effect_mul_effect

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

theorem solution {α β γ ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement ((α × β) × γ) ι)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M)
    (a : α) (b : β) (c : γ) :
    ((M.postprocess (fun abc => abc.1)).effect (a, b)) *
        ((M.postprocess (fun abc => (abc.1.1, abc.2))).effect (a, c)) =
      M.effect ((a, b), c) := by
  classical
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [Finset.mul_sum]
  calc
    ∑ z ∈ Finset.univ.filter (fun z : (α × β) × γ =>
        (z.1.1, z.2) = (a, c)),
        ((M.postprocess (fun abc => abc.1)).effect (a, b)) * M.effect z =
      ∑ z ∈ Finset.univ.filter (fun z : (α × β) × γ =>
        (z.1.1, z.2) = (a, c)), if z.1 = (a, b) then M.effect z else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      exact _root_.MIPStarRE.QPBT.DistanceCalculus.postprocess_effect_mul_effect M hM (fun abc => abc.1) (a, b) z
    _ = M.effect ((a, b), c) := by
      rw [Finset.sum_eq_single ((a, b), c)]
      · simp
      · intro z hz hne
        have hzfiber := (Finset.mem_filter.mp hz).2
        rw [if_neg]
        intro hzfirst
        apply hne
        exact Prod.ext hzfirst (congrArg (fun p : α × γ => p.2) hzfiber)
      · simp
