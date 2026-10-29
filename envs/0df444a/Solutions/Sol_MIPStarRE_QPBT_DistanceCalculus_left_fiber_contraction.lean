-- Prove2me | solution 1 for MIPStarRE.QPBT.DistanceCalculus.left_fiber_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:10:09.444215+00:00
-- url     : https://prove2.me/submissions/0f3cb271-620f-4cf2-9bf8-44c93f1e5897

-- Generated proof for MIPStarRE.QPBT.DistanceCalculus.left_fiber_contraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
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
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_measurement_fiber_sum_adjoint_mul_le_one

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

theorem solution {α β ιA ιB : Type*}
    [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement (α × β) ιA) (a : α) :
    (1 - ∑ b : β, (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) (M.effect (a, b)))ᴴ *
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) (M.effect (a, b))).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [sub_nonneg]
  calc
    ∑ b : β, (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) (M.effect (a, b)))ᴴ *
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) (M.effect (a, b)) =
        ∑ b : β, _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB)
          ((M.effect (a, b))ᴴ * M.effect (a, b)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_conjTranspose, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor]
    _ = _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB)
        (∑ b : β, (M.effect (a, b))ᴴ * M.effect (a, b)) :=
      _root_.LIDT.MIPStarRE.LDT.leftTensor_finset_sum Finset.univ _
    _ ≤ _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) :=
      _root_.LIDT.MIPStarRE.LDT.leftTensor_mono (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_fiber_sum_adjoint_mul_le_one M a)
    _ = 1 := _root_.LIDT.MIPStarRE.LDT.leftTensor_one
