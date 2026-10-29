-- Prove2me | solution 1 for MIPStarRE.QPBT.DistanceCalculus.measurement_fiber_sum_adjoint_mul_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:06:37.432062+00:00
-- url     : https://prove2.me/submissions/decba95c-dc56-415f-b588-6dfe8cbe7c4b

-- Generated proof for MIPStarRE.QPBT.DistanceCalculus.measurement_fiber_sum_adjoint_mul_le_one.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support

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
4.14): every effect of a complete measurement is bounded by the identity. -/
theorem measurement_effect_le_one {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (a : α) :
    M.effect a ≤ 1 := by
  calc
    M.effect a ≤ ∑ b : α, M.effect b :=
      Finset.single_le_sum (fun b _ => M.pos b) (Finset.mem_univ a)
    _ = 1 := M.sum_eq_one

















































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

theorem solution {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement (α × β) ι) (a : α) :
    ∑ b : β, (M.effect (a, b))ᴴ * M.effect (a, b) ≤ 1 := by
  classical
  have hsquare_le (z : α × β) :
      (M.effect z)ᴴ * M.effect z ≤ M.effect z := by
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian M z]
    exact _root_.LIDT.MIPStarRE.Quantum.sq_le_self (M.pos z) (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one M z)
  calc
    ∑ b : β, (M.effect (a, b))ᴴ * M.effect (a, b) ≤
        ∑ b : β, M.effect (a, b) :=
      Finset.sum_le_sum fun b _ => hsquare_le (a, b)
    _ ≤ ∑ a' : α, ∑ b : β, M.effect (a', b) :=
      Finset.single_le_sum
        (fun a' _ => Finset.sum_nonneg fun b _ => M.pos (a', b))
        (Finset.mem_univ a)
    _ = ∑ z : α × β, M.effect z := (Fintype.sum_prod_type _).symm
    _ = 1 := M.sum_eq_one
