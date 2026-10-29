-- Prove2me | solution 1 for MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_placed_le_four
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:59:25.597907+00:00
-- url     : https://prove2.me/submissions/9d7c1477-53a2-4970-b213-eebe40defd55

-- Generated proof for MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_placed_le_four.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_sum_norm_sub_apply_sq_le_four

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
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

/- Source helpers from QPBT/Games/DistanceTheorems.lean. -/
/-! # State-dependent distance calculus

This module records the consistency and state-dependent distance estimates used
throughout the quantum Pauli basis test. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

The operator-level inequalities they rest on live in
`MIPStarRE.QPBT.Games.DistanceTheorems.Calculus`.

## References

The source results run from blueprint `fact:agreement` through
`lem:close-strategies-have-close-values`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-461` and
`:531-540`. The observable conversion lemmas come from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:95-131`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus











/-- The squared effects of a POVM sum to at most the identity. This is the
formalization-only estimate `lem:sandwich-povm-square-sum` used in the
contractions underlying `lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem measurement_sum_adjoint_mul_le_one
    {α I : Type*} [Fintype α] [Fintype I] [DecidableEq I]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α I) :
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ 1 := by
  calc
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ ∑ a : α, M.effect a := by
      apply Finset.sum_le_sum
      intro a _
      rw [_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
      exact _root_.LIDT.MIPStarRE.Quantum.sq_le_self (M.pos a) (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one M a)
    _ = 1 := M.sum_eq_one























end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/LineMeasurement/SquareRootError.lean. -/
/-!
# Square-root error bounds for placed measurement families

The consistency conclusions of `lem:qld-comm-line-cons` are stated with the
common error `deltaLine ε = √ε`, while the individual estimates of the proof
are linear in `ε` or already of square-root form. This module records the two
elementary facts that convert those estimates into the common form: the
state-dependent distance between two placed complete measurements never
exceeds `4`, and a quantity bounded by both `a * ε` and `4` is bounded by
`(a + 4) * √ε`.

## References

`lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-545`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

namespace DistanceCalculus



/-- The adjoint squares of a left-placed complete measurement sum to at most
the identity on the product space. -/
theorem leftPlaced_sum_adjoint_mul_le_one {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) :
    ∑ a : α, (_root_.MIPStarRE.QPBT.heteroKron (M.effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB))ᴴ *
      _root_.MIPStarRE.QPBT.heteroKron (M.effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) ≤ 1 :=
  _root_.MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
    (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := ιB) M)

/-- The adjoint squares of a right-placed complete measurement sum to at most
the identity on the product space. -/
theorem rightPlaced_sum_adjoint_mul_le_one {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB) :
    ∑ a : α, (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (M.effect a))ᴴ *
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (M.effect a) ≤ 1 :=
  _root_.MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
    (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := ιA) M)



end DistanceCalculus



end MIPStarRE.QPBT

/-!
# Square-root error bounds for placed measurement families

The consistency conclusions of `lem:qld-comm-line-cons` are stated with the
common error `deltaLine ε = √ε`, while the individual estimates of the proof
are linear in `ε` or already of square-root form. This module records the two
elementary facts that convert those estimates into the common form: the
state-dependent distance between two placed complete measurements never
exceeds `4`, and a quantity bounded by both `a * ε` and `4` is bounded by
`(a + 4) * √ε`.

## References

`lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-545`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

open MIPStarRE.QPBT.DistanceCalculus

theorem solution {X α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (hμ : μ.IsProbability)
    (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA)
    (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1)
      (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ ≤ 4 := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ∑ a : α,
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.heteroKron ((A x).effect a) 1 - _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).effect a)) ψ‖ ^ 2)
        ≤ _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun _ => (4 : ℝ)) := by
      apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
      intro x
      exact _root_.MIPStarRE.QPBT.DistanceCalculus.sum_norm_sub_apply_sq_le_four _ _ ψ hψ
        (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlaced_sum_adjoint_mul_le_one (A x))
        (_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlaced_sum_adjoint_mul_le_one (B x))
    _ = 4 := _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability μ hμ 4
