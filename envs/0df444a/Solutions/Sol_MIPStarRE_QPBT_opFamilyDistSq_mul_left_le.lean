-- Prove2me | solution 1 for MIPStarRE.QPBT.opFamilyDistSq_mul_left_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:48:41.732992+00:00
-- url     : https://prove2.me/submissions/c31a84ba-6906-4937-9d80-53eb816daa25

-- Generated proof for MIPStarRE.QPBT.opFamilyDistSq_mul_left_le.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono

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

/-- The squared norm of `M ψ` is the quadratic form of `Mᴴ M`. -/
private theorem norm_applyOperatorToState_sq_eq {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState M ψ‖ ^ 2 =
      (inner ℂ ψ (_root_.MIPStarRE.QPBT.applyOperatorToState (Mᴴ * M) ψ)).re := by
  rw [@norm_sq_eq_re_inner ℂ]
  unfold _root_.MIPStarRE.QPBT.applyOperatorToState
  rw [_root_.LIDT.Matrix.toEuclideanLin_conjTranspose_mul_self]
  change (inner ℂ (Matrix.toEuclideanLin M ψ) (Matrix.toEuclideanLin M ψ)).re =
    (inner ℂ ψ ((Matrix.toEuclideanLin M).adjoint (Matrix.toEuclideanLin M ψ))).re
  rw [LinearMap.adjoint_inner_right]





/-- Finite-subset form of contraction by square-summable left multipliers. -/
private theorem finset_sum_norm_mul_apply_le {γ ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (s : Finset γ) (C : γ → _root_.LIDT.MIPStarRE.Quantum.Op ι) (D : _root_.LIDT.MIPStarRE.Quantum.Op ι) (v : EuclideanSpace ℂ ι)
    (hC : ∑ c ∈ s, (C c)ᴴ * C c ≤ 1) :
    ∑ c ∈ s, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (C c * D) v‖ ^ 2 ≤
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState D v‖ ^ 2 := by
  calc
    ∑ c ∈ s, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (C c * D) v‖ ^ 2 =
        ∑ c ∈ s,
          (inner ℂ (_root_.MIPStarRE.QPBT.applyOperatorToState D v)
            (_root_.MIPStarRE.QPBT.applyOperatorToState ((C c)ᴴ * C c)
              (_root_.MIPStarRE.QPBT.applyOperatorToState D v))).re := by
          apply Finset.sum_congr rfl
          intro c _
          rw [_root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul]
          exact norm_applyOperatorToState_sq_eq (C c) _
    _ = (inner ℂ (_root_.MIPStarRE.QPBT.applyOperatorToState D v)
          (_root_.MIPStarRE.QPBT.applyOperatorToState (∑ c ∈ s, (C c)ᴴ * C c)
            (_root_.MIPStarRE.QPBT.applyOperatorToState D v))).re := by
          simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
    _ ≤ (inner ℂ (_root_.MIPStarRE.QPBT.applyOperatorToState D v)
          (_root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (_root_.MIPStarRE.QPBT.applyOperatorToState D v))).re :=
      _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hC _
    _ = ‖_root_.MIPStarRE.QPBT.applyOperatorToState D v‖ ^ 2 := by
      simpa [_root_.MIPStarRE.QPBT.applyOperatorToState] using
        (norm_applyOperatorToState_sq_eq (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (_root_.MIPStarRE.QPBT.applyOperatorToState D v)).symm

/-- Formalization-only auxiliary lemma for Fact 4.20: a square-summable family
of left multipliers contracts total squared norm. -/
theorem sum_norm_mul_apply_le {γ ι : Type*}
    [Fintype γ] [Fintype ι] [DecidableEq ι]
    (C : γ → _root_.LIDT.MIPStarRE.Quantum.Op ι) (D : _root_.LIDT.MIPStarRE.Quantum.Op ι) (v : EuclideanSpace ℂ ι)
    (hC : ∑ c : γ, (C c)ᴴ * C c ≤ 1) :
    ∑ c : γ, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (C c * D) v‖ ^ 2 ≤
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState D v‖ ^ 2 := by
  simpa using finset_sum_norm_mul_apply_le Finset.univ C D v (by simpa using hC)

















































































end MIPStarRE.QPBT.DistanceCalculus

/-!
# Consistency and state-dependent distance inequalities

This module collects the operator-level part of the state-dependent distance
calculus: the two-sided comparison between consistency defect and distance, the
monotonicity of the distance under products and function-indexed operators, its
triangle inequality and data-processing bound, and the approximate commutation
obtained from a joint projective refinement. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

## References

The source results run from blueprint `fact:agreement` through
`lem:commutation-analysis`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-461`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution {X Y α β γ ι : Type*}
    [DecidableEq X] [Fintype α] [Fintype β] [Fintype γ]
    [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution (X × Y)) (A B : X → (α × β) → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (C : Y → α → γ → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) (δ : ℝ)
    (hC : ∀ y a, (1 - ∑ c : γ, (C y a c)ᴴ * C y a c).PosSemidef)
    (h : _root_.MIPStarRE.QPBT.opFamilyDistSq (μ.map Prod.fst) A B ψ ≤ δ) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ
      (fun p (abc : (α × β) × γ) =>
        C p.2 abc.1.1 abc.2 * A p.1 (abc.1.1, abc.1.2))
      (fun p (abc : (α × β) × γ) =>
        C p.2 abc.1.1 abc.2 * B p.1 (abc.1.1, abc.1.2)) ψ ≤ δ := by
  have hC' (y : Y) (a : α) :
      ∑ c : γ, (C y a c)ᴴ * C y a c ≤ 1 :=
    Matrix.le_iff.mpr (hC y a)
  calc
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ
        (fun p (abc : (α × β) × γ) =>
          C p.2 abc.1.1 abc.2 * A p.1 (abc.1.1, abc.1.2))
        (fun p (abc : (α × β) × γ) =>
          C p.2 abc.1.1 abc.2 * B p.1 (abc.1.1, abc.1.2)) ψ
        ≤ _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun p ab => A p.1 ab) (fun p ab => B p.1 ab) ψ := by
          unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
          intro p
          rw [Fintype.sum_prod_type]
          apply Finset.sum_le_sum
          intro ab _
          simpa only [mul_sub] using
            _root_.MIPStarRE.QPBT.DistanceCalculus.sum_norm_mul_apply_le (fun c => C p.2 ab.1 c)
              (A p.1 ab - B p.1 ab) ψ (hC' p.2 ab.1)
    _ = _root_.MIPStarRE.QPBT.opFamilyDistSq (μ.map Prod.fst) A B ψ := by
      unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
      exact (_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map μ Prod.fst
        (fun x => ∑ a : α × β,
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ ^ 2)).symm
    _ ≤ δ := h
