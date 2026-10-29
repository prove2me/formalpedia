-- Prove2me | solution 1 for MIPStarRE.QPBT.abs_cross_move_gap_le_sqrt_distinct_families
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:42:40.063186+00:00
-- url     : https://prove2.me/submissions/339cbc52-9493-4489-9635-b6a354f76cde

-- Generated proof for MIPStarRE.QPBT.abs_cross_move_gap_le_sqrt_distinct_families.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
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

















/-- The state quadratic form is additive over finite sums of operators. This is
the formalization-only identity `lem:distance-qform-finset-sum`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M b) := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]













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

/-! # Moving a second codeword effect across the tensor factors

This module records the estimate of step 5 of the proof of the adopted
statement of `lem:pasting`: in the cross term of the commutator mass of a first
codeword family against a second codeword family, the rightmost second codeword
effect is moved to the opposite tensor factor at the cost of the square root of
the summed cross distance of that family.

## References

`lem:pasting` in `blueprint/src/chapter/ch12_qpbt_games.tex:960-990`, with the
proof of the adopted statement in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

theorem solution {R₁ Γ₂ ι : Type*}
    [Fintype R₁] [DecidableEq R₁] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ι] [DecidableEq ι]
    (P : _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι) (G opposite : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (hψ : ‖ψ‖ = 1) :
    |(∑ a : R₁, ∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1
          (G.effect g * P.effect a * G.effect g * P.effect a))) -
        ∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (opposite.effect g)
          (∑ a : R₁, P.effect a * G.effect g * P.effect a))| ≤
      Real.sqrt (∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron 1 (G.effect g) - _root_.MIPStarRE.QPBT.heteroKron (opposite.effect g) 1) ψ‖ ^ 2) := by
  classical
  -- the inlined identities of the distance calculus; see issue Dengnifer/MIPStarRE-QPBT-bak#204
  have hqf : ∀ M N : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι), _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M * N) =
      (inner ℂ (_root_.MIPStarRE.QPBT.applyOperatorToState Mᴴ ψ) (_root_.MIPStarRE.QPBT.applyOperatorToState N ψ)).re := by
    intro M N
    have happ : _root_.MIPStarRE.QPBT.applyOperatorToState (M * N) ψ =
        _root_.MIPStarRE.QPBT.applyOperatorToState M (_root_.MIPStarRE.QPBT.applyOperatorToState N ψ) := by
      unfold _root_.MIPStarRE.QPBT.applyOperatorToState
      simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
    have hadj : (Matrix.toEuclideanLin M).adjoint = Matrix.toEuclideanLin Mᴴ := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    have h1 : (inner ℂ ((Matrix.toEuclideanLin M).adjoint ψ)
        (_root_.MIPStarRE.QPBT.applyOperatorToState N ψ) : ℂ) =
        inner ℂ ψ (Matrix.toEuclideanLin M (_root_.MIPStarRE.QPBT.applyOperatorToState N ψ)) :=
      LinearMap.adjoint_inner_left _ _ _
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, happ]
    rw [show _root_.MIPStarRE.QPBT.applyOperatorToState Mᴴ ψ = (Matrix.toEuclideanLin M).adjoint ψ by
      rw [hadj]; rfl]
    rw [h1]
    rfl
  have hct : ∀ M N : _root_.LIDT.MIPStarRE.Quantum.Op ι, (_root_.MIPStarRE.QPBT.heteroKron M N)ᴴ = _root_.MIPStarRE.QPBT.heteroKron Mᴴ Nᴴ := by
    intro M N
    unfold _root_.MIPStarRE.QPBT.heteroKron
    exact Matrix.conjTranspose_kronecker M N
  set u : R₁ × Γ₂ → EuclideanSpace ℂ (ι × ι) := fun p =>
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect p.1) *
      (_root_.MIPStarRE.QPBT.heteroKron 1 (G.effect p.2) - _root_.MIPStarRE.QPBT.heteroKron (opposite.effect p.2) 1)) ψ with hu
  set v : R₁ × Γ₂ → EuclideanSpace ℂ (ι × ι) := fun p =>
    _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 (G.effect p.2 * P.effect p.1)) ψ with hv
  -- the pointwise gap is the overlap of the moved vector with the cross vector
  have hpt : ∀ (a : R₁) (g : Γ₂),
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1
          (G.effect g * P.effect a * G.effect g * P.effect a)) -
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (opposite.effect g)
          (P.effect a * G.effect g * P.effect a)) =
        (inner ℂ (u (a, g)) (v (a, g))).re := by
    intro a g
    have e1 : _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)
        (G.effect g * P.effect a * G.effect g * P.effect a) =
        _root_.MIPStarRE.QPBT.heteroKron 1 (G.effect g * P.effect a) *
          _root_.MIPStarRE.QPBT.heteroKron 1 (G.effect g * P.effect a) := by
      rw [_root_.MIPStarRE.QPBT.heteroKron_mul]
      congr 1
      · rw [one_mul]
      · simp [mul_assoc]
    have e2 : _root_.MIPStarRE.QPBT.heteroKron (opposite.effect g) (P.effect a * G.effect g * P.effect a) =
        _root_.MIPStarRE.QPBT.heteroKron (opposite.effect g) (P.effect a) *
          _root_.MIPStarRE.QPBT.heteroKron 1 (G.effect g * P.effect a) := by
      rw [_root_.MIPStarRE.QPBT.heteroKron_mul]
      congr 1
      · rw [mul_one]
      · simp [mul_assoc]
    have h1 : (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (G.effect g * P.effect a))ᴴ =
        _root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g) := by
      rw [hct]
      simp [Matrix.conjTranspose_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
    have h2 : (_root_.MIPStarRE.QPBT.heteroKron (opposite.effect g) (P.effect a))ᴴ =
        _root_.MIPStarRE.QPBT.heteroKron (opposite.effect g) (P.effect a) := by
      rw [hct, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
    have hudiff : _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g)) ψ -
        _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (opposite.effect g) (P.effect a)) ψ = u (a, g) := by
      simp only [hu]
      rw [show _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (P.effect a) *
          (_root_.MIPStarRE.QPBT.heteroKron 1 (G.effect g) - _root_.MIPStarRE.QPBT.heteroKron (opposite.effect g) 1) =
          _root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g) -
            _root_.MIPStarRE.QPBT.heteroKron (opposite.effect g) (P.effect a) by
        simp [mul_sub, _root_.MIPStarRE.QPBT.heteroKron_mul]]
      simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
    rw [e1, e2, hqf, hqf, h1, h2, ← Complex.sub_re, ← inner_sub_left, hudiff]
  -- the two mass estimates
  have hCP : ∑ a : R₁, (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (P.effect a))ᴴ *
      _root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a) ≤ 1 := by
    simpa using _root_.MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
      (_root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ι) P)
  have hCG : ∑ g : Γ₂, (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (G.effect g))ᴴ *
      _root_.MIPStarRE.QPBT.heteroKron 1 (G.effect g) ≤ 1 := by
    simpa using _root_.MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
      (_root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ι) G)
  have hmassU : (∑ p : R₁ × Γ₂, ‖u p‖ ^ 2) ≤
      ∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron 1 (G.effect g) - _root_.MIPStarRE.QPBT.heteroKron (opposite.effect g) 1) ψ‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_le_sum fun g _ => ?_
    simpa [hu] using _root_.MIPStarRE.QPBT.DistanceCalculus.sum_norm_mul_apply_le
      (fun a : R₁ => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (P.effect a))
      (_root_.MIPStarRE.QPBT.heteroKron 1 (G.effect g) - _root_.MIPStarRE.QPBT.heteroKron (opposite.effect g) 1) ψ hCP
  have hmassV : (∑ p : R₁ × Γ₂, ‖v p‖ ^ 2) ≤ 1 := by
    have hone : _root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) ψ = ψ := by
      simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
    rw [Fintype.sum_prod_type]
    calc (∑ a : R₁, ∑ g : Γ₂, ‖v (a, g)‖ ^ 2)
        ≤ ∑ a : R₁, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a)) ψ‖ ^ 2 := by
          refine Finset.sum_le_sum fun a _ => ?_
          simpa [hv, _root_.MIPStarRE.QPBT.heteroKron_mul] using _root_.MIPStarRE.QPBT.DistanceCalculus.sum_norm_mul_apply_le
            (fun g : Γ₂ => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (G.effect g))
            (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a)) ψ hCG
      _ ≤ 1 := by
          have h := _root_.MIPStarRE.QPBT.DistanceCalculus.sum_norm_mul_apply_le
            (fun a : R₁ => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (P.effect a)) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) ψ hCP
          rw [hone, hψ, one_pow] at h
          simpa using h
  -- the expansion of the gap over the pairs
  have hexpand : (∑ a : R₁, ∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1
        (G.effect g * P.effect a * G.effect g * P.effect a))) -
      (∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (opposite.effect g)
        (∑ a : R₁, P.effect a * G.effect g * P.effect a))) =
      ∑ p : R₁ × Γ₂, (inner ℂ (u p) (v p)).re := by
    have hB : (∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (opposite.effect g)
        (∑ a : R₁, P.effect a * G.effect g * P.effect a))) =
        ∑ a : R₁, ∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (opposite.effect g)
          (P.effect a * G.effect g * P.effect a)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
    rw [hB, ← Finset.sum_sub_distrib, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun g _ => hpt a g
  rw [hexpand]
  calc |∑ p : R₁ × Γ₂, (inner ℂ (u p) (v p)).re|
      ≤ ∑ p : R₁ × Γ₂, |(inner ℂ (u p) (v p)).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : R₁ × Γ₂, ‖u p‖ * ‖v p‖ := Finset.sum_le_sum fun p _ =>
        le_trans (Complex.abs_re_le_norm _) (norm_inner_le_norm _ _)
    _ ≤ Real.sqrt (∑ p : R₁ × Γ₂, ‖u p‖ ^ 2) *
          Real.sqrt (∑ p : R₁ × Γ₂, ‖v p‖ ^ 2) := by
        simpa using Real.sum_mul_le_sqrt_mul_sqrt
          (Finset.univ : Finset (R₁ × Γ₂)) (fun p => ‖u p‖) (fun p => ‖v p‖)
    _ ≤ Real.sqrt (∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.heteroKron 1 (G.effect g) - _root_.MIPStarRE.QPBT.heteroKron (opposite.effect g) 1) ψ‖ ^ 2) * 1 := by
        refine mul_le_mul (Real.sqrt_le_sqrt hmassU) ?_ (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
        rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
        exact Real.sqrt_le_sqrt hmassV
    _ = Real.sqrt (∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.heteroKron 1 (G.effect g) - _root_.MIPStarRE.QPBT.heteroKron (opposite.effect g) 1) ψ‖ ^ 2) := by
        rw [mul_one]
