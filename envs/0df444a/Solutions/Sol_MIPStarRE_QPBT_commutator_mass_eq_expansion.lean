-- Prove2me | solution 1 for MIPStarRE.QPBT.commutator_mass_eq_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:42:40.170706+00:00
-- url     : https://prove2.me/submissions/d01ca5f8-80da-49ca-a26c-59bf9752d9f5

-- Generated proof for MIPStarRE.QPBT.commutator_mass_eq_expansion.
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



























/-- The state quadratic form is additive over finite sums of operators. This is
the formalization-only identity `lem:distance-qform-finset-sum`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M b) := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]































































end MIPStarRE.QPBT.DistanceCalculus

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
    (P : _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι) (G : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ι)
    (ψ : EuclideanSpace ℂ (ι × ι))
    (hG : _root_.MIPStarRE.QPBT.Measurement.IsProjective G) :
    (∑ a : R₁, ∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1
        (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2) =
      (∑ a : R₁, ∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2) +
        (∑ a : R₁, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * P.effect a))) -
        2 * ∑ a : R₁, ∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1
          (G.effect g * P.effect a * G.effect g * P.effect a)) := by
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
  have hkr : ∀ B C : _root_.LIDT.MIPStarRE.Quantum.Op ι,
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (B - C) = _root_.MIPStarRE.QPBT.heteroKron 1 B - _root_.MIPStarRE.QPBT.heteroKron 1 C := by
    intro B C
    ext p q
    simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, mul_sub]
  have hnorm : ∀ M : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι),
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState M ψ‖ ^ 2 = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (Mᴴ * M) := by
    intro M
    rw [hqf Mᴴ M, Matrix.conjTranspose_conjTranspose]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (_root_.MIPStarRE.QPBT.applyOperatorToState M ψ)).symm
  have hsub : ∀ M N : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι),
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M - N) ψ‖ ^ 2 =
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState M ψ‖ ^ 2 + ‖_root_.MIPStarRE.QPBT.applyOperatorToState N ψ‖ ^ 2 -
          2 * _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (Mᴴ * N) := by
    intro M N
    have hlin : _root_.MIPStarRE.QPBT.applyOperatorToState (M - N) ψ =
        _root_.MIPStarRE.QPBT.applyOperatorToState M ψ - _root_.MIPStarRE.QPBT.applyOperatorToState N ψ := by
      simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
    rw [hlin, norm_sub_sq (𝕜 := ℂ), hqf Mᴴ N, Matrix.conjTranspose_conjTranspose]
    simp only [RCLike.re_to_complex]
    ring
  -- the pointwise expansion at a pair of an answer and a codeword
  have hpt : ∀ (a : R₁) (g : Γ₂),
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2 =
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2 +
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g * P.effect a)) -
          2 * _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1
            (G.effect g * P.effect a * G.effect g * P.effect a)) := by
    intro a g
    have hH : (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (P.effect a * G.effect g))ᴴ =
        _root_.MIPStarRE.QPBT.heteroKron 1 (G.effect g * P.effect a) := by
      rw [hct]
      simp [Matrix.conjTranspose_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
    have hH2 : (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (G.effect g * P.effect a))ᴴ =
        _root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g) := by
      rw [hct]
      simp [Matrix.conjTranspose_mul, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
    have hNN : (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (G.effect g * P.effect a))ᴴ *
        _root_.MIPStarRE.QPBT.heteroKron 1 (G.effect g * P.effect a) =
        _root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g * P.effect a) := by
      rw [hH2, _root_.MIPStarRE.QPBT.heteroKron_mul, one_mul]
      congr 1
      rw [mul_assoc, ← mul_assoc (G.effect g), (hG g).isIdempotentElem.eq]
      exact (mul_assoc _ _ _).symm
    have hXN : (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (P.effect a * G.effect g))ᴴ *
        _root_.MIPStarRE.QPBT.heteroKron 1 (G.effect g * P.effect a) =
        _root_.MIPStarRE.QPBT.heteroKron 1 (G.effect g * P.effect a * G.effect g * P.effect a) := by
      rw [hH, _root_.MIPStarRE.QPBT.heteroKron_mul, one_mul]
      congr 1
      simp [mul_assoc]
    rw [hkr, hsub, hnorm (_root_.MIPStarRE.QPBT.heteroKron 1 (G.effect g * P.effect a)),
      hNN, hXN]
  -- the row sum at a fixed answer
  have hrow : ∀ a : R₁,
      (∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2) =
        (∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2) +
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * P.effect a)) -
          2 * ∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1
            (G.effect g * P.effect a * G.effect g * P.effect a)) := by
    intro a
    have h2 : (∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1
        (P.effect a * G.effect g * P.effect a))) =
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * P.effect a)) := by
      rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, ← _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right]
      congr 2
      rw [← Finset.sum_mul, ← Finset.mul_sum, G.sum_eq_one, mul_one]
    calc (∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1
            (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2)
        = ∑ g : Γ₂, (‖_root_.MIPStarRE.QPBT.applyOperatorToState
              (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2 +
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g * P.effect a)) -
            2 * _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1
              (G.effect g * P.effect a * G.effect g * P.effect a))) :=
          Finset.sum_congr rfl fun g _ => hpt a g
      _ = (∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
              (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2) +
            (∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
              (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g * P.effect a))) -
            2 * ∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1
              (G.effect g * P.effect a * G.effect g * P.effect a)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [h2]
  calc (∑ a : R₁, ∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1
          (P.effect a * G.effect g - G.effect g * P.effect a)) ψ‖ ^ 2)
      = ∑ a : R₁, ((∑ g : Γ₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * G.effect g)) ψ‖ ^ 2) +
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1 (P.effect a * P.effect a)) -
          2 * ∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1
            (G.effect g * P.effect a * G.effect g * P.effect a))) :=
        Finset.sum_congr rfl fun a _ => hrow a
    _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
