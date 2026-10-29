-- Prove2me | solution 1 for MIPStarRE.QPBT.avgOver_pinched_collision_le_distinct_families
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:45:51.352159+00:00
-- url     : https://prove2.me/submissions/03431f4f-93fe-4e8a-982d-7b17dd3710da

-- Generated proof for MIPStarRE.QPBT.avgOver_pinched_collision_le_distinct_families.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_avgOver_collision_le

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

/-- A positive semidefinite operator has nonnegative state quadratic form. This
is the formalization-only order fact `lem:distance-qform-nonnegative`, used for
the nonnegative overlap terms in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) {M : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hM : 0 ≤ M) :
    0 ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  calc
    0 = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ 0 := by simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]
    _ ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hM ψ











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

/-! # Consistency and commutation of the pasting codeword families

This module records the cross consistency of the coarse second codeword family,
the commutator estimate for the two coarse families, the collision average of
the distinct second codewords, and the comparison of the fine second codeword
family with its coarse-graining.  These are the codeword-family steps of the
proof of `lem:pasting` recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `blueprint/src/chapter/ch12_qpbt_games.tex:960-1050`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

theorem solution
    {X Y₁ Y₂ R₁ R₂ Γ₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype Γ₂] [DecidableEq Γ₂]
    [Fintype ι] [DecidableEq ι]
    (D : _root_.LIDT.MIPStarRE.LDT.Distribution ((X × Y₁) × Y₂)) (eval₂ : Γ₂ → Y₂ → R₂)
    (G₂ opposite : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ι) (P : (X × Y₁) → _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (η : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1) (hη : 0 ≤ η)
    (hcoll : ∀ x y₁, 0 < (D.map Prod.fst).weight (x, y₁) →
      ∀ g g' : Γ₂, g ≠ g' →
        (∑ y₂ : Y₂, D.weight ((x, y₁), y₂) *
          if eval₂ g y₂ = eval₂ g' y₂ then 1 else 0) ≤
          η * (D.map Prod.fst).weight (x, y₁)) :
    _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => ∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else
      if eval₂ g q.2 = eval₂ g' q.2 then
        ∑ a : R₁, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((opposite q.1.1).effect g')
          ((P q.1).effect a * (G₂ q.1.1).effect g * (P q.1).effect a))
      else 0) ≤ η := by
  classical
  have hconj : ∀ (p : X × Y₁) (a : R₁) (g : Γ₂),
      0 ≤ (P p).effect a * (G₂ p.1).effect g * (P p).effect a := by
    intro p a g
    apply Matrix.nonneg_iff_posSemidef.mpr
    have hpos : (((P p).effect a)ᴴ * (G₂ p.1).effect g *
        (P p).effect a).PosSemidef :=
      (Matrix.nonneg_iff_posSemidef.mp ((G₂ p.1).pos g)).conjTranspose_mul_mul_same
        ((P p).effect a)
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian (P p) a] at hpos
    exact hpos
  have hcnn : ∀ (p : X × Y₁) (g g' : Γ₂),
      0 ≤ ∑ a : R₁, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((opposite p.1).effect g')
        ((P p).effect a * (G₂ p.1).effect g * (P p).effect a)) := by
    intro p g g'
    exact Finset.sum_nonneg fun a _ =>
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_nonneg ψ (_root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg ((opposite p.1).pos g') (hconj p a g))
  -- The unit quadratic form of the identity is inlined here; see issue
  -- Dengnifer/MIPStarRE-QPBT-bak#204.
  have hone : _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) = ‖ψ‖ ^ 2 := by
    have hid : _root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) ψ = ψ := by
      simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, hid]
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) ψ)
  have htotal : ∀ p : X × Y₁,
      (∑ g : Γ₂, ∑ g' : Γ₂, ∑ a : R₁, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        (_root_.MIPStarRE.QPBT.heteroKron ((opposite p.1).effect g')
          ((P p).effect a * (G₂ p.1).effect g * (P p).effect a))) ≤ 1 := by
    intro p
    have hin : ∀ g : Γ₂,
        (∑ g' : Γ₂, ∑ a : R₁, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((opposite p.1).effect g')
          ((P p).effect a * (G₂ p.1).effect g * (P p).effect a))) =
        ∑ a : R₁, ∑ g' : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((opposite p.1).effect g')
          ((P p).effect a * (G₂ p.1).effect g * (P p).effect a)) :=
      fun g => Finset.sum_comm
    rw [Finset.sum_congr rfl (fun g (_ : g ∈ Finset.univ) => hin g), Finset.sum_comm]
    have hfill : ∀ (a : R₁) (g : Γ₂),
        (∑ g' : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((opposite p.1).effect g')
          ((P p).effect a * (G₂ p.1).effect g * (P p).effect a))) =
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1
          ((P p).effect a * (G₂ p.1).effect g * (P p).effect a)) := by
      intro a g
      rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, ← _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left,
        (opposite p.1).sum_eq_one]
    simp_rw [hfill]
    have hmid : ∀ a : R₁,
        (∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1
          ((P p).effect a * (G₂ p.1).effect g * (P p).effect a))) =
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron 1 ((P p).effect a * (P p).effect a)) := by
      intro a
      rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, ← _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right]
      congr 2
      rw [← Finset.sum_mul, ← Finset.mul_sum, (G₂ p.1).sum_eq_one, mul_one]
    simp_rw [hmid]
    rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum, ← _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right]
    have hS : (∑ a : R₁, (P p).effect a * (P p).effect a) ≤ 1 := by
      refine le_of_eq_of_le ?_ (_root_.MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one (P p))
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian (P p) a]
    have hmono : _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)
        (∑ a : R₁, (P p).effect a * (P p).effect a) ≤ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) := by
      have hsub : (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) -
          _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (∑ a : R₁, (P p).effect a * (P p).effect a) =
          _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)
            (1 - ∑ a : R₁, (P p).effect a * (P p).effect a) := by
        have hbil : _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)
            (1 - ∑ a : R₁, (P p).effect a * (P p).effect a) =
            _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) 1 -
              _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)
                (∑ a : R₁, (P p).effect a * (P p).effect a) := by
          ext u v
          simp only [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply,
            Matrix.sub_apply, Matrix.one_apply, mul_sub]
        rw [hbil, _root_.MIPStarRE.QPBT.heteroKron_one_one]
      have hnn : 0 ≤ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) -
          _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)
            (∑ a : R₁, (P p).effect a * (P p).effect a) := by
        rw [hsub]
        exact _root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg (Matrix.PosSemidef.one.nonneg) (sub_nonneg.mpr hS)
      exact sub_nonneg.mp hnn
    calc _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι)
        (∑ a : R₁, (P p).effect a * (P p).effect a))
        ≤ _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hmono ψ
      _ = ‖ψ‖ ^ 2 := hone
      _ = 1 := by rw [hψ]; norm_num
  have hmass : ∀ p : X × Y₁,
      (∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else
        ∑ a : R₁, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((opposite p.1).effect g')
          ((P p).effect a * (G₂ p.1).effect g * (P p).effect a))) ≤ 1 := by
    intro p
    refine le_trans ?_ (htotal p)
    refine Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun g' _ => ?_
    by_cases hgg : g = g'
    · simp only [if_pos hgg]
      exact hcnn p g g'
    · simp only [if_neg hgg]
      exact le_rfl
  exact _root_.MIPStarRE.QPBT.avgOver_collision_le D eval₂
    (fun p g g' => ∑ a : R₁, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((opposite p.1).effect g')
      ((P p).effect a * (G₂ p.1).effect g * (P p).effect a))) η hD hη
    hcnn hmass hcoll
