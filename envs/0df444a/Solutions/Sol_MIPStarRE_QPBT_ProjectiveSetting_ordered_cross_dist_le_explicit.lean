-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.ordered_cross_dist_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:45:51.96743+00:00
-- url     : https://prove2.me/submissions/d81dbdca-52f1-4cb7-ad76-178d53d2b94a

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.ordered_cross_dist_le_explicit.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Points_Commutation
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_comm
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_mul
import Theorems.Thm_MIPStarRE_QPBT_exp_point_self_cons_explicit
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_of_le_of_le

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
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

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

/-!
# The sandwich POVM of the expanded point measurements

The first step of the proof of `lem:qld-4-10` combines the two expanded point
measurements into the sandwich POVM
`R^{x,z}_{a,b} = M^{(Point,Z),z}_b M^{(Point,X),x}_a M^{(Point,Z),z}_b`.  The
source forms it from the binary refinements; here it is formed directly with
outcomes in `F_q × F_q`, which the Parseval transfer of
`MIPStarRE/QPBT/Combining/Points/Commutation.lean` makes possible.  This file
defines the POVM, proves that it is close to the ordered product
`M^Z_b M^X_a` by the approximate commutation, and records the consistency of
the ordered products across opposite register placements, which follows from
the self-consistency of each factor.

## Main results

* `ProjectiveSetting.sandwichPoint`: the sandwich POVM.
* `sandwichPoint_ordered_dist_le`: closeness of the sandwich to the ordered
  product on every placement, with the error of `lem:qld-comm-cons`.
* `ordered_cross_dist_le`: the ordered product on one placement is close to
  the reversed ordered product on the opposite placement.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:731-748`
(the sandwich and display `eq:qld-r-2`), blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:803-960` (`lem:qld-4-10`); the
route is explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
      (p₁ p₂ : _root_.MIPStarRE.QPBT.Placement), p₁.IsOpposite p₂ →
      _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
        (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) => S.place p₁
          ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p₁.side .X xz.1).effect ab.1))
        (fun xz ab => S.place p₂
          ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p₂.side .Z xz.2).effect ab.2))
        S.psiHat ≤ 688 * ε := by
  intro P ε S p₁ p₂ hopp
  have hX := _root_.MIPStarRE.QPBT.exp_point_self_cons_explicit P ε S p₁ p₂ hopp .X
  have hZ := _root_.MIPStarRE.QPBT.exp_point_self_cons_explicit P ε S p₁ p₂ hopp .Z
  -- the middle family is `M^Z_b` on the first placement times `M^X_a` on the
  -- second; each factor is transported by the self-consistency of that factor
  have h₁ : _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
      (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) => S.place p₁
        ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2 *
          (S.pointMeasExp p₁.side .X xz.1).effect ab.1))
      (fun xz ab => S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) *
        S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1))
      S.psiHat ≤ 172 * ε := by
    refine le_trans ?_ (le_of_eq_of_le (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_fst
      (β := Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
      (fun x => ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .X x).effect a) -
          S.place p₂ ((S.pointMeasExp p₂.side .X x).effect a)) S.psiHat‖ ^ 2)) hX)
    unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun xz => ?_
    have hpt : ∀ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
        S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2 *
            (S.pointMeasExp p₁.side .X xz.1).effect ab.1) -
          S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) *
            S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1) =
          S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) *
            (S.place p₁ ((S.pointMeasExp p₁.side .X xz.1).effect ab.1) -
              S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1)) := by
      intro ab
      rw [S.place_mul p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2)
        ((S.pointMeasExp p₁.side .X xz.1).effect ab.1), mul_sub]
    simp only [hpt, Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun a _ => ?_
    exact _root_.MIPStarRE.QPBT.DistanceCalculus.sum_norm_mul_apply_le
      (fun b => S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect b))
      (S.place p₁ ((S.pointMeasExp p₁.side .X xz.1).effect a) -
        S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect a)) S.psiHat
      (_root_.MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
        (S.placedMeasurement p₁ (S.pointMeasExp p₁.side .Z xz.2)))
  have h₂ : _root_.MIPStarRE.QPBT.opFamilyDistSq (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
      (fun xz (ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) =>
        S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) *
          S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1))
      (fun xz ab => S.place p₂
        ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 *
          (S.pointMeasExp p₂.side .Z xz.2).effect ab.2))
      S.psiHat ≤ 172 * ε := by
    refine le_trans ?_ (le_of_eq_of_le (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_snd
      (α := Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
      (fun z => ∑ b : _root_.MIPStarRE.QPBT.PauliScalar P, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (S.place p₁ ((S.pointMeasExp p₁.side .Z z).effect b) -
          S.place p₂ ((S.pointMeasExp p₂.side .Z z).effect b)) S.psiHat‖ ^ 2)) hZ)
    unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
    refine _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun xz => ?_
    have hpt : ∀ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
        S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) *
            S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1) -
          S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1 *
            (S.pointMeasExp p₂.side .Z xz.2).effect ab.2) =
          S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1) *
            (S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2) -
              S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect ab.2)) := by
      intro ab
      rw [S.place_mul p₂ ((S.pointMeasExp p₂.side .X xz.1).effect ab.1)
        ((S.pointMeasExp p₂.side .Z xz.2).effect ab.2),
        S.place_comm p₁ p₂ hopp ((S.pointMeasExp p₁.side .Z xz.2).effect ab.2)
          ((S.pointMeasExp p₂.side .X xz.1).effect ab.1), ← mul_sub]
    simp only [hpt, Fintype.sum_prod_type_right]
    refine Finset.sum_le_sum fun b _ => ?_
    exact _root_.MIPStarRE.QPBT.DistanceCalculus.sum_norm_mul_apply_le
      (fun a => S.place p₂ ((S.pointMeasExp p₂.side .X xz.1).effect a))
      (S.place p₁ ((S.pointMeasExp p₁.side .Z xz.2).effect b) -
        S.place p₂ ((S.pointMeasExp p₂.side .Z xz.2).effect b)) S.psiHat
      (_root_.MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
        (S.placedMeasurement p₂ (S.pointMeasExp p₂.side .X xz.1)))
  have htri := _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PointPair P))
    _ _ _ S.psiHat (172 * ε) (172 * ε) h₁ h₂
  linarith
