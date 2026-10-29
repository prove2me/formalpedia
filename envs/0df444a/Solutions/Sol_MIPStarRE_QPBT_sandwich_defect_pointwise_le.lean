-- Prove2me | solution 1 for MIPStarRE.QPBT.sandwich_defect_pointwise_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:10:09.700307+00:00
-- url     : https://prove2.me/submissions/915a564a-b7e4-4ae1-a20e-423262f8371c

-- Generated proof for MIPStarRE.QPBT.sandwich_defect_pointwise_le.
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
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Rigidity_GroundSlice
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_sandwich_overlap_identity

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
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
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

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean. -/
/-!
# Contractions, isometries and the ground slice of the dilation

Support for the transfer step of `thm:ms-rigidity` (blueprint
`thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`):
the calculus needed to compare the dilated projective strategy of
`Rigidity/Dilation.lean` with the original strategy on states.

* Contractions: operators `K` with `Kᴴ K ≤ 1` do not increase norms; effects,
  observables of binary measurements, orthogonal projections, tensor placements,
  products and isometry conjugates are contractions.
* Matrices of isometries: `Vᴴ V = 1`, the two-sided isometry image of a state
  preserves norms, and a conjugated local operator acts on the transported state
  as the original operator acts on the original state.
* The ground projection `Π` of an enlarged local space: an orthogonal projection
  fixing the dilated state, with `Π P Π` the inflation of the compression of `P`.
* Leakage: the part `(1 - Π) P ψ'` of a dilated operator that leaves the ground
  slice is bounded by the intertwining defect of `P ⊗ 1` against any `1 ⊗ Q`,
  because `(1 - Π) ⊗ 1` annihilates `(1 ⊗ Q) ψ'`.  This is the estimate that
  replaces the `≈_δ`-preservation which Naimark dilation lacks in general
  (`references/ldt-paper/orthonormalization.tex:82-101`, blueprint
  `ex:easy-but-long`).

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Contractions and their action on states -/



















/-- An operator `K` with `Kᴴ K ≤ 1` does not increase norms. -/
theorem norm_applyOperatorToState_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : _root_.LIDT.MIPStarRE.Quantum.Op ι} (hK : Kᴴ * K ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState K v‖ ≤ ‖v‖ := by
  have h := _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hK v
  have hv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [← _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_sq, _root_.MIPStarRE.QPBT.MagicSquareRigidity.applyOperatorToState_one, hv] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h















/-! ## Kronecker algebra of placed operators

The mixed-product rule `heteroKron_mul`, the identity `heteroKron_one_one` and
the additive and difference identities are the shared tensor-placement lemmas of
`MIPStarRE/QPBT/Games/Defs.lean`; the identities below extend them with the
finite-sum and scalar facts used by the transfer step. -/









/-! ## Matrices of isometries -/





















/-! ## The ground projection -/





















/-! ## Leakage out of the ground slice is bounded by the intertwining defect -/





end

end MIPStarRE.QPBT.MagicSquareRigidity

/- Source helpers from QPBT/Combining/Points/Consistency.lean. -/
/-!
# Self-consistency of the sandwich POVM

The sandwich POVM `R^{x,z}_{a,b} = M^Z_b M^X_a M^Z_b` of
`MIPStarRE/QPBT/Combining/Points/Sandwich.lean` is approximately self-consistent
between opposite register placements.  The source establishes this by a
Cauchy--Schwarz chain (displays `eq:qld-rw-self-cons-1` to
`eq:qld-rw-self-cons-4`); here an exact identity is used instead.  Writing
`P_1, P_2` for the two placements of an operator `P`,
`W_b = (M^Z_b)_1 (M^Z_b)_2`, and `D^W_c = (M^W_c)_1 - (M^W_c)_2`, the
consistency defect of the two placed sandwiches equals
`(1/2) ∑_b ‖D^Z_b ψ‖^2 + (1/2) ∑_{a,b} ‖D^X_a W_b ψ‖^2`,
by two applications of the identity
`∑_c ⟨w, P_c Q_c w⟩ = ‖w‖^2 - (1/2) ∑_c ‖(P_c - Q_c) w‖^2` for projective
measurements.  The second sum is then bounded by the self-consistency of `M^X`
and the commutators on the two placements, since
`D^X_a W_b = W_b D^X_a + (M^Z_b)_2 K^1_{a,b} - (M^Z_b)_1 K^2_{a,b}`, where
`K^i_{a,b}` is the placed commutator of `M^X_a` and `M^Z_b`.

## Main results

* `sandwich_overlap_identity`: the exact expression of the overlap of two
  placed sandwiches.
* `sandwich_defect_pointwise_le`: the pointwise bound on the consistency
  defect of the sandwich for a fixed point pair.
* `ProjectiveSetting.sandwichDefectBound`,
  `ProjectiveSetting.sandwich_offDiagonal_le_sandwichDefectBound`, and
  `ProjectiveSetting.avg_sandwichDefectBound_le`: the bound as a function of
  the point pair, the pointwise estimate, and the average.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:743-790`,
blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex:851-880`
(`lem:qld-4-10`, first step); the identity route is explained in
`docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## Quadratic-form identities -/





/-- An effect of a projective measurement is a contraction. -/
theorem norm_applyOperatorToState_proj_effect_le {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) (a : α)
    (v : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M.effect a) v‖ ≤ ‖v‖ := by
  refine _root_.MIPStarRE.QPBT.MagicSquareRigidity.norm_applyOperatorToState_le ?_ v
  rw [(hM a).isSelfAdjoint.isHermitian.eq, (hM a).isIdempotentElem.eq]
  exact _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one M a



/-! ## The overlap of two placed sandwiches -/

section Abstract

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]



omit [DecidableEq ι] in
/-- Formalization-only auxiliary for `lem:qld-4-10`: the decomposition of
`(X_1 - X_2) Z_1 Z_2` into `Z_1 Z_2 (X_1 - X_2)` and the two commutator
terms. -/
theorem sub_mul_mul_eq_add_commutators (X₁ X₂ Z₁ Z₂ : _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (hXZ : X₁ * Z₂ = Z₂ * X₁) (hZX : Z₁ * X₂ = X₂ * Z₁)
    (hZZ : Z₁ * Z₂ = Z₂ * Z₁) :
    (X₁ - X₂) * (Z₁ * Z₂) =
      Z₁ * Z₂ * (X₁ - X₂) + Z₂ * (X₁ * Z₁ - Z₁ * X₁) -
        Z₁ * (X₂ * Z₂ - Z₂ * X₂) := by
  simp only [sub_mul, mul_sub, Matrix.mul_assoc]
  rw [(show Commute Z₂ X₁ from hXZ.symm).left_comm Z₁, ← hZZ,
    (show Commute Z₂ Z₁ from hZZ.symm).left_comm X₁,
    (show Commute Z₁ X₂ from hZX).left_comm Z₂]
  abel





end Abstract

/-! ## The bound for the placed sandwiches -/



end

end MIPStarRE.QPBT

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
# Self-consistency of the sandwich POVM

The sandwich POVM `R^{x,z}_{a,b} = M^Z_b M^X_a M^Z_b` of
`MIPStarRE/QPBT/Combining/Points/Sandwich.lean` is approximately self-consistent
between opposite register placements.  The source establishes this by a
Cauchy--Schwarz chain (displays `eq:qld-rw-self-cons-1` to
`eq:qld-rw-self-cons-4`); here an exact identity is used instead.  Writing
`P_1, P_2` for the two placements of an operator `P`,
`W_b = (M^Z_b)_1 (M^Z_b)_2`, and `D^W_c = (M^W_c)_1 - (M^W_c)_2`, the
consistency defect of the two placed sandwiches equals
`(1/2) ∑_b ‖D^Z_b ψ‖^2 + (1/2) ∑_{a,b} ‖D^X_a W_b ψ‖^2`,
by two applications of the identity
`∑_c ⟨w, P_c Q_c w⟩ = ‖w‖^2 - (1/2) ∑_c ‖(P_c - Q_c) w‖^2` for projective
measurements.  The second sum is then bounded by the self-consistency of `M^X`
and the commutators on the two placements, since
`D^X_a W_b = W_b D^X_a + (M^Z_b)_2 K^1_{a,b} - (M^Z_b)_1 K^2_{a,b}`, where
`K^i_{a,b}` is the placed commutator of `M^X_a` and `M^Z_b`.

## Main results

* `sandwich_overlap_identity`: the exact expression of the overlap of two
  placed sandwiches.
* `sandwich_defect_pointwise_le`: the pointwise bound on the consistency
  defect of the sandwich for a fixed point pair.
* `ProjectiveSetting.sandwichDefectBound`,
  `ProjectiveSetting.sandwich_offDiagonal_le_sandwichDefectBound`, and
  `ProjectiveSetting.avg_sandwichDefectBound_le`: the bound as a function of
  the point pair, the pointwise estimate, and the average.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:743-790`,
blueprint `blueprint/src/chapter/ch15_qpbt_combining.tex:851-880`
(`lem:qld-4-10`, first step); the identity route is explained in
`docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Quadratic-form identities -/









/-! ## The overlap of two placed sandwiches -/



variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]

theorem solution (ψ : EuclideanSpace ℂ ι)
    (X₁ X₂ : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (Z₁ Z₂ : _root_.LIDT.MIPStarRE.Quantum.Measurement β ι)
    (hX₁ : _root_.MIPStarRE.QPBT.Measurement.IsProjective X₁)
    (hX₂ : _root_.MIPStarRE.QPBT.Measurement.IsProjective X₂)
    (hZ₁ : _root_.MIPStarRE.QPBT.Measurement.IsProjective Z₁)
    (hZ₂ : _root_.MIPStarRE.QPBT.Measurement.IsProjective Z₂)
    (hXZ : ∀ a b, X₁.effect a * Z₂.effect b = Z₂.effect b * X₁.effect a)
    (hZX : ∀ a b, Z₁.effect b * X₂.effect a = X₂.effect a * Z₁.effect b)
    (hZZ : ∀ b, Z₁.effect b * Z₂.effect b = Z₂.effect b * Z₁.effect b) :
    ‖ψ‖ ^ 2 - ∑ ab : α × β, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
        ((Z₁.effect ab.2 * X₁.effect ab.1 * Z₁.effect ab.2) *
          (Z₂.effect ab.2 * X₂.effect ab.1 * Z₂.effect ab.2)) ≤
      (1 / 2) * ∑ b, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (Z₁.effect b - Z₂.effect b) ψ‖ ^ 2 +
        (3 / 2) * ((∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (X₁.effect a - X₂.effect a) ψ‖ ^ 2) +
          (∑ ab : α × β, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (X₁.effect ab.1 * Z₁.effect ab.2 -
              Z₁.effect ab.2 * X₁.effect ab.1) ψ‖ ^ 2) +
          ∑ ab : α × β, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (X₂.effect ab.1 * Z₂.effect ab.2 -
              Z₂.effect ab.2 * X₂.effect ab.1) ψ‖ ^ 2) := by
  rw [_root_.MIPStarRE.QPBT.sandwich_overlap_identity ψ X₁ X₂ Z₁ Z₂ hX₁ hX₂ hZ₁ hZ₂ hXZ hZX hZZ]
  -- the pointwise decomposition of `(X_1 - X_2) W_b ψ`
  have hpt : ∀ ab : α × β,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (X₁.effect ab.1 - X₂.effect ab.1)
          (_root_.MIPStarRE.QPBT.applyOperatorToState (Z₁.effect ab.2 * Z₂.effect ab.2) ψ)‖ ^ 2 ≤
        3 * (‖_root_.MIPStarRE.QPBT.applyOperatorToState (Z₂.effect ab.2 *
              (X₁.effect ab.1 - X₂.effect ab.1)) ψ‖ ^ 2 +
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (X₁.effect ab.1 * Z₁.effect ab.2 -
              Z₁.effect ab.2 * X₁.effect ab.1) ψ‖ ^ 2 +
          ‖_root_.MIPStarRE.QPBT.applyOperatorToState
            (X₂.effect ab.1 * Z₂.effect ab.2 -
              Z₂.effect ab.2 * X₂.effect ab.1) ψ‖ ^ 2) := by
    intro ab
    obtain ⟨a, b⟩ := ab
    rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul,
      _root_.MIPStarRE.QPBT.sub_mul_mul_eq_add_commutators _ _ _ _ (hXZ a b) (hZX a b) (hZZ b)]
    have hlin : _root_.MIPStarRE.QPBT.applyOperatorToState
        (Z₁.effect b * Z₂.effect b * (X₁.effect a - X₂.effect a) +
          Z₂.effect b * (X₁.effect a * Z₁.effect b - Z₁.effect b * X₁.effect a) -
          Z₁.effect b * (X₂.effect a * Z₂.effect b - Z₂.effect b * X₂.effect a)) ψ =
        _root_.MIPStarRE.QPBT.applyOperatorToState (Z₁.effect b)
            (_root_.MIPStarRE.QPBT.applyOperatorToState (Z₂.effect b * (X₁.effect a - X₂.effect a)) ψ) +
          _root_.MIPStarRE.QPBT.applyOperatorToState (Z₂.effect b) (_root_.MIPStarRE.QPBT.applyOperatorToState
            (X₁.effect a * Z₁.effect b - Z₁.effect b * X₁.effect a) ψ) -
          _root_.MIPStarRE.QPBT.applyOperatorToState (Z₁.effect b) (_root_.MIPStarRE.QPBT.applyOperatorToState
            (X₂.effect a * Z₂.effect b - Z₂.effect b * X₂.effect a) ψ) := by
      rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul,
        ← _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul,
        ← _root_.MIPStarRE.QPBT.DistanceCalculus.applyOperatorToState_mul, Matrix.mul_assoc]
      unfold _root_.MIPStarRE.QPBT.applyOperatorToState
      simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    rw [hlin]
    set u := _root_.MIPStarRE.QPBT.applyOperatorToState (Z₁.effect b)
      (_root_.MIPStarRE.QPBT.applyOperatorToState (Z₂.effect b * (X₁.effect a - X₂.effect a)) ψ)
    set v := _root_.MIPStarRE.QPBT.applyOperatorToState (Z₂.effect b) (_root_.MIPStarRE.QPBT.applyOperatorToState
      (X₁.effect a * Z₁.effect b - Z₁.effect b * X₁.effect a) ψ)
    set w := _root_.MIPStarRE.QPBT.applyOperatorToState (Z₁.effect b) (_root_.MIPStarRE.QPBT.applyOperatorToState
      (X₂.effect a * Z₂.effect b - Z₂.effect b * X₂.effect a) ψ)
    have hu : ‖u‖ ≤ ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (Z₂.effect b * (X₁.effect a - X₂.effect a)) ψ‖ :=
      _root_.MIPStarRE.QPBT.norm_applyOperatorToState_proj_effect_le Z₁ hZ₁ b _
    have hv : ‖v‖ ≤ ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (X₁.effect a * Z₁.effect b - Z₁.effect b * X₁.effect a) ψ‖ :=
      _root_.MIPStarRE.QPBT.norm_applyOperatorToState_proj_effect_le Z₂ hZ₂ b _
    have hw : ‖w‖ ≤ ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (X₂.effect a * Z₂.effect b - Z₂.effect b * X₂.effect a) ψ‖ :=
      _root_.MIPStarRE.QPBT.norm_applyOperatorToState_proj_effect_le Z₁ hZ₁ b _
    have htri : ‖u + v - w‖ ≤ ‖u‖ + ‖v‖ + ‖w‖ :=
      le_trans (norm_sub_le (u + v) w) (add_le_add (norm_add_le u v) (le_refl ‖w‖))
    have hsq : ‖u + v - w‖ ^ 2 ≤ 3 * (‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2) := by
      nlinarith [sq_nonneg (‖u‖ - ‖v‖), sq_nonneg (‖v‖ - ‖w‖),
        sq_nonneg (‖u‖ - ‖w‖), norm_nonneg (u + v - w), norm_nonneg u,
        norm_nonneg v, norm_nonneg w]
    have hu2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
    have hv2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
    have hw2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    linarith
  -- the contraction sum over `b`
  have hcontr : ∑ ab : α × β, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (Z₂.effect ab.2 *
      (X₁.effect ab.1 - X₂.effect ab.1)) ψ‖ ^ 2 ≤
      ∑ a, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (X₁.effect a - X₂.effect a) ψ‖ ^ 2 := by
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun a _ => ?_
    exact _root_.MIPStarRE.QPBT.DistanceCalculus.sum_norm_mul_apply_le Z₂.effect (X₁.effect a - X₂.effect a) ψ
      (_root_.MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one Z₂)
  have hsum := Finset.sum_le_sum fun ab (_ : ab ∈ Finset.univ) => hpt ab
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  linarith
