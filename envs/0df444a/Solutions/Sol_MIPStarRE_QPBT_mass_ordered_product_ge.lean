-- Prove2me | solution 1 for MIPStarRE.QPBT.mass_ordered_product_ge
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:45:51.459762+00:00
-- url     : https://prove2.me/submissions/cf29ce98-68fe-4fb3-98d7-621986a68fce

-- Generated proof for MIPStarRE.QPBT.mass_ordered_product_ge.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono
import Theorems.Thm_MIPStarRE_QPBT_sum_norm_ordered_product_le_one

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

/- Source helpers from QPBT/Games/Sandwich/Pasting/Assembly.lean. -/
/-! # Ordered product masses and the assembly of the pasting estimate

This module records the mass estimates of step 3 of the proof of the adopted
statement of `lem:pasting`, the fine commutator mass of step 5, the assembly of
those estimates into the explicit bound on the defect of the pasted family, the
bound of one on the defect of an arbitrary pair of placed families, and the
scalar comparison of the assembled bound with the error function of the
theorem.  The proof of the adopted statement is recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `ch12_qpbt_games.tex:960-990`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open DistanceCalculus

/-- The squared norm of the image of a state is the quadratic form of the
operator against its adjoint.  This is a formalization-only auxiliary of the
distance calculus, stated here for the assembly of `lem:pasting`. -/
private theorem norm_sq_eq_stateQForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState X ψ‖ ^ 2 = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (Xᴴ * X) := by
  have hqf : ∀ M N : _root_.LIDT.MIPStarRE.Quantum.Op ι, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M * N) =
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
  have hkey := hqf Xᴴ X
  rw [Matrix.conjTranspose_conjTranspose] at hkey
  rw [hkey]
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (_root_.MIPStarRE.QPBT.applyOperatorToState X ψ)).symm

/-- A family whose adjoint products sum to the identity preserves the total
mass of a state. -/
private theorem sum_norm_sq_eq_of_sum_adjoint_mul_eq_one {γ ι : Type*}
    [Fintype γ] [Fintype ι] [DecidableEq ι]
    (C : γ → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι)
    (hC : (∑ c : γ, (C c)ᴴ * C c) = 1) :
    (∑ c : γ, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (C c) ψ‖ ^ 2) = ‖ψ‖ ^ 2 := by
  have hone : _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) = ‖ψ‖ ^ 2 := by
    have hid : _root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ψ = ψ := by
      simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, hid]
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) ψ)
  calc (∑ c : γ, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (C c) ψ‖ ^ 2)
      = ∑ c : γ, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ ((C c)ᴴ * C c) :=
        Finset.sum_congr rfl fun c _ => norm_sq_eq_stateQForm (C c) ψ
    _ = _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ c : γ, (C c)ᴴ * C c) := (_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum ψ _ _).symm
    _ = ‖ψ‖ ^ 2 := by rw [hC, hone]

/-- A perturbation estimate for the total mass of a finite family of vectors:
the mass of a family of mass at most one increases by at most twice the square
root of the summed squared distance, plus that distance. -/
private theorem sum_norm_sq_le_of_mass_le_one {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (u v : α → EuclideanSpace ℂ ι) (hu : (∑ a : α, ‖u a‖ ^ 2) ≤ 1) :
    (∑ a : α, ‖v a‖ ^ 2) ≤ (∑ a : α, ‖u a‖ ^ 2) +
      2 * Real.sqrt (∑ a : α, ‖u a - v a‖ ^ 2) + ∑ a : α, ‖u a - v a‖ ^ 2 := by
  have hpt : ∀ a : α, ‖v a‖ ^ 2 ≤
      ‖u a‖ ^ 2 + 2 * (‖u a‖ * ‖u a - v a‖) + ‖u a - v a‖ ^ 2 := by
    intro a
    have hle : ‖v a‖ ≤ ‖u a‖ + ‖u a - v a‖ := by
      have := norm_sub_le (u a) (u a - v a)
      simpa using this
    nlinarith [norm_nonneg (v a), norm_nonneg (u a), norm_nonneg (u a - v a)]
  have hsum : (∑ a : α, ‖v a‖ ^ 2) ≤
      (∑ a : α, ‖u a‖ ^ 2) + 2 * (∑ a : α, ‖u a‖ * ‖u a - v a‖) +
        ∑ a : α, ‖u a - v a‖ ^ 2 := by
    have := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpt a)
    simpa [Finset.sum_add_distrib, Finset.mul_sum] using this
  have hcs : (∑ a : α, ‖u a‖ * ‖u a - v a‖) ≤
      Real.sqrt (∑ a : α, ‖u a‖ ^ 2) * Real.sqrt (∑ a : α, ‖u a - v a‖ ^ 2) := by
    simpa using Real.sum_mul_le_sqrt_mul_sqrt (s := (Finset.univ : Finset α))
      (f := fun a => ‖u a‖) (g := fun a => ‖u a - v a‖)
  have hsq : Real.sqrt (∑ a : α, ‖u a‖ ^ 2) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hu
  have hnn : 0 ≤ Real.sqrt (∑ a : α, ‖u a - v a‖ ^ 2) := Real.sqrt_nonneg _
  nlinarith [hsum, hcs, hsq, hnn]























end MIPStarRE.QPBT

/-! # Ordered product masses and the assembly of the pasting estimate

This module records the mass estimates of step 3 of the proof of the adopted
statement of `lem:pasting`, the fine commutator mass of step 5, the assembly of
those estimates into the explicit bound on the defect of the pasted family, the
bound of one on the defect of an arbitrary pair of placed families, and the
scalar comparison of the assembled bound with the error function of the
theorem.  The proof of the adopted statement is recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `ch12_qpbt_games.tex:960-990`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

theorem solution {X R₁ R₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype ι] [DecidableEq ι]
    (D : _root_.LIDT.MIPStarRE.LDT.Distribution X) (Ac P : X → _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι) (Q : X → _root_.LIDT.MIPStarRE.Quantum.Measurement R₂ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (d K : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1)
    (hAc : ∀ q, _root_.MIPStarRE.QPBT.Measurement.IsProjective (Ac q))
    (hQ : ∀ q, _root_.MIPStarRE.QPBT.Measurement.IsProjective (Q q))
    (hd : _root_.MIPStarRE.QPBT.opFamilyDistSq D (fun q a => _root_.MIPStarRE.QPBT.heteroKron ((Ac q).effect a) 1)
      (fun q a => _root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect a)) ψ ≤ d)
    (hK : _root_.MIPStarRE.QPBT.opFamilyDistSq D (fun q (ab : R₁ × R₂) => _root_.MIPStarRE.QPBT.heteroKron 1
      ((P q).effect ab.1 * (Q q).effect ab.2 -
        (Q q).effect ab.2 * (P q).effect ab.1)) (fun _ _ => 0) ψ ≤ K) :
    1 - 2 * Real.sqrt d - d - 2 * Real.sqrt K - K ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => ∑ ab : R₁ × R₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect ab.1 * (Q q).effect ab.2)) ψ‖ ^ 2) := by
  classical
  -- the inlined identities of the distance calculus; see issue Dengnifer/MIPStarRE-QPBT-bak#204
  have hct : ∀ M N : _root_.LIDT.MIPStarRE.Quantum.Op ι, (_root_.MIPStarRE.QPBT.heteroKron M N)ᴴ = _root_.MIPStarRE.QPBT.heteroKron Mᴴ Nᴴ := by
    intro M N
    unfold _root_.MIPStarRE.QPBT.heteroKron
    exact Matrix.conjTranspose_kronecker M N
  have hmulapp : ∀ (M N : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)), _root_.MIPStarRE.QPBT.applyOperatorToState (M * N) ψ =
      _root_.MIPStarRE.QPBT.applyOperatorToState M (_root_.MIPStarRE.QPBT.applyOperatorToState N ψ) := by
    intro M N
    unfold _root_.MIPStarRE.QPBT.applyOperatorToState
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
  have hlin : ∀ M N : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι), _root_.MIPStarRE.QPBT.applyOperatorToState (M - N) ψ =
      _root_.MIPStarRE.QPBT.applyOperatorToState M ψ - _root_.MIPStarRE.QPBT.applyOperatorToState N ψ := by
    intro M N
    simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
  have hsubr : ∀ M N : _root_.LIDT.MIPStarRE.Quantum.Op ι,
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) (M - N) = _root_.MIPStarRE.QPBT.heteroKron 1 M - _root_.MIPStarRE.QPBT.heteroKron 1 N := by
    intro M N
    ext p r
    simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, mul_sub]
  set S : X → ℝ := fun q => ∑ a : R₁,
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect a)) ψ‖ ^ 2 with hS
  set C1 : X → ℝ := fun q => ∑ ab : R₁ × R₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
    (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect ab.1 * (Q q).effect ab.2)) ψ‖ ^ 2 with hC1
  set dq : X → ℝ := fun q => ∑ a : R₁, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
    (_root_.MIPStarRE.QPBT.heteroKron ((Ac q).effect a) 1 - _root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect a)) ψ‖ ^ 2 with hdq
  set kq : X → ℝ := fun q => ∑ ab : R₁ × R₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
    (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect ab.1 * (Q q).effect ab.2 -
      (Q q).effect ab.2 * (P q).effect ab.1)) ψ‖ ^ 2 with hkq
  -- the projective family placed on the first factor carries the whole mass
  have hAcmass : ∀ q : X, (∑ a : R₁,
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron ((Ac q).effect a) 1) ψ‖ ^ 2) = 1 := by
    intro q
    have hterm : ∀ a : R₁, (_root_.MIPStarRE.QPBT.heteroKron ((Ac q).effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))ᴴ *
        _root_.MIPStarRE.QPBT.heteroKron ((Ac q).effect a) 1 = _root_.MIPStarRE.QPBT.heteroKron ((Ac q).effect a) 1 := by
      intro a
      rw [hct, Matrix.conjTranspose_one, _root_.MIPStarRE.QPBT.heteroKron_mul, mul_one,
        _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian (Ac q) a, (hAc q a).isIdempotentElem.eq]
    have hsum : (∑ a : R₁, (_root_.MIPStarRE.QPBT.heteroKron ((Ac q).effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι))ᴴ *
        _root_.MIPStarRE.QPBT.heteroKron ((Ac q).effect a) 1) = 1 := by
      rw [Finset.sum_congr rfl fun a _ => hterm a,
        ← _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left, (Ac q).sum_eq_one, _root_.MIPStarRE.QPBT.heteroKron_one_one]
    rw [sum_norm_sq_eq_of_sum_adjoint_mul_eq_one _ ψ hsum, hψ, one_pow]
  -- the mass of a placed measurement is at most one
  have hone : _root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) ψ = ψ := by
    simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
  have hSle : ∀ q : X, S q ≤ 1 := by
    intro q
    have hCP : ∑ a : R₁, (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ((P q).effect a))ᴴ *
        _root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect a) ≤ 1 := by
      simpa using _root_.MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
        (_root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ι) (P q))
    have h := _root_.MIPStarRE.QPBT.DistanceCalculus.sum_norm_mul_apply_le
      (fun a : R₁ => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ((P q).effect a))
      (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ι × ι)) ψ hCP
    rw [hone, hψ, one_pow] at h
    simpa [hS] using h
  have hC1le : ∀ q : X, C1 q ≤ 1 := by
    intro q
    simp only [hC1]
    rw [Fintype.sum_prod_type]
    exact _root_.MIPStarRE.QPBT.sum_norm_ordered_product_le_one (P q) (Q q) ψ hψ
  -- reversing the order of the placements preserves the mass
  have hRv : ∀ q : X, (∑ ab : R₁ × R₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
      (_root_.MIPStarRE.QPBT.heteroKron 1 ((Q q).effect ab.2 * (P q).effect ab.1)) ψ‖ ^ 2) = S q := by
    intro q
    have hQsum : (∑ b : R₂, (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ((Q q).effect b))ᴴ *
        _root_.MIPStarRE.QPBT.heteroKron 1 ((Q q).effect b)) = 1 := by
      have hterm : ∀ b : R₂, (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ((Q q).effect b))ᴴ *
          _root_.MIPStarRE.QPBT.heteroKron 1 ((Q q).effect b) = _root_.MIPStarRE.QPBT.heteroKron 1 ((Q q).effect b) := by
        intro b
        rw [hct, Matrix.conjTranspose_one, _root_.MIPStarRE.QPBT.heteroKron_mul, mul_one,
          _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian (Q q) b, (hQ q b).isIdempotentElem.eq]
      rw [Finset.sum_congr rfl fun b _ => hterm b,
        ← _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, (Q q).sum_eq_one, _root_.MIPStarRE.QPBT.heteroKron_one_one]
    rw [Fintype.sum_prod_type, hS]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hsplit : ∀ b : R₂, _root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron 1 ((Q q).effect b * (P q).effect a)) ψ =
        _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ((Q q).effect b))
          (_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect a)) ψ) := by
      intro b
      rw [← hmulapp, _root_.MIPStarRE.QPBT.heteroKron_mul, one_mul]
    rw [Finset.sum_congr rfl fun b _ => by rw [hsplit b]]
    exact sum_norm_sq_eq_of_sum_adjoint_mul_eq_one _ _ hQsum
  -- the two perturbation estimates at a fixed question
  have hP1 : ∀ q : X, 1 ≤ S q + 2 * Real.sqrt (dq q) + dq q := by
    intro q
    have h := sum_norm_sq_le_of_mass_le_one
      (fun a : R₁ => _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect a)) ψ)
      (fun a : R₁ => _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron ((Ac q).effect a) 1) ψ)
      (by simpa [hS] using hSle q)
    have hdist : (∑ a : R₁, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect a)) ψ -
        _root_.MIPStarRE.QPBT.applyOperatorToState (_root_.MIPStarRE.QPBT.heteroKron ((Ac q).effect a) 1) ψ‖ ^ 2) = dq q := by
      rw [hdq]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hlin, norm_sub_rev]
    rw [hAcmass q, hdist] at h
    simpa [hS] using h
  have hP2 : ∀ q : X, S q ≤ C1 q + 2 * Real.sqrt (kq q) + kq q := by
    intro q
    have h := sum_norm_sq_le_of_mass_le_one
      (fun ab : R₁ × R₂ => _root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect ab.1 * (Q q).effect ab.2)) ψ)
      (fun ab : R₁ × R₂ => _root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron 1 ((Q q).effect ab.2 * (P q).effect ab.1)) ψ)
      (by simpa [hC1] using hC1le q)
    have hdist : (∑ ab : R₁ × R₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect ab.1 * (Q q).effect ab.2)) ψ -
        _root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.heteroKron 1 ((Q q).effect ab.2 * (P q).effect ab.1)) ψ‖ ^ 2) = kq q := by
      rw [hkq]
      refine Finset.sum_congr rfl fun ab _ => ?_
      rw [hsubr, hlin]
    rw [hRv q, hdist] at h
    simpa [hC1] using h
  -- averaging the two estimates over the question
  have hdnn : ∀ q : X, 0 ≤ dq q := fun q => Finset.sum_nonneg fun a _ => sq_nonneg _
  have hknn : ∀ q : X, 0 ≤ kq q := fun q => Finset.sum_nonneg fun ab _ => sq_nonneg _
  have hdavg : _root_.LIDT.MIPStarRE.LDT.avgOver D dq ≤ d := hd
  have hkavg : _root_.LIDT.MIPStarRE.LDT.avgOver D kq ≤ K := by
    refine le_trans (le_of_eq ?_) hK
    refine (_root_.LIDT.MIPStarRE.LDT.avgOver_congr D _ _ fun q => ?_).symm
    exact Finset.sum_congr rfl fun ab _ => by rw [sub_zero]
  have hJd : _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => Real.sqrt (dq q)) ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver D dq) :=
    le_trans (le_abs_self _)
      (_root_.LIDT.MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise D _ dq
        (fun q => by rw [abs_of_nonneg (Real.sqrt_nonneg _)]) hdnn
        (by rw [hD.weight_sum_eq_one]))
  have hJk : _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => Real.sqrt (kq q)) ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver D kq) :=
    le_trans (le_abs_self _)
      (_root_.LIDT.MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise D _ kq
        (fun q => by rw [abs_of_nonneg (Real.sqrt_nonneg _)]) hknn
        (by rw [hD.weight_sum_eq_one]))
  have hA1 : (1 : ℝ) ≤ _root_.LIDT.MIPStarRE.LDT.avgOver D S + 2 * _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => Real.sqrt (dq q)) +
      _root_.LIDT.MIPStarRE.LDT.avgOver D dq := by
    have hmono := _root_.LIDT.MIPStarRE.LDT.avgOver_mono D (fun _ : X => (1 : ℝ))
      (fun q => S q + 2 * Real.sqrt (dq q) + dq q) hP1
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability D hD, _root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_add,
      _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul] at hmono
    exact hmono
  have hA2 : _root_.LIDT.MIPStarRE.LDT.avgOver D S ≤ _root_.LIDT.MIPStarRE.LDT.avgOver D C1 + 2 * _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => Real.sqrt (kq q)) +
      _root_.LIDT.MIPStarRE.LDT.avgOver D kq := by
    have hmono := _root_.LIDT.MIPStarRE.LDT.avgOver_mono D S
      (fun q => C1 q + 2 * Real.sqrt (kq q) + kq q) hP2
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul] at hmono
    exact hmono
  have hsd : Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver D dq) ≤ Real.sqrt d := Real.sqrt_le_sqrt hdavg
  have hsk : Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver D kq) ≤ Real.sqrt K := Real.sqrt_le_sqrt hkavg
  linarith
