-- Prove2me | solution 1 for MIPStarRE.QPBT.pasting_error_heterogeneous_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:08:33.019085+00:00
-- url     : https://prove2.me/submissions/4ddd18e1-44a8-4c96-9c87-3a5a1ced6dbb

-- Generated proof for MIPStarRE.QPBT.pasting_error_heterogeneous_explicit.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Pasting_Heterogeneous
import Theorems.Thm_MIPStarRE_QPBT_pasting_error_of_marginal_consistency_explicit

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
namespace MIPStarRE.QPBT.Pasting
end MIPStarRE.QPBT.Pasting
namespace MIPStarRE.QPBT.SandwichProduct
end MIPStarRE.QPBT.SandwichProduct

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
4.14): the matrix-vector term in `consistencyDefect` is the state quadratic
form. -/
theorem consistency_term_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (M : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    (inner ℂ ψ ((EuclideanSpace.equiv ι ℂ).symm (M.mulVec ψ))).re =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ M := by
  rfl



































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/Sandwich/Defs.lean. -/
/-! # Definitions for sandwiched measurements

This module defines the palindromic operator products and the conditional
collision predicate used by the sandwich and pasting lemmas.

## References

Blueprint `lem:ld-sandwich` and `lem:pasting`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-525`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open DistanceCalculus












/-! ### Tensor placements of measurements

The operator families compared in `lem:pasting` are placed on one factor of a
bipartite space. The two constructions below present such a placed family as a
measurement, so that the consistency calculus applies to it verbatim. -/









/-- The left placement of a projective measurement is projective.
Formalization support for `lem:pasting`, blueprint
`ch12_qpbt_games.tex:960-990`. -/
theorem Measurement.isProjective_leftPlacement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (_root_.MIPStarRE.QPBT.Measurement.leftPlacement (ιB := ιB) M) := by
  intro a
  constructor
  · show _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1 * _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1 =
      _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, (hM a).isIdempotentElem.eq, mul_one]
  · show (_root_.MIPStarRE.QPBT.heteroKron (M.effect a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB))ᴴ = _root_.MIPStarRE.QPBT.heteroKron (M.effect a) 1
    unfold _root_.MIPStarRE.QPBT.heteroKron Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian M a,
      Matrix.conjTranspose_one]

/-- The right placement of a projective measurement is projective. This is the
right-factor mirror of the preceding lemma and the second of the four
properties of the placement collected in the formalization-support node
`lem:pasting-tensor-placement`, blueprint `ch12_qpbt_games.tex:1063-1071`. -/
theorem Measurement.isProjective_rightPlacement {α ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB) (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (_root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ιA) M) := by
  intro a
  constructor
  · show _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (M.effect a) * _root_.MIPStarRE.QPBT.heteroKron 1 (M.effect a) =
      _root_.MIPStarRE.QPBT.heteroKron 1 (M.effect a)
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, (hM a).isIdempotentElem.eq, mul_one]
  · show (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (M.effect a))ᴴ = _root_.MIPStarRE.QPBT.heteroKron 1 (M.effect a)
    unfold _root_.MIPStarRE.QPBT.heteroKron Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian M a,
      Matrix.conjTranspose_one]

/-- Postprocessing commutes with the left tensor placement. This is one of the
four properties of the placement collected in the formalization-support node
`lem:pasting-tensor-placement`, blueprint `ch12_qpbt_games.tex:1063-1071`; it
records the compatibility of the placement of `lem:pasting` with the outcome
coarse-grainings its statement applies, and is stated for the left factor
alongside its right-factor mirror below. -/
theorem Measurement.leftPlacement_postprocess {α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιA) (f : α → β) (b : β) :
    (_root_.MIPStarRE.QPBT.Measurement.leftPlacement (ιB := ιB) (M.postprocess f)).effect b =
      ((_root_.MIPStarRE.QPBT.Measurement.leftPlacement (ιB := ιB) M).postprocess f).effect b := by
  classical
  simp only [_root_.MIPStarRE.QPBT.Measurement.leftPlacement_effect, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
    _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left]

/-- Postprocessing commutes with the right tensor placement. This is the
right-factor mirror of the preceding compatibility, the fourth of the four
properties of the placement collected in the formalization-support node
`lem:pasting-tensor-placement`, blueprint `ch12_qpbt_games.tex:1063-1071`. -/
theorem Measurement.rightPlacement_postprocess {α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ιB) (f : α → β) (b : β) :
    (_root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ιA) (M.postprocess f)).effect b =
      ((_root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ιA) M).postprocess f).effect b := by
  classical
  simp only [_root_.MIPStarRE.QPBT.Measurement.rightPlacement_effect, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
    _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right]










end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/Sandwich/Pasting/Heterogeneous.lean. -/
/-! # Pasting on independent local spaces

The two local spaces are realized in a common product space by adjoining fixed
basis vectors. Tensor placement supplies the corresponding
measurements, with projectivity and postprocessing preserved.

## References

Paper `lem:pasting`,
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`, and its use in
`lem:qld-xz-lines`, `14_analysis_of_the_pauli_basis_test.tex:882-963`.
The common-space realization is a formalization-only auxiliary; see issue
Dengnifer/MIPStarRE-QPBT-bak#495.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open DistanceCalculus



namespace Pasting

variable {ιA ιB : Type*}
  [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]



/-- Adjoining unit basis vectors preserves the state norm. Formalization-only
auxiliary, blueprint `lem:pasting-product-state-preservation`. -/
theorem productPaddedState_norm (a₀ : ιA) (b₀ : ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖_root_.MIPStarRE.QPBT.Pasting.productPaddedState a₀ b₀ ψ‖ = ‖ψ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [EuclideanSpace.norm_sq_eq, _root_.MIPStarRE.QPBT.Pasting.productPaddedState, Fintype.sum_prod_type, apply_ite]

/-- Local tensor padding preserves every bipartite quadratic form. This exact
identity is independent of positivity and of normalization of the state.
Formalization-only auxiliary, blueprint `lem:pasting-product-state-preservation`. -/
theorem stateQForm_productPaddedState (a₀ : ιA) (b₀ : ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.Pasting.productPaddedState a₀ b₀ ψ)
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron A (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB)) (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) B)) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A B) := by
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm _root_.MIPStarRE.QPBT.applyOperatorToState
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  apply congrArg Complex.re
  simp [_root_.MIPStarRE.QPBT.Pasting.productPaddedState, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct,
    _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Finset.sum_mul, apply_ite]

/-- Tensor padding preserves the off-diagonal consistency defect for arbitrary
operator families. No measurement or probability assumption is required.
Formalization-only auxiliary, blueprint `lem:pasting-product-state-preservation`. -/
theorem consistencyDefect_productPaddedState {X α : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    (D : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ιB)
    (a₀ : ιA) (b₀ : ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.consistencyDefect D
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.heteroKron (A x a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB)) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB)))
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB)) (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B x a)))
        (_root_.MIPStarRE.QPBT.Pasting.productPaddedState a₀ b₀ ψ) =
      _root_.MIPStarRE.QPBT.consistencyDefect D (fun x a => _root_.MIPStarRE.QPBT.heteroKron (A x a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB))
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B x a)) ψ := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.consistency_term_eq_stateQForm, _root_.MIPStarRE.QPBT.heteroKron_mul, mul_one, one_mul,
    _root_.MIPStarRE.QPBT.Pasting.stateQForm_productPaddedState]

end Pasting













end MIPStarRE.QPBT

/-! # Pasting on independent local spaces

The two local spaces are realized in a common product space by adjoining fixed
basis vectors. Tensor placement supplies the corresponding
measurements, with projectivity and postprocessing preserved.

## References

Paper `lem:pasting`,
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`, and its use in
`lem:qld-xz-lines`, `14_analysis_of_the_pauli_basis_test.tex:882-963`.
The common-space realization is a formalization-only auxiliary; see issue
Dengnifer/MIPStarRE-QPBT-bak#495.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus



open MIPStarRE.QPBT.Pasting

variable {ιA ιB : Type*}
  [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

theorem solution :
    ∀ {X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ιA ιB : Type*}
        [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
        [Fintype Y₂] [DecidableEq Y₂] [Fintype R₁] [DecidableEq R₁]
        [Fintype R₂] [DecidableEq R₂]
        [Fintype Γ₁] [DecidableEq Γ₁] [Fintype Γ₂] [DecidableEq Γ₂]
        [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
        (D : _root_.LIDT.MIPStarRE.LDT.Distribution ((X × Y₁) × Y₂))
        (eval₁ : Γ₁ → Y₁ → R₁) (eval₂ : Γ₂ → Y₂ → R₂)
        (G₁ : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₁ ιB) (G₂ : X → _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ιB)
        (A : ((X × Y₁) × Y₂) → _root_.LIDT.MIPStarRE.Quantum.Measurement (R₁ × R₂) ιA)
        (ψ : EuclideanSpace ℂ (ιA × ιB)) (η δ : ℝ),
        D.IsProbability → ‖ψ‖ = 1 → 0 ≤ η → 0 ≤ δ →
        (∀ x, _root_.MIPStarRE.QPBT.Measurement.IsProjective (G₂ x)) →
        (∀ q, _root_.MIPStarRE.QPBT.Measurement.IsProjective (A q)) →
        _root_.MIPStarRE.QPBT.HasConditionalCollisionBound D eval₂ η →
        _root_.MIPStarRE.QPBT.consistencyDefect D
          (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.fst).effect a₁) 1)
          (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₁ q.1.1).postprocess
            (fun g => eval₁ g q.1.2)).effect a₁)) ψ ≤ δ →
        _root_.MIPStarRE.QPBT.consistencyDefect D
          (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron (((A q).postprocess Prod.snd).effect a₂) 1)
          (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₂ q.1.1).postprocess
            (fun g => eval₂ g q.2)).effect a₂)) ψ ≤ δ →
        _root_.MIPStarRE.QPBT.consistencyDefect D (fun q a => _root_.MIPStarRE.QPBT.heteroKron ((A q).effect a) 1)
          (fun q a => _root_.MIPStarRE.QPBT.heteroKron 1 (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
            if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
              _root_.MIPStarRE.QPBT.pastedMeasurement (fun g => (G₁ q.1.1).effect g)
                (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0)) ψ ≤
          115 * (η ^ (1 / 4 : ℝ) + δ ^ (1 / 8 : ℝ)) := by
  classical
  intro X Y₁ Y₂ R₁ R₂ Γ₁ Γ₂ ιA ιB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    D eval₁ eval₂ G₁ G₂ A ψ η δ hD hψ hη hδ hG₂ hA hcoll h₁ h₂
  have hnonempty : Nonempty (ιA × ιB) := by
    rcases isEmpty_or_nonempty (ιA × ιB) with h | h
    · letI := h
      have hz : ψ = 0 := Subsingleton.elim _ _
      simp [hz] at hψ
    · exact h
  obtain ⟨⟨a₀, b₀⟩⟩ := hnonempty
  let A' := fun q => _root_.MIPStarRE.QPBT.Measurement.leftPlacement (ιB := ιB) (A q)
  let G₁' := fun x => _root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ιA) (G₁ x)
  let G₂' := fun x => _root_.MIPStarRE.QPBT.Measurement.rightPlacement (ιA := ιA) (G₂ x)
  let ψ' := _root_.MIPStarRE.QPBT.Pasting.productPaddedState a₀ b₀ ψ
  have hψ' : ‖ψ'‖ = 1 := (_root_.MIPStarRE.QPBT.Pasting.productPaddedState_norm a₀ b₀ ψ).trans hψ
  have h₁' : _root_.MIPStarRE.QPBT.consistencyDefect D
      (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron (((A' q).postprocess Prod.fst).effect a₁) 1)
      (fun q a₁ => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₁' q.1.1).postprocess
        (fun g => eval₁ g q.1.2)).effect a₁)) ψ' ≤ δ := by
    simpa only [A', G₁', ψ', ← _root_.MIPStarRE.QPBT.Measurement.leftPlacement_postprocess,
      ← _root_.MIPStarRE.QPBT.Measurement.rightPlacement_postprocess, _root_.MIPStarRE.QPBT.Measurement.leftPlacement_effect,
      _root_.MIPStarRE.QPBT.Measurement.rightPlacement_effect, _root_.MIPStarRE.QPBT.Pasting.consistencyDefect_productPaddedState] using h₁
  have h₂' : _root_.MIPStarRE.QPBT.consistencyDefect D
      (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron (((A' q).postprocess Prod.snd).effect a₂) 1)
      (fun q a₂ => _root_.MIPStarRE.QPBT.heteroKron 1 (((G₂' q.1.1).postprocess
        (fun g => eval₂ g q.2)).effect a₂)) ψ' ≤ δ := by
    simpa only [A', G₂', ψ', ← _root_.MIPStarRE.QPBT.Measurement.leftPlacement_postprocess,
      ← _root_.MIPStarRE.QPBT.Measurement.rightPlacement_postprocess, _root_.MIPStarRE.QPBT.Measurement.leftPlacement_effect,
      _root_.MIPStarRE.QPBT.Measurement.rightPlacement_effect, _root_.MIPStarRE.QPBT.Pasting.consistencyDefect_productPaddedState] using h₂
  have hpadded := _root_.MIPStarRE.QPBT.pasting_error_of_marginal_consistency_explicit
    D eval₁ eval₂ G₁' G₂' A' ψ' η δ hD hψ' hη hδ
    (fun x => _root_.MIPStarRE.QPBT.Measurement.isProjective_rightPlacement (G₂ x) (hG₂ x))
    (fun q => _root_.MIPStarRE.QPBT.Measurement.isProjective_leftPlacement (A q) (hA q)) hcoll h₁' h₂'
  have hpaste (q : (X × Y₁) × Y₂) (a : R₁ × R₂) :
      (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
        if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
          _root_.MIPStarRE.QPBT.pastedMeasurement (fun g => (G₁' q.1.1).effect g)
            (fun g => (G₂' q.1.1).effect g) g₁ g₂ else 0) =
        _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (∑ g₁ : Γ₁, ∑ g₂ : Γ₂,
          if (eval₁ g₁ q.1.2, eval₂ g₂ q.2) = a then
            _root_.MIPStarRE.QPBT.pastedMeasurement (fun g => (G₁ q.1.1).effect g)
              (fun g => (G₂ q.1.1).effect g) g₁ g₂ else 0) := by
    simp only [G₁', G₂', _root_.MIPStarRE.QPBT.Measurement.rightPlacement_effect, _root_.MIPStarRE.QPBT.pastedMeasurement,
      _root_.MIPStarRE.QPBT.heteroKron_mul, one_mul]
    simp_rw [_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right]
    apply Finset.sum_congr rfl
    intro g₁ _
    apply Finset.sum_congr rfl
    intro g₂ _
    split_ifs <;> simp [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker]
  simp_rw [hpaste] at hpadded
  simpa only [A', ψ', _root_.MIPStarRE.QPBT.Measurement.leftPlacement_effect,
    _root_.MIPStarRE.QPBT.Pasting.consistencyDefect_productPaddedState] using hpadded
