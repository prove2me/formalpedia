-- Prove2me | solution 1 for MIPStarRE.QPBT.DistanceCalculus.norm_finset_sum_projector_mul_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:53:00.030985+00:00
-- url     : https://prove2.me/submissions/c79dfb68-8881-4004-9c3e-170d39e1ebab

-- Generated proof for MIPStarRE.QPBT.DistanceCalculus.norm_finset_sum_projector_mul_sq_le.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_QPBT_QPBT_Games_Defs
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_quadratic_form_mono

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















/-- Gram expansion for a finite sum with mutually orthogonal left projectors. -/
private theorem gram_finset_sum_projector_mul {α ι : Type*}
    [Fintype ι]
    (P D : α → _root_.LIDT.MIPStarRE.Quantum.Op ι) (hproj : ∀ a, _root_.LIDT.MIPStarRE.Quantum.IsProj (P a))
    (horth : ∀ {a b}, a ≠ b → P a * P b = 0) (s : Finset α) :
    (∑ a ∈ s, P a * D a)ᴴ * (∑ a ∈ s, P a * D a) =
      ∑ a ∈ s, (D a)ᴴ * P a * D a := by
  classical
  let T : α → _root_.LIDT.MIPStarRE.Quantum.Op ι := fun a => P a * D a
  have hstar (a : α) : (P a)ᴴ = P a := by
    simpa [Matrix.star_eq_conjTranspose] using (hproj a).isSelfAdjoint.star_eq
  calc
    _ = (∑ a ∈ s, (T a)ᴴ) * (∑ b ∈ s, T b) := by
      simp only [T, Matrix.conjTranspose_sum]
    _ = ∑ a ∈ s, ∑ b ∈ s, (T a)ᴴ * T b := by
      rw [Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Matrix.mul_sum]
    _ = ∑ a ∈ s, (D a)ᴴ * P a * D a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_eq_single a]
      · simp only [T, Matrix.conjTranspose_mul, hstar a]
        rw [mul_assoc (D a)ᴴ (P a) (P a * D a),
          ← mul_assoc (P a) (P a) (D a), (hproj a).isIdempotentElem.eq]
        exact (mul_assoc (D a)ᴴ (P a) (D a)).symm
      · intro b _ hba
        calc
          (T a)ᴴ * T b = (D a)ᴴ * (P a * P b) * D b := by
            simp [T, Matrix.conjTranspose_mul, hstar a, mul_assoc]
          _ = 0 := by rw [horth (Ne.symm hba)]; simp
      · exact fun h => (h ha).elim









































































end MIPStarRE.QPBT.DistanceCalculus

/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

theorem solution {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (P D : α → _root_.LIDT.MIPStarRE.Quantum.Op ι) (hproj : ∀ a, _root_.LIDT.MIPStarRE.Quantum.IsProj (P a))
    (horth : ∀ {a b}, a ≠ b → P a * P b = 0)
    (s : Finset α) (ψ : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (∑ a ∈ s, P a * D a) ψ‖ ^ 2 ≤
      ∑ a : α, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (D a) ψ‖ ^ 2 := by
  classical
  have hgram :
      (∑ a ∈ s, P a * D a)ᴴ * (∑ a ∈ s, P a * D a) ≤
        ∑ a : α, (D a)ᴴ * D a := by
    rw [gram_finset_sum_projector_mul P D hproj horth s]
    calc
      ∑ a ∈ s, (D a)ᴴ * P a * D a ≤
          ∑ a ∈ s, (D a)ᴴ * D a := by
        refine Finset.sum_le_sum ?_
        intro a _
        simpa [Matrix.star_eq_conjTranspose] using
          (star_left_conjugate_le_conjugate (hproj a).le_one (D a))
      _ ≤ ∑ a : α, (D a)ᴴ * D a :=
        Finset.sum_le_sum_of_subset_of_nonneg (by simp)
          (fun a _ _ => (Matrix.posSemidef_conjTranspose_mul_self (D a)).nonneg)
  rw [norm_applyOperatorToState_sq_eq]
  calc
    (inner ℂ ψ (_root_.MIPStarRE.QPBT.applyOperatorToState
        ((∑ a ∈ s, P a * D a)ᴴ * (∑ a ∈ s, P a * D a)) ψ)).re ≤
        (inner ℂ ψ (_root_.MIPStarRE.QPBT.applyOperatorToState (∑ a : α, (D a)ᴴ * D a) ψ)).re :=
      _root_.MIPStarRE.QPBT.DistanceCalculus.quadratic_form_mono hgram ψ
    _ = ∑ a : α,
          (inner ℂ ψ (_root_.MIPStarRE.QPBT.applyOperatorToState ((D a)ᴴ * D a) ψ)).re := by
      simp [_root_.MIPStarRE.QPBT.applyOperatorToState]
    _ = ∑ a : α, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (D a) ψ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      exact (norm_applyOperatorToState_sq_eq (D a) ψ).symm
