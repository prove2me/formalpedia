-- Prove2me | solution 1 for GlobalTheory.matrixGaussSum_mul_dual_eq_card_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:58.009714+00:00
-- url     : https://prove2.me/submissions/7ec7525d-46ab-4a89-8bb7-13687c32ae9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumSingularAndInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumMulDualEqCardPowSq
import Theorems.Thm_GlobalTheory_sum_addChar_trace_mul_eq
import Theorems.Thm_GlobalTheory_matrixGaussSum_singular_and_invertible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped TensorProduct Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type) [CommRing R] [IsDomain R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) * (∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ⁻¹ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) = (Fintype.card k : R) ^ (r ^ 2) := by
  intro k _ _ _ R _ _ ψ ξ r hψ hξ
  obtain ⟨hsing, hinv⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k R ψ ξ r hψ hξ
  let S : Matrix (Fin r) (Fin r) k → R := fun a => ∑ x : GL (Fin r) k,
    (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (trace (a * (x : Matrix (Fin r) (Fin r) k)))

  have key1 : ∑ a, S a * ψ (-trace a) = (Fintype.card k : R) ^ (r ^ 2) := by
    simp only [S, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hx : ∀ x : GL (Fin r) k, ∑ a : Matrix (Fin r) (Fin r) k,
        (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (trace (a * (x : Matrix (Fin r) (Fin r) k))) * ψ (-trace a)
        = (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) *
          ∑ a : Matrix (Fin r) (Fin r) k, ψ (trace (a * ((x : Matrix (Fin r) (Fin r) k) - 1))) := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_assoc, ← AddChar.map_add_eq_mul, Matrix.mul_sub, Matrix.mul_one, trace_sub, sub_eq_add_neg]
    simp_rw [hx, sum_addChar_trace_mul_eq ψ hψ]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro x _ hx1
      rw [if_neg, mul_zero]
      intro h
      apply hx1
      ext1
      simpa using sub_eq_zero.mp h
    · simp

  have key2 : ∑ a, S a * ψ (-trace a) =
      ∑ g : GL (Fin r) k, S (g : Matrix (Fin r) (Fin r) k) * ψ (-trace (g : Matrix (Fin r) (Fin r) k)) := by
    symm
    refine Fintype.sum_of_injective (fun g : GL (Fin r) k => (g : Matrix (Fin r) (Fin r) k)) (fun g h e => Units.ext e) _ _ ?_ (fun g => rfl)
    intro a ha
    have hdet : a.det = 0 := by
      by_contra h
      exact ha ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero a h, rfl⟩
    simp only [S]
    rw [hsing a hdet, zero_mul]
  rw [← key1, key2]
  simp only [S]
  simp_rw [hinv]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp [MonoidHom.inv_apply, AddChar.inv_apply]
  ring
end GlobalTheory
