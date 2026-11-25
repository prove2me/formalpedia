-- Prove2me | solution 1 for GlobalTheory.sum_addChar_trace_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:40:52.719739+00:00
-- url     : https://prove2.me/submissions/70ba4feb-aae0-4619-82ee-206ee2400025

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumSingularAndInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumMulDualEqCardPowSq

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
theorem _root_.solution {k : Type} [Field k] [Fintype k] [DecidableEq k] {R : Type}
    [CommRing R] [IsDomain R] (ψ : AddChar k R) (hψ : ψ.IsPrimitive) {r : ℕ}
    (m : Matrix (Fin r) (Fin r) k) :
    ∑ a : Matrix (Fin r) (Fin r) k, ψ (trace (a * m)) =
      if m = 0 then (Fintype.card k : R) ^ (r ^ 2) else 0 := by
  split_ifs with hm
  · subst hm
    simp only [Matrix.mul_zero, trace_zero, AddChar.map_zero_eq_one, sum_const, card_univ,
      nsmul_eq_mul, mul_one]
    rw [show Fintype.card (Matrix (Fin r) (Fin r) k) = Fintype.card (Fin r → Fin r → k) from rfl]
    simp [Fintype.card_fun, ← pow_mul, sq]
  · obtain ⟨i, j, hij⟩ : ∃ i j, m i j ≠ 0 := by
      by_contra h; push_neg at h; exact hm (Matrix.ext h)
    have h1 := hψ hij
    obtain ⟨c, hc⟩ : ∃ c, ψ (m i j * c) ≠ 1 := by
      by_contra h; push_neg at h; apply h1; ext c; simp [AddChar.mulShift_apply, h]
    set a₀ : Matrix (Fin r) (Fin r) k := Matrix.single j i c
    have ha₀ : trace (a₀ * m) = m i j * c := by
      simp [a₀, Matrix.trace_single_mul, mul_comm]
    set S := ∑ a : Matrix (Fin r) (Fin r) k, ψ (trace (a * m))
    have hS : S = ψ (trace (a₀ * m)) * S := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight a₀) _ _ (fun a => ?_)
      simp only [Equiv.subRight_apply, ← AddChar.map_add_eq_mul, Matrix.sub_mul, trace_sub]
      congr 1; ring
    rw [ha₀] at hS
    have : (1 - ψ (m i j * c)) * S = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hc
    · exact h
end GlobalTheory
