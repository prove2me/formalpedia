-- Prove2me | solution 1 for GlobalTheory.exists_isSymm_mulVec_add_diag_mod_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:42:37.946266+00:00
-- url     : https://prove2.me/submissions/a76cfc0d-886f-4108-83dc-09f39d599d5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsIsSymmMulVecAddDiagModTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (g : ℕ) (n n' : Fin g → ℤ), Even (n ⬝ᵥ n') →
      ∃ S : Matrix (Fin g) (Fin g) ℤ, S.IsSymm ∧
        ∀ i, (2 : ℤ) ∣ (S.mulVec n) i + S i i - n' i := by
  intro g n n' h
  by_cases hall : ∀ i, Even (n i)
  · refine ⟨Matrix.diagonal n', Matrix.isSymm_diagonal _, fun i => ?_⟩
    obtain ⟨k, hk⟩ := hall i
    rw [Matrix.mulVec_diagonal, Matrix.diagonal_apply_eq, hk]
    exact ⟨n' i * k, by ring⟩
  · obtain ⟨p, hp⟩ := not_forall.mp hall
    obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hp
    obtain ⟨m, hm⟩ := h
    refine ⟨Matrix.of fun i j => (if i = p then n' j else 0) + (if j = p then n' i else 0),
      ?_, fun i => ?_⟩
    · ext i j
      simp only [Matrix.transpose_apply, Matrix.of_apply]
      ring
    · have hm' : ∑ j, n' j * n j = m + m := by
        rw [← hm]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      have h2 : ∑ j, (if j = p then n' i else 0) * n j = n' i * n p := by
        simp
      by_cases hi : i = p
      · subst hi
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
          if_true, hm', h2, hk]
        exact ⟨m + n' i * k + n' i, by ring⟩
      · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
          if_neg hi, h2, hk, zero_mul, Finset.sum_const_zero]
        exact ⟨n' i * k, by ring⟩
end GlobalTheory
