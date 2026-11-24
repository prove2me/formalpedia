-- Prove2me | solution 1 for GlobalTheory.TriangularDiagonal.mul_diag_of_triangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:39:10.062868+00:00
-- url     : https://prove2.me/submissions/f32a098f-1ab3-4bea-80dc-e207ae5ee13a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TriangularDiagonal
namespace GlobalTheory.TriangularDiagonal
theorem _root_.solution :
    ∀ {p : ℕ} {κ : Fin p → ℤ}, Function.Injective κ → ∀ {M N : Matrix (Fin p) (Fin p) ℂ},
      (∀ (a b : Fin p), κ a < κ b → M a b = (0 : ℂ)) →
      (∀ (a b : Fin p), κ a < κ b → N a b = (0 : ℂ)) →
      ∀ (i : Fin p), (M * N) i i = M i i * N i i := by
  intro p κ hκ M N hM hN i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hk
    rcases lt_trichotomy (κ i) (κ k) with h | h | h
    · rw [hM i k h, zero_mul]
    · exact absurd (hκ h).symm hk
    · rw [hN k i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h
end GlobalTheory.TriangularDiagonal
