-- Prove2me | solution 1 for GlobalTheory.trace_matrix_pi_operator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:56:29.640804+00:00
-- url     : https://prove2.me/submissions/47faa509-4f78-4503-9cc0-682c3d110f5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TraceMatrixPiOperator

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
theorem _root_.solution : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (m : ℕ)
    (h : Matrix (Fin m) (Fin m) ℂ) (A : W →ₗ[ℂ] W),
    LinearMap.trace ℂ (Fin m → W) (∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ : Fin m => W) k ∘ₗ A ∘ₗ
      LinearMap.proj j)) = h.trace * LinearMap.trace ℂ W A := by
  intro W _ _ _ m h A
  have key : ∀ k j : Fin m, LinearMap.trace ℂ (Fin m → W)
      (LinearMap.single ℂ (fun _ : Fin m => W) k ∘ₗ A ∘ₗ LinearMap.proj j)
      = if k = j then LinearMap.trace ℂ W A else 0 := by
    intro k j
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
    by_cases hkj : k = j
    · subst hkj
      rw [LinearMap.proj_comp_single_same, LinearMap.comp_id, if_pos rfl]
    · rw [LinearMap.proj_comp_single_ne (R := ℂ) (φ := fun _ : Fin m => W) j k (Ne.symm hkj), LinearMap.comp_zero, map_zero, if_neg hkj]
  simp only [map_sum, map_smul, key, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.sum_mul]
end GlobalTheory
