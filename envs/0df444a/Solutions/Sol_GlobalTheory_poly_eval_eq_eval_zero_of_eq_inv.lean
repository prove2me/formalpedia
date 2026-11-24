-- Prove2me | solution 1 for GlobalTheory.poly_eval_eq_eval_zero_of_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:06.062368+00:00
-- url     : https://prove2.me/submissions/05c80def-e070-4042-b89e-a55e05d6ba20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k : Type} [Field k] [Infinite k] (p q : k[X]) (c : k)
    (h : ∀ x : k, x ≠ 0 → p.eval x = c * q.eval x⁻¹) : ∀ x : k, p.eval x = p.eval 0 := by
  set N := q.natDegree
  have key : X ^ N * p = C c * reflect N q := by
    apply eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := ({0}ᶜ : Set k))
    · intro x hx
      have hx0 : x ≠ 0 := hx
      letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx0)
      have hr := eval₂_reflect_mul_pow (RingHom.id k) x⁻¹ N q le_rfl
      rw [invOf_eq_inv, inv_inv] at hr
      simp only [Set.mem_setOf_eq, eval_mul, eval_pow, eval_X, eval_C, h x hx0]
      rw [← eval₂_id, ← eval₂_id, ← hr, inv_pow]
      field_simp
    · exact (Set.finite_singleton (0 : k)).infinite_compl
  by_cases hp : p = 0
  · intro x; simp [hp]
  have hdeg : (X ^ N * p).natDegree = N + p.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hp, natDegree_X_pow]
  have hle : (C c * reflect N q).natDegree ≤ N :=
    (natDegree_C_mul_le _ _).trans (natDegree_reflect_le.trans (by simp [N]))
  rw [key] at hdeg
  have h0 : p.natDegree = 0 := by omega
  intro x
  rw [eq_C_of_natDegree_eq_zero h0]
  simp
end GlobalTheory
