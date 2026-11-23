-- Prove2me | solution 1 for GroundTheory.Automorphic.eq_of_permGL_mem_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:11.897801+00:00
-- url     : https://prove2.me/submissions/bc8ce0ce-4e45-492b-9a09-3e8df7392a8f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Theorems.Thm_GroundTheory_Automorphic_mem_borel_iff
import Theorems.Thm_GroundTheory_Automorphic_mul_permGL_apply
import Theorems.Thm_GroundTheory_Automorphic_permGL_mul_apply
import Theorems.Thm_GroundTheory_Automorphic_borel_diag_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_perm_eq_one_of_forall_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset
variable {n : ℕ} {k : Type*} [Field k]
namespace GroundTheory.Automorphic
theorem _root_.solution {σ τ : Equiv.Perm (Fin n)}
    (h : permGL k τ ∈ doubleCoset (permGL k σ) (borel n k) (borel n k)) : σ = τ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_doubleCoset.mp h
  have hy' : y⁻¹ ∈ borel n k := (borel n k).inv_mem hy
  have hmat : (x : Matrix (Fin n) (Fin n) k) * (permGL k σ : Matrix (Fin n) (Fin n) k) =
      (permGL k τ : Matrix (Fin n) (Fin n) k) * ((y⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [← Units.val_mul, ← Units.val_mul, hxy]
    congr 1
    group
  have hle : ∀ a, τ a ≤ σ a := by
    intro a
    have hent := congrFun (congrFun hmat (τ a)) a
    rw [mul_permGL_apply, permGL_mul_apply] at hent
    by_contra hlt
    push Not at hlt
    have h0 := (mem_borel_iff x).mp hx (τ a) (σ a) hlt
    rw [hent, show τ⁻¹ (τ a) = a from τ.symm_apply_apply a] at h0
    exact borel_diag_ne_zero hy' a h0
  have hπ := perm_eq_one_of_forall_le (τ * σ⁻¹) (fun x => by
    simpa using hle (σ⁻¹ x))
  have := congrArg (· * σ) hπ
  simpa using this.symm
end GroundTheory.Automorphic
