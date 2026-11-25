-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.mem_laurentSubalgebra_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:56:58.061859+00:00
-- url     : https://prove2.me/submissions/41d548a2-9a04-4ea2-9fb2-2b8bdf79fbf4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLaurentIdeal
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_X_inv_mem_laurentSubalgebra
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_algebraMap_mem_laurentSubalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Polynomial
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution {R : RatFunc ℂ} :
    R ∈ laurentSubalgebra ↔
      ∃ (P : ℂ[X]) (k : ℕ), R = algebraMap ℂ[X] (RatFunc ℂ) P / RatFunc.X ^ k := by
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  constructor
  · intro hR
    induction hR using Algebra.adjoin_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨Polynomial.X, 0, by simp [RatFunc.algebraMap_X]⟩
      · exact ⟨1, 1, by simp⟩
    | algebraMap r =>
      exact ⟨Polynomial.C r, 0, by simp [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]⟩
    | add x y _ _ hx hy =>
      obtain ⟨P, k, rfl⟩ := hx
      obtain ⟨Q, l, rfl⟩ := hy
      refine ⟨P * Polynomial.X ^ l + Q * Polynomial.X ^ k, k + l, ?_⟩
      rw [map_add, map_mul, map_mul, map_pow, map_pow, RatFunc.algebraMap_X]
      field_simp
      ring
    | mul x y _ _ hx hy =>
      obtain ⟨P, k, rfl⟩ := hx
      obtain ⟨Q, l, rfl⟩ := hy
      refine ⟨P * Q, k + l, ?_⟩
      rw [map_mul, pow_add]
      field_simp
  · rintro ⟨P, k, rfl⟩
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (algebraMap_mem_laurentSubalgebra P) (pow_mem X_inv_mem_laurentSubalgebra k)
end GroundTheory.Automorphic.GodementJacquet
