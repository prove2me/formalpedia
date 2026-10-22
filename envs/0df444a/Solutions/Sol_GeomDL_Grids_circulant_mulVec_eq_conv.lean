-- Prove2me | solution 1 for GeomDL.Grids.circulant_mulVec_eq_conv
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T19:36:32.883154+00:00
-- url     : https://prove2.me/submissions/7c1e0012-c0ab-4311-8bfa-7b81f82db721

import Mathlib
import Definitions.Def_GeomDL_Grids_Defs

open GeomDL.Grids Matrix

theorem solution {R : Type*} [CommRing R] {n : ℕ} [NeZero n] :
    (∀ θ x : ZMod n → R, circulant θ *ᵥ x = conv x θ) ∧
      ∀ (x : ZMod n → R) (u : ZMod n), (shift R n *ᵥ x) u = x (u - 1) := by
  refine ⟨fun θ x => ?_, fun x u => ?_⟩
  · funext u
    simp only [mulVec, dotProduct, circulant_apply, conv]
    exact Finset.sum_congr rfl fun v _ => mul_comm _ _
  · simp only [mulVec, dotProduct, shift, circulant_apply, Pi.single_apply]
    have : ∀ v : ZMod n, (u - v = 1) ↔ (v = u - 1) := fun v => by
      constructor <;> intro h <;> [rw [← h]; rw [h]] <;> ring
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
