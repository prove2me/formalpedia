-- Prove2me | solution 1 for GlobalTheory.LatOrb.matLat_adj_mul_eq_of_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:53:20.342801+00:00
-- url     : https://prove2.me/submissions/3441b5e7-59c3-4da6-b0a8-f6e8767b923e

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixImageAdjointMulEqOfSelfDualLattices
import Theorems.Thm_GlobalTheory_LatOrb_herm_mulVec_eq_adj
import Theorems.Thm_GlobalTheory_LatOrb_mem_matLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.LatOrb
namespace GlobalTheory.LatOrb
theorem _root_.solution : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K),
    (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (x : Matrix (Fin n) (Fin n) K), IsUnit x →
    ∀ M : Submodule O (Fin n → K), SelfDual O σ M → SelfDual O σ (matLat O x M) →
    matLat O ((x.map σ)ᵀ * x) M = M := by
  intro O K _ _ _ σ _ n x hx M hM hxM

  have key : ∀ y, y ∈ matLat O x M ↔ (x.map σ)ᵀ *ᵥ y ∈ M := by
    intro y
    rw [hxM y, hM ((x.map σ)ᵀ *ᵥ y)]
    constructor
    · intro h m hm
      rw [← herm_mulVec_eq_adj]
      exact h _ ((mem_matLat x M _).2 ⟨m, hm, rfl⟩)
    · intro h w hw
      obtain ⟨m, hm, rfl⟩ := (mem_matLat x M w).1 hw
      rw [herm_mulVec_eq_adj]
      exact h m hm
  have hdet : IsUnit ((x.map σ)ᵀ * x).det := by
    have e : (x.map σ).det = σ x.det := (RingHom.map_det σ x).symm
    rw [Matrix.det_mul, Matrix.det_transpose, e]
    refine IsUnit.mul ?_ ((Matrix.isUnit_iff_isUnit_det x).1 hx)
    have h0 : x.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det x).1 hx).ne_zero
    exact isUnit_iff_ne_zero.2 ((map_ne_zero σ).2 h0)
  ext u
  rw [mem_matLat]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [← Matrix.mulVec_mulVec]
    exact (key _).1 ((mem_matLat x M _).2 ⟨m, hm, rfl⟩)
  · intro hu
    set A := (x.map σ)ᵀ * x with hA
    refine ⟨A⁻¹ *ᵥ u, ?_, ?_⟩
    · have h1 : (x.map σ)ᵀ *ᵥ (x *ᵥ (A⁻¹ *ᵥ u)) ∈ M := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hA,
          Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
        exact hu
      obtain ⟨m', hm', hxm'⟩ := (mem_matLat x M _).1 ((key _).2 h1)
      have : m' = A⁻¹ *ᵥ u := by
        have hx' : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det x).1 hx
        have := congrArg (fun v => x⁻¹ *ᵥ v) hxm'
        simpa [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul x hx'] using this
      exact this ▸ hm'
    · rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
end GlobalTheory.LatOrb
