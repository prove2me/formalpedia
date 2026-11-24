-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.mem_map_of_mul_mem_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:38:51.243321+00:00
-- url     : https://prove2.me/submissions/2879dc27-826c-406f-a5ae-842f9965cd24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_of_tmul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
namespace GlobalTheory.ProperFunctions
theorem _root_.solution {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (hφ : φ.Flat) (I J : Ideal R) (a : R) (hJ : ∀ r : R, r * a ∈ I → r ∈ J) (x : A)
    (h : φ a * x ∈ I.map φ) : x ∈ J.map φ := by
  algebraize [φ]
  refine mem_map_of_tmul_eq_zero x (Ideal.Quotient.mk I a) J (fun r hr ↦ hJ r ?_) ?_
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact hr
  · have h1 : ∀ y ∈ I.map φ, ∀ z : A, (z * y) ⊗ₜ[R] (1 : R ⧸ I) = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨r, hr, rfl⟩ := hy
        intro z
        have : z * φ r = r • z := by rw [mul_comm]; rfl
        rw [this, TensorProduct.smul_tmul]
        have : r • (1 : R ⧸ I) = 0 := by
          rw [← Algebra.algebraMap_eq_smul_one]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
        simp [this]
      | zero => simp
      | add y y' _ _ hy hy' => intro z; rw [mul_add, TensorProduct.add_tmul, hy, hy', add_zero]
      | smul c y _ hy => intro z; rw [smul_eq_mul, ← mul_assoc, hy]
    have h2 := h1 _ h 1
    have h3 : (1 : A) * (φ a * x) = a • x := by rw [one_mul]; rfl
    rw [h3, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one] at h2
    exact h2
end GlobalTheory.ProperFunctions
