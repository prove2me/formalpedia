-- Prove2me | solution 1 for GlobalTheory.QuadraticEtale.isIntegral_of_involution
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:21.943578+00:00
-- url     : https://prove2.me/submissions/2bd9f674-335a-4282-b494-2925ec3b728b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsUnitFormSelfOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.QuadraticEtale
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (σ : S →+* S)
namespace GlobalTheory.QuadraticEtale
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → x ∈ (algebraMap R S).range) : Algebra.IsIntegral R S := by
  refine ⟨fun x => ?_⟩
  obtain ⟨t, ht⟩ := hfix (x + σ x) (by rw [map_add, hσ, add_comm])
  obtain ⟨n, hn⟩ := hfix (x * σ x) (by rw [map_mul, hσ, mul_comm])
  refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, ht, hn]
    ring
end GlobalTheory.QuadraticEtale
