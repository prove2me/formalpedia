-- Prove2me | solution 1 for GlobalTheory.finite_sq_eq_one_of_finite_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:33:54.61603+00:00
-- url     : https://prove2.me/submissions/3f8f80bb-a375-4f70-a89e-b8541de7e94a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSqEqOneOfFiniteAlgebra

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
theorem _root_.solution (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A]
    [Algebra k A] [Module.Finite k A] : Set.Finite {x : A | x ^ 2 = 1} := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : Finite (TopologicalSpace.Clopens (PrimeSpectrum A)) :=
    Finite.of_injective (fun s : TopologicalSpace.Clopens (PrimeSpectrum A) => (s : Set (PrimeSpectrum A)))
      SetLike.coe_injective
  haveI : Finite {e : A // IsIdempotentElem e} :=
    Finite.of_equiv _ (PrimeSpectrum.isIdempotentElemEquivClopens (R := A)).symm.toEquiv
  set c : A := algebraMap k A (2⁻¹ : k) with hc
  have hc2 : c * 2 = 1 := by
    rw [hc, (map_ofNat (algebraMap k A) 2).symm, ← map_mul,
      inv_mul_cancel₀ (two_ne_zero : (2 : k) ≠ 0), map_one]
  have hmap : ∀ x : A, x ^ 2 = 1 → IsIdempotentElem (c * (1 + x)) := by
    intro x hx
    unfold IsIdempotentElem
    have : (c * (1 + x)) * (c * (1 + x)) = c * (c * 2) * (1 + x) := by
      linear_combination (c * c) * hx
    rw [this, hc2, mul_one]
  have hinj : Set.InjOn (fun x : A => c * (1 + x)) {x : A | x ^ 2 = 1} := by
    intro x _ y _ hxy
    have h : (2 : A) * (c * (1 + x)) = 2 * (c * (1 + y)) := by simp only at hxy; rw [hxy]
    have e : ∀ z : A, (2 : A) * (c * (1 + z)) = 1 + z := fun z => by
      rw [← mul_assoc, mul_comm (2 : A) c, hc2, one_mul]
    rw [e, e] at h
    exact add_left_cancel h
  have hfin : Set.Finite {e : A | IsIdempotentElem e} :=
    Set.finite_coe_iff.mp (‹Finite {e : A // IsIdempotentElem e}› :)
  exact Set.Finite.of_finite_image (hfin.subset (by
    rintro _ ⟨x, hx, rfl⟩; exact hmap x hx)) hinj
end GlobalTheory
