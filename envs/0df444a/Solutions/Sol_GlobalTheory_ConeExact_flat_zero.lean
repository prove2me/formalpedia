-- Prove2me | solution 1 for GlobalTheory.ConeExact.flat_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:38.899042+00:00
-- url     : https://prove2.me/submissions/0b9d63e9-17c3-4234-bc81-7d6d381cd14a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
variable {R : Type u} [CommRing R] {K : ℕ → Type v} {C : ℕ → Type w} [∀ p, AddCommGroup (K p)]
  [∀ p, AddCommGroup (C p)] [∀ p, Module R (K p)] [∀ p, Module R (C p)]
variable {dK : ∀ p, K p →ₗ[R] K (p + 1)} {dC : ∀ p, C p →ₗ[R] C (p + 1)}
    {φ : ∀ p, K p →ₗ[R] C p}
namespace GlobalTheory
namespace ConeExact
theorem _root_.solution [∀ p, Module.Flat R (K (p + 1))] [∀ p, Module.Flat R (C p)]
    (h : ConeExact (fun p => dK p) (fun p => dC p) (fun p => φ p))
    (hK : ∀ p x, dK (p + 1) (dK p x) = 0) (hC : ∀ p x, dC (p + 1) (dC p x) = 0)
    (hφ : ∀ p x, dC p (φ p x) = φ (p + 1) (dK p x)) (n : ℕ)
    (hnK : ∀ p, n < p → Subsingleton (K p)) (hnC : ∀ p, n < p → Subsingleton (C p)) :
    Module.Flat R (K 0) := by
  obtain ⟨h0, h1, h2⟩ := (coneExact_iff hK hC hφ).1 h
  have := flat_range_coneD h2 n hnK hnC 0
  have : Module.Flat R (C 0 × K (0 + 1)) := flat_prod
  have := flat_range_of_exact h1
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofInjective _ h0)
end ConeExact
end GlobalTheory
