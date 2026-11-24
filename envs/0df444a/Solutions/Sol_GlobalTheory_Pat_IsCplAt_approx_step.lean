-- Prove2me | solution 1 for GlobalTheory.Pat.IsCplAt.approx_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:19:55.598805+00:00
-- url     : https://prove2.me/submissions/7290622f-5584-4891-a87e-9f5b9acb19e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCplAtApprox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Pat
namespace GlobalTheory.Pat
namespace IsCplAt
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] [IsLocalRing S] {q : Ideal R}
    [hq : q.IsPrime] {φ : R →+* S} (h : IsCplAt q φ) (k : ℕ) (t : S) (ht : t ∈ maximalIdeal S ^ k) :
    ∀ c : S, ∃ a b : R, b ∉ q ∧ φ b * (c * t) - φ a ∈ maximalIdeal S ^ (k + 1) := by
  have e : maximalIdeal S ^ k = (q ^ k).map φ := by rw [h.max_eq, Ideal.map_pow]
  rw [e, Ideal.map] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    intro c
    obtain ⟨a, b, hb, hab⟩ := h.res c
    refine ⟨a * x, b, hb, ?_⟩
    have : φ b * (c * φ x) - φ (a * x) = φ x * (φ b * c - φ a) := by rw [map_mul]; ring
    rw [this, pow_succ]
    exact Ideal.mul_mem_mul (e ▸ Ideal.mem_map_of_mem φ hx) hab
  | zero =>
    intro c
    exact ⟨0, 1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simp⟩
  | add x y _ _ hx hy =>
    intro c
    obtain ⟨a, b, hb, hab⟩ := hx c
    obtain ⟨a', b', hb', hab'⟩ := hy c
    refine ⟨b' * a + b * a', b * b', fun hh => (hq.mem_or_mem hh).elim hb hb', ?_⟩
    have : φ (b * b') * (c * (x + y)) - φ (b' * a + b * a')
        = φ b' * (φ b * (c * x) - φ a) + φ b * (φ b' * (c * y) - φ a') := by
      simp only [map_mul, map_add]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hab) (Ideal.mul_mem_left _ _ hab')
  | smul r x _ hx =>
    intro c
    obtain ⟨a, b, hb, hab⟩ := hx (c * r)
    exact ⟨a, b, hb, by simpa [mul_assoc] using hab⟩
end IsCplAt
end GlobalTheory.Pat
