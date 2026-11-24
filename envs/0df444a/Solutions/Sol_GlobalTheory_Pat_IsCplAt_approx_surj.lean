-- Prove2me | solution 1 for GlobalTheory.Pat.IsCplAt.approx_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:37:39.492356+00:00
-- url     : https://prove2.me/submissions/df550af5-cfac-4c75-a4bd-b58bde5a8aff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCplAtApprox
import Theorems.Thm_GlobalTheory_Pat_IsCplAt_approx_step

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
    [hq : q.IsPrime] {φ : R →+* S} (h : IsCplAt q φ) (k : ℕ) (s : S) :
    ∃ a b : R, b ∉ q ∧ φ b * s - φ a ∈ maximalIdeal S ^ k := by
  induction k with
  | zero => exact ⟨0, 1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simp⟩
  | succ k ih =>
    obtain ⟨a, b, hb, hab⟩ := ih
    obtain ⟨a', b', hb', hab'⟩ := h.approx_step k _ hab 1
    refine ⟨b' * a + a', b * b', fun hh => (hq.mem_or_mem hh).elim hb hb', ?_⟩
    have : φ (b * b') * s - φ (b' * a + a') = φ b' * (1 * (φ b * s - φ a)) - φ a' := by
      simp only [map_mul, map_add]; ring
    rw [this]
    exact hab'
end IsCplAt
end GlobalTheory.Pat
