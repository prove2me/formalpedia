-- Prove2me | solution 1 for GlobalTheory.exists_common_nat_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:39:07.675383+00:00
-- url     : https://prove2.me/submissions/a70be2ac-30ce-4e2e-b748-92da00009d8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ConeClosureArcOfIntegralImageReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R F α : Type*} [CommRing R] [CommRing F] (φ : R →+* F)
    (h : ∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ r = n * x) (g : α → F) (S : Finset α) :
    ∃ n : ℕ, 0 < n ∧ ∀ s ∈ S, ∃ r : R, φ r = n * g s := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S ha ih =>
    obtain ⟨n, hn, hS⟩ := ih
    obtain ⟨r, m, hm, hr⟩ := h (g a)
    refine ⟨n * m, Nat.mul_pos hn hm, fun s hs => ?_⟩
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact ⟨n * r, by rw [map_mul, map_natCast, hr]; push_cast; ring⟩
    · obtain ⟨r', hr'⟩ := hS s hs
      exact ⟨m * r', by rw [map_mul, map_natCast, hr']; push_cast; ring⟩
end GlobalTheory
