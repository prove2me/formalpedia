-- Prove2me | solution 1 for GlobalTheory.WittMapUniq.exists_pow_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:59.54294+00:00
-- url     : https://prove2.me/submissions/1005fcbe-3fd8-4895-9bed-b16a468c9dce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorRingHomEqMapOfCoeffZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory GlobalTheory.WittMapUniq
open WittVector
namespace GlobalTheory.WittMapUniq
theorem _root_.solution (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l]
    [PerfectRing R l] : ∀ (n : ℕ) (r : R), ∃ s : R, s ^ l ^ n = r := by
  intro n
  induction n with
  | zero => intro r; exact ⟨r, by simp⟩
  | succ n ih =>
    intro r
    obtain ⟨t, ht⟩ := surjective_frobenius R l r
    obtain ⟨s, hs⟩ := ih t
    refine ⟨s, ?_⟩
    rw [pow_succ, pow_mul, hs, ← ht, frobenius_def]
end GlobalTheory.WittMapUniq
