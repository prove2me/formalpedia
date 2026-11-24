-- Prove2me | solution 1 for GlobalTheory.PerfectCompletion.dvd_of_pow_dvd_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:21:22.159538+00:00
-- url     : https://prove2.me/submissions/90801f4a-2c77-4dd9-8018-59564640f38c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfect
import Theorems.Thm_GlobalTheory_PerfectCompletion_pow_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PerfectCompletion
variable (l : ℕ) [Fact l.Prime] {V : Type} [CommRing V] [CharP V l] [PerfectRing V l]
namespace GlobalTheory.PerfectCompletion
theorem _root_.solution (x s : V) (n : ℕ) (h : x ^ (l * n) ∣ s ^ l) : x ^ n ∣ s := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(frobeniusEquiv V l).symm c, (frobeniusEquiv V l).injective ?_⟩
  rw [frobeniusEquiv_apply, frobeniusEquiv_apply, frobenius_def, frobenius_def, hc, mul_pow,
    pow_root, ← pow_mul, mul_comm n l]
end GlobalTheory.PerfectCompletion
