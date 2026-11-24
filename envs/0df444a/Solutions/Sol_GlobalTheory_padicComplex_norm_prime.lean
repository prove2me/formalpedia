-- Prove2me | solution 1 for GlobalTheory.padicComplex_norm_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:14.704811+00:00
-- url     : https://prove2.me/submissions/009a1c02-425d-42d2-9f4e-f2a188a646b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LiftHasSumZeroOfSurjectiveModPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
    ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)),
    PadicAlgCl.norm_extends, Padic.norm_p]
end GlobalTheory
