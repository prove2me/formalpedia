-- Prove2me | solution 1 for GlobalTheory.T.prime_power_not_dvd_different
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:51:39.103171+00:00
-- url     : https://prove2.me/submissions/f91f1954-a9b4-43e8-a452-7fa2fa64a1ce

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimePowerNotDvdDifferent
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimePowerNotDvdDifferentStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Glob_not_pow_dvd_different


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (P J : Ideal (𝓞 E)) [P.IsPrime] (p k : ℕ), p.Prime → (p : 𝓞 E) ∈ P → ¬ P ∣ J → Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} = P ^ k * J → ¬ P ^ k ∣ differentIdeal ℤ (𝓞 E) := by
  first | exact @GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different | exact GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different | (intros; apply GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different <;> assumption)
end _root_.GlobalTheory.T
