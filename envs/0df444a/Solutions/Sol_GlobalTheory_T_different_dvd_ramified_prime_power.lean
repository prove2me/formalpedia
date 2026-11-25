-- Prove2me | solution 1 for GlobalTheory.T.different_dvd_ramified_prime_power
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:09.760826+00:00
-- url     : https://prove2.me/submissions/59fdd0bb-11aa-4de8-9b93-f2ff365832af

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DifferentDvdRamifiedPrimePower
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DifferentDvdRamifiedPrimePowerStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Glob_differentIdeal_dvd_span_pow


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (t : ℕ), t ≠ 0 → (∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (t : 𝓞 E) ∈ P) → differentIdeal ℤ (𝓞 E) ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
  first | exact @GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow | exact GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow | (intros; apply GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow <;> assumption)
end _root_.GlobalTheory.T
