-- Prove2me | solution 1 for GroundTheory.Global.emultiplicity_asIdeal_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:51.729885+00:00
-- url     : https://prove2.me/submissions/8b6ab49c-4aac-4237-b856-4971e6bcf336

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Theorems.Thm_GroundTheory_Global_prime_asIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain NumberField Module
open GroundTheory GroundTheory.Global
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
namespace GroundTheory.Global
theorem _root_.solution {F : Type*} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) (p : Ideal (𝓞 F)) [hp : p.IsMaximal] :
    emultiplicity u.asIdeal p = if u.asIdeal = p then 1 else 0 := by
  split_ifs with h
  · have h1 := emultiplicity_pow_self_of_prime (prime_asIdeal u) 1
    rw [pow_one] at h1
    rw [← h, h1]
    rfl
  · rw [emultiplicity_eq_zero, Ideal.dvd_iff_le]
    intro hle
    exact h (hp.eq_of_le u.isPrime.ne_top hle).symm
end GroundTheory.Global
