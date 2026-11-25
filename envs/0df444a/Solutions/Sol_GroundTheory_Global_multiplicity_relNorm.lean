-- Prove2me | solution 1 for GroundTheory.Global.multiplicity_relNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:14.137311+00:00
-- url     : https://prove2.me/submissions/3fa44834-2286-4fb5-b0b8-98d2140865c6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Theorems.Thm_GroundTheory_Global_prime_asIdeal
import Theorems.Thm_GroundTheory_Global_emultiplicity_relNorm

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
variable (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global
theorem _root_.solution (I : Ideal (𝓞 M)) (hI : I ≠ ⊥) :
    multiplicity v.asIdeal (Ideal.relNorm (𝓞 K) I) =
      ∑ w : SemiLocal.PlacesOver M v,
        w.1.asIdeal.inertiaDeg (𝓞 K) * multiplicity w.1.asIdeal I := by
  have h := emultiplicity_relNorm v I hI
  rw [(FiniteMultiplicity.of_prime_left (prime_asIdeal v)
    ((Ideal.relNorm_eq_bot_iff (R := 𝓞 K)).not.2 hI)).emultiplicity_eq_multiplicity] at h
  simp only [fun w : SemiLocal.PlacesOver M v ↦
    (FiniteMultiplicity.of_prime_left (prime_asIdeal w.1) hI).emultiplicity_eq_multiplicity] at h
  exact_mod_cast h
end GroundTheory.Global
