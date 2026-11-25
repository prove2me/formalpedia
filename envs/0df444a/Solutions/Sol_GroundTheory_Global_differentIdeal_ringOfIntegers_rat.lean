-- Prove2me | solution 1 for GroundTheory.Global.differentIdeal_ringOfIntegers_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:50.148318+00:00
-- url     : https://prove2.me/submissions/1a5cff25-c3fe-46f6-94e4-1fe31fd5b251

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant

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
variable (M : Type*) [Field M] [NumberField M]
namespace GroundTheory.Global
theorem _root_.solution :
    differentIdeal (𝓞 ℚ) (𝓞 M) = differentIdeal ℤ (𝓞 M) := by
  have h1 : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
    rw [← Ideal.absNorm_eq_one_iff, absNorm_differentIdeal ℚ, Rat.numberField_discr]
    rfl
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 ℚ) (𝓞 M), h1, Ideal.map_top,
    Ideal.mul_top]
end GroundTheory.Global
