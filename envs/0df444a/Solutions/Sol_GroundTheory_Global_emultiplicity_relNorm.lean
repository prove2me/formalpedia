-- Prove2me | solution 1 for GroundTheory.Global.emultiplicity_relNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:37.909241+00:00
-- url     : https://prove2.me/submissions/7d03ce40-de05-480a-b016-4e63b1c53419

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Theorems.Thm_GroundTheory_Global_prime_asIdeal
import Theorems.Thm_GroundTheory_Global_emultiplicity_relNorm_of_prime

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
    emultiplicity v.asIdeal (Ideal.relNorm (𝓞 K) I) =
      ∑ w : SemiLocal.PlacesOver M v,
        (w.1.asIdeal.inertiaDeg (𝓞 K) : ℕ∞) * emultiplicity w.1.asIdeal I := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.1 hx, Ideal.relNorm_top, ← Ideal.one_eq_top,
      emultiplicity_of_one_right (prime_asIdeal v).not_isUnit]
    symm
    apply Finset.sum_eq_zero
    intro w _
    rw [← Ideal.one_eq_top, emultiplicity_of_one_right (prime_asIdeal w.1).not_isUnit, mul_zero]
  | h₃ a p ha hp ih =>
    rw [map_mul, emultiplicity_mul (prime_asIdeal v), ih ha,
      emultiplicity_relNorm_of_prime v p hp, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    rw [emultiplicity_mul (prime_asIdeal w.1), mul_add]
end GroundTheory.Global
