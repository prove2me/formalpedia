-- Prove2me | solution 1 for GlobalTheory.powGr.toQuot_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:49.03912+00:00
-- url     : https://prove2.me/submissions/8487cbec-f143-4dc1-af83-430404777d18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R]
open GlobalTheory.powGr
variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (a : ℕ)
namespace GlobalTheory.powGr
theorem _root_.solution : Function.Injective (toQuot I M a) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := mk_surjective I M a x
  rwa [toQuot_mk, Submodule.Quotient.mk_eq_zero, ← mk_eq_zero] at hx
end GlobalTheory.powGr
