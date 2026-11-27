-- Prove2me | solution 1 for GlobalTheory.powGr.exact_toQuot_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:42:08.585972+00:00
-- url     : https://prove2.me/submissions/d982aa32-62cb-425e-8a23-1ea8ab1d0e7e

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
theorem _root_.solution :
    Function.Exact (toQuot I M a) (Submodule.factor (pow_succ_smul_le I M a)) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  constructor
  · intro h
    exact ⟨mk I M a ⟨y, (Submodule.Quotient.mk_eq_zero _).mp h⟩, rfl⟩
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := mk_surjective I M a x
    rw [← hx]
    exact (Submodule.Quotient.mk_eq_zero _).mpr x.2
end GlobalTheory.powGr
