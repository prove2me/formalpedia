-- Prove2me | solution 1 for GlobalTheory.exists_unit_smul_eq_of_bijective_toSpanSingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:47:44.585013+00:00
-- url     : https://prove2.me/submissions/2a4ab0ac-16c2-44c4-a150-a02c236d14e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {A : Type*} [CommRing A]
namespace GlobalTheory
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module A M]
    {e e' : M} (he : Function.Bijective (LinearMap.toSpanSingleton A M e))
    (he' : Function.Bijective (LinearMap.toSpanSingleton A M e')) :
    ∃ u : Aˣ, e' = (u : A) • e := by
  obtain ⟨a, ha⟩ := he.2 e'
  obtain ⟨b, hb⟩ := he'.2 e
  simp only [LinearMap.toSpanSingleton_apply] at ha hb
  have : b * a = 1 := he.1 (by simp [mul_smul, ha, hb])
  exact ⟨Units.mkOfMulEqOne a b (by rw [mul_comm, this]), ha.symm⟩
end GlobalTheory
