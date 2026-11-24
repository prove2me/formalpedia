-- Prove2me | solution 1 for GlobalTheory.bijective_toSpanSingleton_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:24:41.632944+00:00
-- url     : https://prove2.me/submissions/98795331-cb36-4485-b83d-6313c324f0f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_dual_apply_smul_comm

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
variable {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution [Module.Invertible A M] (f : Module.Dual A M)
    (e : M) {A' M' : Type*} [CommRing A'] [Algebra A A'] [AddCommGroup M'] [Module A M']
    [Module A' M'] [IsScalarTower A A' M'] (l : M →ₗ[A] M') (hl : IsBaseChange A' l)
    (hu : IsUnit (algebraMap A A' (f e))) :
    Function.Bijective (LinearMap.toSpanSingleton A' M' (l e)) := by
  haveI : Module.Invertible A' M' := .congr hl.equiv
  refine Module.Invertible.bijective_of_surjective fun y ↦ ?_
  induction y using hl.inductionOn with
  | zero => exact ⟨0, map_zero _⟩
  | tmul m =>
    obtain ⟨u, hu⟩ := hu
    refine ⟨↑u⁻¹ * algebraMap A A' (f m), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, mul_smul, algebraMap_smul, ← map_smul,
      dual_apply_smul_comm, map_smul, ← algebraMap_smul A' (f e), ← hu, smul_smul, Units.inv_mul,
      one_smul]
  | smul s n hn =>
    obtain ⟨a, rfl⟩ := hn
    exact ⟨s • a, map_smul _ _ _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
end GlobalTheory
