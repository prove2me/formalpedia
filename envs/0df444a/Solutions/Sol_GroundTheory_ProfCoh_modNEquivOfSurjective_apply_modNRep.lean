-- Prove2me | solution 1 for GroundTheory.ProfCoh.modNEquivOfSurjective_apply_modNRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:34:18.520798+00:00
-- url     : https://prove2.me/submissions/cae232fe-323b-4b5f-a33d-abfa95b6b7de

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_GroundTheory_ProfCoh_modNEquivOfSurjective_mk
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable {n : ℕ} {A X : Type*} [AddCommGroup A] [AddCommGroup X] [Module (ZMod n) X]
namespace GroundTheory.ProfCoh
theorem _root_.solution {Γ : Type*} [Group Γ] [DistribMulAction Γ A]
    (ρ : Representation (ZMod n) Γ X) (φ : A →+ X) (hs : Function.Surjective φ)
    (hker : ∀ a, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ A n))
    (hφ : ∀ (γ : Γ) (a : A), φ (γ • a) = ρ γ (φ a)) (γ : Γ) (x : ModN A n) :
    modNEquivOfSurjective φ hs hker (modNRep Γ A n γ x) =
      ρ γ (modNEquivOfSurjective φ hs hker x) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [modNRep_mk, modNEquivOfSurjective_mk, modNEquivOfSurjective_mk]
  exact hφ γ a
end GroundTheory.ProfCoh
