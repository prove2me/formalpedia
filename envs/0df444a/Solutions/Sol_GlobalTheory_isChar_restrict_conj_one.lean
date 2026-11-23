-- Prove2me | solution 1 for GlobalTheory.isChar_restrict_conj_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:24.821161+00:00
-- url     : https://prove2.me/submissions/5a4be44e-fac6-4b9f-89cd-58b0ec52e21e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (χ : G → L), IsChar K L χ → (∀ (H : Type) [Group H] (f : H →* G), IsChar K L (fun h => χ (f h))) ∧ (∀ g x : G, χ (x⁻¹ * g * x) = χ g) ∧ ∃ n : ℕ, χ 1 = (n : L) ∧ (n = 0 → χ = 0) := by
  intro K L _ _ _ G _ χ hχ
  obtain ⟨n, ρ, hρ⟩ := hχ
  refine ⟨?_, ?_, n, ?_, ?_⟩
  · intro H _ f
    exact ⟨n, ρ.comp f, fun h => hρ (f h)⟩
  · intro g x
    rw [hρ, hρ]
    have hc := ρ.char_conj g x⁻¹
    rw [inv_inv] at hc
    rw [hc]
  · rw [hρ, Representation.char_one]
    simp
  · rintro rfl
    funext g
    have hz : ρ g = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hρ, Pi.zero_apply, Representation.character, hz, map_zero, map_zero]
end GlobalTheory
