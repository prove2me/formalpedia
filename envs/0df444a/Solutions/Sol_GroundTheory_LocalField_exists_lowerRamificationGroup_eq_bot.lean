-- Prove2me | solution 1 for GroundTheory.LocalField.exists_lowerRamificationGroup_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:30:39.336448+00:00
-- url     : https://prove2.me/submissions/91a2fc11-ea12-4120-bdd5-5d6a7cc06429

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Theorems.Thm_GroundTheory_LocalField_algEquiv_eq_one_of_forall_integer
import Theorems.Thm_GroundTheory_LocalField_mem_lowerRamificationGroup_natCast_iff
import Theorems.Thm_GroundTheory_LocalField_lowerRamificationGroup_antitone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
variable (K L)
variable {K L}
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution :
    ∃ n : ℕ, ∀ i : ℤ, n ≤ i → lowerRamificationGroup K L i = ⊥ := by
  have key : ∀ σ : L ≃ₐ[K] L, ∃ m : ℕ, σ ≠ 1 → σ ∉ lowerRamificationGroup K L m := by
    intro σ
    by_cases hσ : σ = 1
    · exact ⟨0, fun h ↦ (h hσ).elim⟩
    obtain ⟨x, hx⟩ : ∃ x : 𝒪[L], integerAlgEquiv K L σ x ≠ x := by
      by_contra! h
      exact hσ (algEquiv_eq_one_of_forall_integer h)
    have hd : integerAlgEquiv K L σ x - x ≠ 0 := sub_ne_zero.mpr hx
    have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing (𝓂[L]) (Ideal.IsPrime.ne_top')
    obtain ⟨m, hm⟩ : ∃ m : ℕ, integerAlgEquiv K L σ x - x ∉ 𝓂[L] ^ m := by
      by_contra! h
      exact hd (by
        have : integerAlgEquiv K L σ x - x ∈ ⨅ m : ℕ, 𝓂[L] ^ m := Submodule.mem_iInf _ |>.mpr h
        rwa [hinf, Ideal.mem_bot] at this)
    refine ⟨m, fun _ hmem ↦ hm ?_⟩
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (mem_lowerRamificationGroup_natCast_iff.mp hmem x)
  choose f hf using key
  obtain ⟨N, hN⟩ := Finite.exists_le f
  refine ⟨N, fun i hi ↦ eq_bot_iff.mpr fun σ hσ ↦ ?_⟩
  by_contra h
  exact hf σ h (lowerRamificationGroup_antitone K L (by have := hN σ; omega) hσ)
end GroundTheory.LocalField
