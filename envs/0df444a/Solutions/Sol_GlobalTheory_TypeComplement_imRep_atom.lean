-- Prove2me | solution 1 for GlobalTheory.TypeComplement.imRep_atom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:58:01.17817+00:00
-- url     : https://prove2.me/submissions/983232b7-3c36-4c08-b831-27fc68b9bb62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsComplementWithoutCommonIrreducibleTypes
import Theorems.Thm_GlobalTheory_TypeComplement_toSubmodule_bot
import Theorems.Thm_GlobalTheory_TypeComplement_ne_bot_iff_toSubmodule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TypeComplement
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}
namespace GlobalTheory.TypeComplement
theorem _root_.solution (f : V →ₗ[ℂ] V) (hf : ∀ k v, f (ρ k v) = ρ k (f v)) {S : Subrepresentation ρ}
    (hS : IsAtom S) (hne : ∃ s ∈ S.toSubmodule, f s ≠ 0) :
    IsAtom (imRep f hf S) ∧
      Nonempty (S.toRepresentation.Equiv (imRep f hf S).toRepresentation) := by
  obtain ⟨s₀, hs₀, hfs₀⟩ := hne

  have hinj : Function.Injective (f ∘ₗ S.toSubmodule.subtype) := by
    let Kr : Subrepresentation ρ := preRep f hf S ⊥
    have hK : Kr ≤ S := fun v hv => hv.1
    rcases hS.le_iff.mp hK with h | h
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      have hx' : (x : V) ∈ Kr.toSubmodule := by
        refine ⟨x.2, ?_⟩
        show f x ∈ (⊥ : Submodule ℂ V)
        simpa using hx
      rw [h] at hx'
      simp only [toSubmodule_bot, Submodule.mem_bot] at hx'
      simpa using Subtype.ext hx'
    · exfalso
      have : s₀ ∈ Kr.toSubmodule := by rw [h]; exact hs₀
      exact hfs₀ ((Submodule.mem_bot ℂ).mp (show f s₀ ∈ (⊥ : Submodule ℂ V) from this.2))
  refine ⟨⟨?_, fun C hC => ?_⟩, ?_⟩
  · rw [ne_bot_iff_toSubmodule]
    intro h
    have : f s₀ ∈ (imRep f hf S).toSubmodule := ⟨s₀, hs₀, rfl⟩
    rw [h] at this
    exact hfs₀ ((Submodule.mem_bot ℂ).mp this)
  · by_contra hC0
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (ne_bot_iff_toSubmodule.mp hC0)
    obtain ⟨s, hs, rfl⟩ : c ∈ (imRep f hf S).toSubmodule := hC.le hc
    have hB : preRep f hf S C ≤ S := fun v hv => hv.1
    rcases hS.le_iff.mp hB with h | h
    · have : s ∈ (preRep f hf S C).toSubmodule := ⟨hs, hc⟩
      rw [h] at this
      simp only [toSubmodule_bot, Submodule.mem_bot] at this
      exact hc0 (by simp [this])
    · have hle : imRep f hf S ≤ C := by
        rintro _ ⟨t, ht, rfl⟩
        have : t ∈ (preRep f hf S C).toSubmodule := by rw [h]; exact ht
        exact this.2
      exact lt_irrefl _ (lt_of_lt_of_le hC hle)
  · have hr : LinearMap.range (f ∘ₗ S.toSubmodule.subtype) = (imRep f hf S).toSubmodule := by
      rw [LinearMap.range_comp, Submodule.range_subtype]; rfl
    let e : S.toSubmodule ≃ₗ[ℂ] (imRep f hf S).toSubmodule :=
      (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hr)
    refine ⟨Representation.Equiv.mk e fun k => ?_⟩
    ext x
    simp [e, Subrepresentation.toRepresentation, hf]
end GlobalTheory.TypeComplement
