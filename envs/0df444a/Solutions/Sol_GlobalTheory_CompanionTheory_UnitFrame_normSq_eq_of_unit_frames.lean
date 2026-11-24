-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnitFrame.normSq_eq_of_unit_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:08:19.182512+00:00
-- url     : https://prove2.me/submissions/ed6af743-2791-4f64-9bc5-4021fb09880d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryFramesPreserveNormSqSum
import Theorems.Thm_GlobalTheory_CompanionTheory_UnitFrame_normSq_eq_scalar_mul_form
import Theorems.Thm_GlobalTheory_CompanionTheory_UnitFrame_normSq_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnitFrame
namespace GlobalTheory.CompanionTheory.UnitFrame
theorem _root_.solution : ∀ (m : ℕ), 1 ≤ m → ∀ (J : Matrix (Fin m) (Fin m) ℂ) (fr fr' : GL (Fin m) ℂ) (ζ ζ' : ℂ) (s s' : ℤˣ), (ζ = 1 ∨ ζ = Complex.I) → (ζ' = 1 ∨ ζ' = Complex.I) → ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1 → ζ' • (fr'.1ᵀ * J * fr'.1.map star) = ((s' : ℤ) : ℂ) • 1 → ∀ v : Fin m → ℂ, ∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 = ∑ a, ‖((fr'⁻¹).1 *ᵥ v) a‖ ^ 2 := by
  intro m hm J fr fr' ζ ζ' s s' hζ hζ' h h' v
  have key := normSq_eq_scalar_mul_form J fr ζ s h
  have key' := normSq_eq_scalar_mul_form J fr' ζ' s' h'
  have hα : ((s : ℤ) : ℂ) * star ζ = ((s' : ℤ) : ℂ) * star ζ' := by
    have k0 := key (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))
    have k0' := key' (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))
    have hr := normSq_pos hm fr
    have hr' := normSq_pos hm fr'
    generalize (∑ a, ‖((fr⁻¹).1 *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))) a‖ ^ 2) = r at k0 hr
    generalize (∑ a, ‖((fr'⁻¹).1 *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))) a‖ ^ 2) = r' at k0' hr'
    generalize (star (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ)) ⬝ᵥ
      (J.map star *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ)))) = Q at k0 k0'
    rcases hζ with rfl | rfl <;> rcases hζ' with rfl | rfl <;>
      rcases Int.units_eq_one_or s with rfl | rfl <;>
      rcases Int.units_eq_one_or s' with rfl | rfl <;>
      simp [Complex.ext_iff] at k0 k0' ⊢ <;> linarith
  apply Complex.ofReal_injective
  rw [key v, key' v, hα]
end GlobalTheory.CompanionTheory.UnitFrame
