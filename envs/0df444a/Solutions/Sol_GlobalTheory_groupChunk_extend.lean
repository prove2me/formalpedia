-- Prove2me | solution 1 for GlobalTheory.groupChunk_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:58:58.935799+00:00
-- url     : https://prove2.me/submissions/51ecc574-187e-4aaf-9b97-6f4c2bc44e7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomOfBigCellGenericRelations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G H : Type} [Group G] [Group H] (C : G → Prop) (f : G → H)
    (hmul : ∀ x y, C x → C y → C (x * y) → f (x * y) = f x * f y)
    (hgen : ∀ s : Finset G, ∃ u : G, ∀ g ∈ s, C (g * u)) :
    ∃ Φ : G →* H, ∀ g u, C u → C (g * u) → Φ g = f (g * u) * (f u)⁻¹ := by
  classical

  have key : ∀ g u w, C u → C (g * u) → C w → C (g * w) → C (u⁻¹ * w) →
      f (g * u) * (f u)⁻¹ = f (g * w) * (f w)⁻¹ := by
    intro g u w hu hgu hw hgw huw
    have h1 : f w = f u * f (u⁻¹ * w) := by
      have h := hmul u (u⁻¹ * w) hu huw (by rwa [mul_inv_cancel_left])
      rwa [mul_inv_cancel_left] at h
    have h2 : f (g * w) = f (g * u) * f (u⁻¹ * w) := by
      have h := hmul (g * u) (u⁻¹ * w) hgu huw (by rwa [mul_assoc, mul_inv_cancel_left])
      rwa [mul_assoc, mul_inv_cancel_left] at h
    rw [h1, h2]
    group
  choose u₀ hu₀ using fun g : G => hgen {1, g}
  have hu₀1 : ∀ g, C (u₀ g) := fun g => by simpa using hu₀ g 1 (by simp)
  have hu₀g : ∀ g, C (g * u₀ g) := fun g => hu₀ g g (by simp)
  let φ : G → H := fun g => f (g * u₀ g) * (f (u₀ g))⁻¹
  have hφ : ∀ g u, C u → C (g * u) → φ g = f (g * u) * (f u)⁻¹ := by
    intro g u hu hgu
    obtain ⟨w, hw⟩ := hgen {1, g, u⁻¹, (u₀ g)⁻¹}
    have hw1 : C w := by simpa using hw 1 (by simp)
    have hwg : C (g * w) := hw g (by simp)
    have hwu : C (u⁻¹ * w) := hw u⁻¹ (by simp)
    have hwu₀ : C ((u₀ g)⁻¹ * w) := hw (u₀ g)⁻¹ (by simp)
    rw [key g u w hu hgu hw1 hwg hwu]
    exact key g (u₀ g) w (hu₀1 g) (hu₀g g) hw1 hwg hwu₀
  refine ⟨MonoidHom.mk' φ ?_, fun g u hu hgu => hφ g u hu hgu⟩
  intro g h
  obtain ⟨w, hw⟩ := hgen {1, h, g * h}
  have hw1 : C w := by simpa using hw 1 (by simp)
  have hwh : C (h * w) := hw h (by simp)
  have hwgh : C (g * h * w) := hw (g * h) (by simp)
  rw [hφ (g * h) w hw1 hwgh, hφ h w hw1 hwh, hφ g (h * w) hwh (by rwa [← mul_assoc]),
    ← mul_assoc g h w]
  group
end GlobalTheory
