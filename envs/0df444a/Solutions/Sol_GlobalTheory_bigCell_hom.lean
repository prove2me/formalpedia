-- Prove2me | solution 1 for GlobalTheory.bigCell_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:17:15.044713+00:00
-- url     : https://prove2.me/submissions/5b398699-18b1-4ffb-9031-c5bb4dd5fa01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomOfBigCellGenericRelations
import Theorems.Thm_GlobalTheory_groupChunk_extend

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
theorem _root_.solution : ∀ (G H : Type) [Group G] [Group H] (P : Subgroup G) (w : G) (ρ : P →* H) (W : H), (∀ p q : P, w * p = q * w → W * ρ p = ρ q * W) → (∀ p : P, (∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂) → ∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂ ∧ W * ρ p * W = ρ p₁ * W * ρ p₂) → (∀ s : Finset G, ∃ u : G, ∀ g ∈ s, ∃ p₁ p₂ : P, g * u = p₁ * w * p₂) → ∃ Φ : G →* H, (∀ p : P, Φ p = ρ p) ∧ Φ w = W := by
  classical
  intro G H _ _ P w ρ W ha hb hc
  let C : G → Prop := fun g => ∃ p₁ p₂ : P, g = p₁ * w * p₂

  have hwd : ∀ p₁ p₂ q₁ q₂ : P, (p₁ : G) * w * p₂ = q₁ * w * q₂ →
      ρ p₁ * W * ρ p₂ = ρ q₁ * W * ρ q₂ := by
    intro p₁ p₂ q₁ q₂ h
    have h' : w * ((p₂ * q₂⁻¹ : P) : G) = ((p₁⁻¹ * q₁ : P) : G) * w := by
      push_cast
      calc w * ((p₂ : G) * (q₂ : G)⁻¹)
          = (p₁ : G)⁻¹ * ((p₁ : G) * w * p₂) * (q₂ : G)⁻¹ := by group
        _ = (p₁ : G)⁻¹ * ((q₁ : G) * w * q₂) * (q₂ : G)⁻¹ := by rw [h]
        _ = (p₁ : G)⁻¹ * q₁ * w := by group
    have h'' := ha _ _ h'
    rw [map_mul, map_mul, map_inv, map_inv] at h''
    calc ρ p₁ * W * ρ p₂ = ρ p₁ * (W * (ρ p₂ * (ρ q₂)⁻¹)) * ρ q₂ := by group
      _ = ρ p₁ * ((ρ p₁)⁻¹ * ρ q₁ * W) * ρ q₂ := by rw [h'']
      _ = ρ q₁ * W * ρ q₂ := by group
  let f : G → H := fun g => if h : C g then ρ h.choose * W * ρ h.choose_spec.choose else 1
  have hf : ∀ p₁ p₂ : P, f (p₁ * w * p₂) = ρ p₁ * W * ρ p₂ := by
    intro p₁ p₂
    have hC : C (p₁ * w * p₂) := ⟨p₁, p₂, rfl⟩
    dsimp only [f]
    rw [dif_pos hC]
    exact hwd _ _ _ _ hC.choose_spec.choose_spec.symm
  have hmul : ∀ x y, C x → C y → C (x * y) → f (x * y) = f x * f y := by
    rintro x y ⟨p₁, p₂, rfl⟩ ⟨q₁, q₂, rfl⟩ ⟨r₁, r₂, hr⟩
    have hin : ∃ a b : P, w * ((p₂ * q₁ : P) : G) * w = a * w * b :=
      ⟨p₁⁻¹ * r₁, r₂ * q₂⁻¹, by
        push_cast
        calc w * ((p₂ : G) * q₁) * w
            = (p₁ : G)⁻¹ * ((p₁ : G) * w * p₂ * ((q₁ : G) * w * q₂)) * (q₂ : G)⁻¹ := by group
          _ = (p₁ : G)⁻¹ * ((r₁ : G) * w * r₂) * (q₂ : G)⁻¹ := by rw [hr]
          _ = (p₁ : G)⁻¹ * r₁ * w * ((r₂ : G) * (q₂ : G)⁻¹) := by group⟩
    obtain ⟨a, b, hab, hW⟩ := hb _ hin
    rw [map_mul] at hW
    have hxy : (p₁ : G) * w * p₂ * ((q₁ : G) * w * q₂) = ((p₁ * a : P) : G) * w * ((b * q₂ : P) : G) := by
      calc (p₁ : G) * w * p₂ * ((q₁ : G) * w * q₂)
          = (p₁ : G) * (w * ((p₂ * q₁ : P) : G) * w) * q₂ := by push_cast; group
        _ = (p₁ : G) * ((a : G) * w * b) * q₂ := by rw [hab]
        _ = ((p₁ * a : P) : G) * w * ((b * q₂ : P) : G) := by push_cast; group
    rw [hxy, hf, hf, hf, map_mul, map_mul]
    calc ρ p₁ * ρ a * W * (ρ b * ρ q₂) = ρ p₁ * (ρ a * W * ρ b) * ρ q₂ := by group
      _ = ρ p₁ * (W * (ρ p₂ * ρ q₁) * W) * ρ q₂ := by rw [hW]
      _ = ρ p₁ * W * ρ p₂ * (ρ q₁ * W * ρ q₂) := by group
  obtain ⟨Φ, hΦ⟩ := groupChunk_extend C f hmul hc
  refine ⟨Φ, fun p => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := hc {1}
    obtain ⟨a, b, hab⟩ := hu 1 (by simp)
    rw [one_mul] at hab
    have e1 : (p : G) * u = ((p * a : P) : G) * w * b := by
      rw [hab]
      push_cast
      group
    rw [hΦ p u ⟨a, b, hab⟩ ⟨p * a, b, e1⟩, e1, hab, hf, hf, map_mul]
    group
  · obtain ⟨u, hu⟩ := hc {1, w}
    obtain ⟨a, b, hab⟩ := hu 1 (by simp)
    rw [one_mul] at hab
    obtain ⟨c, d, hcd⟩ := hu w (by simp)
    have hin : ∃ p₁ p₂ : P, w * (a : G) * w = p₁ * w * p₂ :=
      ⟨c, d * b⁻¹, by
        calc w * (a : G) * w = w * u * (b : G)⁻¹ := by rw [hab]; group
          _ = (c : G) * w * d * (b : G)⁻¹ := by rw [hcd]
          _ = (c : G) * w * ((d * b⁻¹ : P) : G) := by push_cast; group⟩
    obtain ⟨r₁, r₂, hr, hW⟩ := hb a hin
    have e1 : w * u = (r₁ : G) * w * ((r₂ * b : P) : G) := by
      rw [hab]
      push_cast
      calc w * ((a : G) * w * b) = w * a * w * b := by group
        _ = (r₁ : G) * w * ((r₂ : G) * b) := by rw [hr]; group
    rw [hΦ w u ⟨a, b, hab⟩ ⟨c, d, hcd⟩, e1, hab, hf, hf, map_mul]
    calc ρ r₁ * W * (ρ r₂ * ρ b) * (ρ a * W * ρ b)⁻¹ = (ρ r₁ * W * ρ r₂) * (ρ a * W)⁻¹ := by group
      _ = (W * ρ a * W) * (ρ a * W)⁻¹ := by rw [hW]
      _ = W := by group
end GlobalTheory
