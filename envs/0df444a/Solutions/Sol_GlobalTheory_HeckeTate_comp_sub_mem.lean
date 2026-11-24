-- Prove2me | solution 1 for GlobalTheory.HeckeTate.comp_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:17:45.293352+00:00
-- url     : https://prove2.me/submissions/fea585d3-34e9-4937-9515-a690a43c0629

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
import Theorems.Thm_GlobalTheory_HeckeTate_smul_mem_mults

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
namespace GlobalTheory.HeckeTate
theorem _root_.solution {N : R} (u₁ u₂ u₃ : M →ₗ[R] M') (w₁ w₂ w₃ : M' →ₗ[R] M) {t₁ t₂ t₃ a₁ a₂ a₃ b₁ b₂ b₃ : R}
    (h₁ : ∀ x, w₁ (u₁ x) = t₁ • x) (h₂ : ∀ x, w₂ (u₂ x) = t₂ • x) (h₃ : ∀ x, w₃ (u₃ x) = t₃ • x)
    (h12 : N ∣ a₁ * b₂) (h13 : N ∣ a₁ * b₃) (h21 : N ∣ a₂ * b₁) (h23 : N ∣ a₂ * b₃)
    (h31 : N ∣ a₃ * b₁) (h32 : N ∣ a₃ * b₂)
    (h : N ∣ a₁ * b₁ * t₁ + a₂ * b₂ * t₂ + a₃ * b₃ * t₃ - 1) (x : M) :
    (b₁ • w₁ + b₂ • w₂ + b₃ • w₃) ((a₁ • u₁ + a₂ • u₂ + a₃ • u₃) x) - x ∈ mults M N := by
  have : (b₁ • w₁ + b₂ • w₂ + b₃ • w₃) ((a₁ • u₁ + a₂ • u₂ + a₃ • u₃) x) - x =
      (a₁ * b₂) • w₂ (u₁ x) + (a₁ * b₃) • w₃ (u₁ x) + (a₂ * b₁) • w₁ (u₂ x) + (a₂ * b₃) • w₃ (u₂ x) +
      (a₃ * b₁) • w₁ (u₃ x) + (a₃ * b₂) • w₂ (u₃ x) +
      (a₁ * b₁ * t₁ + a₂ * b₂ * t₂ + a₃ * b₃ * t₃ - 1) • x := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, h₁, h₂, h₃]
    module
  rw [this]
  repeat' apply Submodule.add_mem
  all_goals exact smul_mem_mults (by assumption) _
end GlobalTheory.HeckeTate
