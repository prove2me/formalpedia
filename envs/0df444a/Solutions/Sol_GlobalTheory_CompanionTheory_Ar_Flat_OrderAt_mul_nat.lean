-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.OrderAt.mul_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:18:40.733883+00:00
-- url     : https://prove2.me/submissions/5c0f56f1-7887-41b9-98d1-effe289dd4e8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]
variable {L : Lat ξ E} {σ : E} {ϖ : Ω} {M M' : ℕ} {a a' : ℤ} {p : Cpt ξ}
namespace GlobalTheory.CompanionTheory.Ar.Flat
namespace OrderAt
theorem _root_.solution (h : OrderAt L σ ϖ M a p) (k : ℕ) : OrderAt L σ ϖ (M * k) (a * k) p := by
  obtain ⟨e, c, he, hL, hσ, h⟩ := h
  refine ⟨e, c, he, hL, hσ, ?_⟩
  rw [pow_mul, zpow_mul, zpow_natCast, ← div_pow]
  exact ZUnit.pow h k
end OrderAt
end GlobalTheory.CompanionTheory.Ar.Flat
