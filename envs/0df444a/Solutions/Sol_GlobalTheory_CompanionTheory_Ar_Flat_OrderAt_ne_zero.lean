-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.OrderAt.ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:18:42.015806+00:00
-- url     : https://prove2.me/submissions/3b9d3db3-3946-490a-88a0-50a57d26bf0d

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
theorem _root_.solution (h : OrderAt L σ ϖ M a p) (hM : M ≠ 0) : σ ≠ 0 := by
  obtain ⟨e, c, he, -, rfl, h⟩ := h
  refine smul_ne_zero ?_ he
  rintro rfl
  exact h.1 (by rw [zero_pow hM, zero_div])
end OrderAt
end GlobalTheory.CompanionTheory.Ar.Flat
