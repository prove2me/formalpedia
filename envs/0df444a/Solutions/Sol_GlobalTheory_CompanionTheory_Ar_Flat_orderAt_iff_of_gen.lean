-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.orderAt_iff_of_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:18:39.200989+00:00
-- url     : https://prove2.me/submissions/f607cb5e-7be7-4ef6-97f6-0cfb1304f39d

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
theorem _root_.solution {e : E} {c : Ω} (he : e ≠ 0) (hL : L p = Submodule.span (regAt ξ p) {e})
    (hσ : σ = c • e) : OrderAt L σ ϖ M a p ↔ unitAt ξ p (c ^ M / ϖ ^ a) :=
  ⟨fun h => h.unitAt hL hσ, fun h => ⟨e, c, he, hL, hσ, h⟩⟩
end GlobalTheory.CompanionTheory.Ar.Flat
