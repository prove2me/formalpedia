-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.TrivMod.of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:31:07.732642+00:00
-- url     : https://prove2.me/submissions/c381afee-cb2a-4230-8904-4f6a6da11c5d

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
namespace GlobalTheory.CompanionTheory.Ar.Flat
namespace TrivMod
theorem _root_.solution {L : Lat ξ E} {ϖ a : Ω} (hϖ : ∀ p, ϖ ∈ regAt ξ p) (ha : ∀ p, a ∈ regAt ξ p)
    (h : TrivMod L (ϖ * a)) : TrivMod L ϖ := by
  have key : ∀ p, ¬ unitAt ξ p ϖ → ¬ unitAt ξ p (ϖ * a) := fun p hp hu => hp (ZUnit.of_mul (hϖ p) (ha p) hu)
  obtain ⟨t, ht⟩ := h
  refine ⟨t, fun p hp => ?_⟩
  obtain ⟨U, hU, h⟩ := ht p (key p hp)
  refine ⟨U, hU, fun q hq hq' => ?_⟩
  obtain ⟨h0, h1, y, hy, e⟩ := h q hq (key q hq')
  exact ⟨h0, h1, a • y, (L q).smul_mem (⟨a, ha q⟩ : regAt ξ q) hy, by rw [e, mul_smul]⟩
end TrivMod
end GlobalTheory.CompanionTheory.Ar.Flat
