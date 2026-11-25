-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.TrivRed.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:31:13.479822+00:00
-- url     : https://prove2.me/submissions/22548abd-c450-4529-95a2-d983879eef16

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_coe_mem_zeroSet

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
namespace TrivRed
theorem _root_.solution {L : Lat ξ E} {ϖ ϖ' : Ω} (h : TrivRed L ϖ) (hs : zeroSet ξ ϖ' ⊆ zeroSet ξ ϖ) :
    TrivRed L ϖ' := by
  have key : ∀ p, ¬ unitAt ξ p ϖ' → ¬ unitAt ξ p ϖ := fun p hp =>
    (coe_mem_zeroSet p).1 (hs ((coe_mem_zeroSet p).2 hp))
  obtain ⟨t, ht⟩ := h
  refine ⟨t, fun p hp => ?_⟩
  obtain ⟨U, hU, H⟩ := ht p (key p hp)
  exact ⟨U, hU, fun q hq hq' => H q hq (key q hq')⟩
end TrivRed
end GlobalTheory.CompanionTheory.Ar.Flat
