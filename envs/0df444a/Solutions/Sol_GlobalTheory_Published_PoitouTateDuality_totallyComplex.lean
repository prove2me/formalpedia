-- Prove2me | solution 1 for GlobalTheory.Published.PoitouTateDuality.totallyComplex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:14:28.921118+00:00
-- url     : https://prove2.me/submissions/56ba8218-a042-4dad-a863-261c6b835cc5

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ExistsPrimitiveRootPow_85cddf4c39d1fc1a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.Published
open PoitouTate
open NumberField IsDedekindDomain
namespace GlobalTheory.Published
namespace _root_.GlobalTheory.Published.PoitouTateDuality
theorem _root_.solution (h : _root_.GlobalTheory.Published.PoitouTateDuality) :
    _root_.GlobalTheory.Published.PoitouTateTotallyComplex := by
  unfold _root_.GlobalTheory.Published.PoitouTateTotallyComplex
  intro F Ω _ _ _ _ _ _ l _ r hr ζ hζ
  obtain ⟨inv, hloc, hall⟩ := h F Ω l r (Or.inr inferInstance) hr ζ hζ
  exact ⟨inv, hloc, fun S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ =>
    ⟨(hall S hS Av hAv μ hμ M ρ hρ).1, (hall S hS Av hAv μ hμ M ρ hρ).2.1⟩⟩
end _root_.GlobalTheory.Published.PoitouTateDuality
end GlobalTheory.Published
