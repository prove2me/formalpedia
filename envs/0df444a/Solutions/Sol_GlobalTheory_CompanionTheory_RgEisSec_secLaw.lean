-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisSec.secLaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:31:01.287078+00:00
-- url     : https://prove2.me/submissions/97fed140-14a1-48c9-9aa0-e5e387f1b7d3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_Iwa
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SectionLawHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisSec_sec_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisSec_sec_continuous
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisSec_sec_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisSec
variable {G : Type} [Group G] [TopologicalSpace G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory.CompanionTheory.RgEisSec
theorem _root_.solution : SecLaw := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ P c hpar
  exact ⟨fun w hw p hp k => sec_mul hpar.ch hw hp k,
    fun w hw => sec_continuous hK hρ hpar hw, sec_bound hK hρ hpar⟩
end GlobalTheory.CompanionTheory.RgEisSec
