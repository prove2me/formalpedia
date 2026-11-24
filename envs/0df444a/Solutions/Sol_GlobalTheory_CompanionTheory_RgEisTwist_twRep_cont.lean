-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisTwist.twRep_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:08:22.882384+00:00
-- url     : https://prove2.me/submissions/3b4070d7-b9d5-47e7-93fa-07916429b61f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistOfSectionLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTwist_ch_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisTwist
open PositivityTheory.RgEis
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K : Subgroup G} {c₀ : G → ℂ}
namespace GlobalTheory.CompanionTheory.RgEisTwist
theorem _root_.solution (h : IsCh Γ ⊤ c₀) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) :
    Continuous (twRep h K ρ) :=
  ((ch_cont h).comp continuous_subtype_val).smul hρ
end GlobalTheory.CompanionTheory.RgEisTwist
