-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.pos_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:01:26.595066+00:00
-- url     : https://prove2.me/submissions/a0632c80-d57d-4d3c-99c6-7afe3e49e21d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {η : G → ℝ} {w : W}
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution (l : G → ℝ) (g : G) : 0 ≤ pos Γ P l g :=
  tsum_nonneg fun _ => (Real.exp_pos _).le
end GlobalTheory.CompanionTheory.RgEis
