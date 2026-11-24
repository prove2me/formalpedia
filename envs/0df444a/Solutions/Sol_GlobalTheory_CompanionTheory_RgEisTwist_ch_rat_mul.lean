-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisTwist.ch_rat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:08:39.845628+00:00
-- url     : https://prove2.me/submissions/b55eeec8-853a-4ebf-bbd1-faa06b1571a1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistOfSectionLaw

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
theorem _root_.solution (h : IsCh Γ ⊤ c₀) {γ : G} (hγ : γ ∈ Γ) (g : G) : c₀ (γ * g) = c₀ g := by
  rw [ch_mul h, h.rat γ hγ (Subgroup.mem_top γ), one_mul]
end GlobalTheory.CompanionTheory.RgEisTwist
