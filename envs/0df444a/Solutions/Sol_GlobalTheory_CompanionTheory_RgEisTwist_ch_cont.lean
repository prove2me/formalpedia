-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisTwist.ch_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:45.329209+00:00
-- url     : https://prove2.me/submissions/be2279bb-e1c9-45a2-8958-1cc58a5bd8e0

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
theorem _root_.solution (h : IsCh Γ ⊤ c₀) : Continuous c₀ := by
  have h' := h.cont
  rw [Subgroup.coe_top] at h'
  exact continuousOn_univ.mp h'
end GlobalTheory.CompanionTheory.RgEisTwist
