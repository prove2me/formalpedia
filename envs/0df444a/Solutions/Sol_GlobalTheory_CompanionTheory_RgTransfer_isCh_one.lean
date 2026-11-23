-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.isCh_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:30.963959+00:00
-- url     : https://prove2.me/submissions/51ab72d7-fd53-486e-9b97-9941f60a735b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgTransfer
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {G' : Type} [Group G'] [TopologicalSpace G']
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution {Γ P : Subgroup G} {c : G → ℂ} (h : IsCh Γ P c) : c 1 = 1 := by
  have h1 := h.mul 1 P.one_mem 1 P.one_mem
  have h2 := h.norm 1 P.one_mem
  have h0 : c 1 ≠ 0 := by
    intro h0
    simp [h0] at h2
  rw [mul_one] at h1
  exact mul_left_cancel₀ h0 (by rw [mul_one]; exact h1.symm)
end GlobalTheory.CompanionTheory.RgTransfer
