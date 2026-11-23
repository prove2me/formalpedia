-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisScale.ht_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:29.9375+00:00
-- url     : https://prove2.me/submissions/3773ada5-d9e0-42d8-bf1e-64aea3b87c51

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EisensteinScalingLaw

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisScale
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory.CompanionTheory.RgEisScale
theorem _root_.solution {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) (q : Cos P Γ) (g : G) :
    l (rep q * g) = l g := by
  have hq : rep q ∈ Γ := (Quotient.out q).2
  rw [hl.left _ (Subgroup.mem_top _), hl.rat _ hq (Subgroup.mem_top _), zero_add]
end GlobalTheory.CompanionTheory.RgEisScale
