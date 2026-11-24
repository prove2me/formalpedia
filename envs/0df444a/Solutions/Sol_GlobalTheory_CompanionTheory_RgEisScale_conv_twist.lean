-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisScale.conv_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:08:28.919072+00:00
-- url     : https://prove2.me/submissions/89d1c1e8-0da0-4390-bf64-f81b8114e516

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EisensteinScalingLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisScale_ht_rep

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
theorem _root_.solution {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) {f f' : G → ℝ} (t : ℝ)
    (h : ∀ x, f' x = f x + t * l x) (hc : Conv Γ P f) : Conv Γ P f' := by
  intro g
  refine ((hc g).mul_right (Real.exp (t * l g))).congr fun q => ?_
  rw [h, ht_rep hl, Real.exp_add]
end GlobalTheory.CompanionTheory.RgEisScale
