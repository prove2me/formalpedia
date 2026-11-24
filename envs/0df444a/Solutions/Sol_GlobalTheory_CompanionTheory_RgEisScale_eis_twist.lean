-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisScale.eis_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:08:29.91782+00:00
-- url     : https://prove2.me/submissions/2ec16ee3-0074-483a-ab7b-c1062b11298d

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
theorem _root_.solution {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) (c : G → ℂ)
    (ρ : K →* (W →L[ℂ] W)) (Λ Λ' : G → ℂ) (t : ℂ) (h : ∀ x, Λ' x = Λ x + t * l x) (g : G) (w : W) :
    eis Γ K P c ρ Λ' g w = Complex.exp (t * l g) • eis Γ K P c ρ Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  rw [h, ht_rep hl, Complex.exp_add, smul_smul, mul_comm]
end GlobalTheory.CompanionTheory.RgEisScale
