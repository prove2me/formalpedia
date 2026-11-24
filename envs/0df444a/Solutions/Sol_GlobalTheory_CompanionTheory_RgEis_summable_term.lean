-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.summable_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:59:00.844367+00:00
-- url     : https://prove2.me/submissions/d5c41285-5997-435d-8248-cbb5d2291855

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_norm_term_le

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
theorem _root_.solution [CompleteSpace W] {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ}
    (hl : Conv Γ P l) {Λ : G → ℂ} (hΛ : ∀ x, (Λ x).re = l x) (g : G) (w : W) :
    Summable fun q : Cos P Γ => Complex.exp (Λ (rep q * g)) • sec K P c ρ (rep q * g) w :=
  Summable.of_norm_bounded ((hl g).mul_left (M * ‖w‖)) fun q => norm_term_le hb hΛ _ w
end GlobalTheory.CompanionTheory.RgEis
