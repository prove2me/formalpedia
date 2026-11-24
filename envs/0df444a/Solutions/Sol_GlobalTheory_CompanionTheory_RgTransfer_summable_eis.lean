-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.summable_eis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:09:36.902131+00:00
-- url     : https://prove2.me/submissions/55494044-a4dc-47fe-8a27-7cb4b3e8226c

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
variable {Γ K Q : Subgroup G} {Γ' K' : Subgroup G'} {π : Q →* G'} {ι : G' →* Q} {c₀ : G → ℂ}
variable {P : Subgroup G} {P' : Subgroup G'} {c : G → ℂ} {c' : G' → ℂ}
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution {ρ : K →* (W →L[ℂ] W)} [CompleteSpace W] {M : ℝ}
    (hM : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {Λ : G → ℂ} {l : G → ℝ}
    (hl : ∀ g, (Λ g).re = l g) (hc : Conv Γ P l) (g : G) (w : W) :
    Summable fun y : Cos P Γ => Complex.exp (Λ (rep y * g)) • sec K P c ρ (rep y * g) w := by
  refine Summable.of_norm_bounded ((hc g).mul_right (M * ‖w‖)) (fun y => ?_)
  rw [norm_smul, Complex.norm_exp, hl]
  exact mul_le_mul_of_nonneg_left (hM _ _) (Real.exp_pos _).le
end GlobalTheory.CompanionTheory.RgTransfer
