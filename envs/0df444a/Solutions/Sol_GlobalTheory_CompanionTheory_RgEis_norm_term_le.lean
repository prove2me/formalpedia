-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.norm_term_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:27.97427+00:00
-- url     : https://prove2.me/submissions/d22af22e-e80e-4623-9f87-46432adb4849

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
theorem _root_.solution {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ} {Λ : G → ℂ}
    (hΛ : ∀ x, (Λ x).re = l x) (x : G) (w : W) :
    ‖Complex.exp (Λ x) • sec K P c ρ x w‖ ≤ M * ‖w‖ * Real.exp (l x) := by
  rw [norm_smul, Complex.norm_exp, hΛ, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb x w) (Real.exp_pos _).le
end GlobalTheory.CompanionTheory.RgEis
