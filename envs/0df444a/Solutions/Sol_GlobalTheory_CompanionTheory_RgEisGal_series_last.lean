-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.series_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:01:35.279092+00:00
-- url     : https://prove2.me/submissions/7b4b05e3-e7f3-484e-b1e9-13efefb83ce3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GalleryOfTubesAndCrossing
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_outer_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_tsum_cos_inf


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W]
  [NormedSpace ℂ W]
variable [CompleteSpace W]
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution {Γ K S : Subgroup G} {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]
    {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {h : G → ℝ}
    {H : ℂ → G → L →L[ℂ] W} {N : ℂ} {T : L →L[ℂ] secSp K S c ρ}
    (hT : ∀ g w, H N g w = Complex.exp (h g) • sec K S c ρ g (T w)) (u : ℂ) (g : G)
    (hs : Summable fun r : Cos (Γ ⊓ S) Γ =>
      ‖Complex.exp (u * h (rep r * g)) • H N (rep r * g)‖) (w : L) :
    outer Γ (Γ ⊓ S) h H (N, u) g w = eis Γ K S c ρ (fun x => h x + u * h x) g (T w) := by
  rw [outer_apply h H (N, u) g hs w]
  simp only [hT]
  rw [tsum_cos_inf Γ S fun v => Complex.exp (u * h (v * g)) •
    Complex.exp (h (v * g)) • sec K S c ρ (v * g) (T w)]
  simp only [eis]
  congr 1
  ext q
  rw [smul_smul, ← Complex.exp_add, add_comm]
end GlobalTheory.CompanionTheory.RgEisGal
