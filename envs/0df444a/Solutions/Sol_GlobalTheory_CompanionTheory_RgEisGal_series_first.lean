-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.series_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:01:33.567174+00:00
-- url     : https://prove2.me/submissions/afee1176-f97c-4815-947c-acdfb4fdb5a9

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
theorem _root_.solution {Γ K S : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {h : G → ℝ}
    {H : ℂ → G → (secSp K S c ρ) →L[ℂ] W} {a₀ : ℂ}
    (hH : ∀ g (w : secSp K S c ρ), H 0 g w = a₀ • sec K S c ρ g w) (z : ℂ) (g : G)
    (hs : Summable fun r : Cos (Γ ⊓ S) Γ =>
      ‖Complex.exp (z * h (rep r * g)) • H 0 (rep r * g)‖) (w : secSp K S c ρ) :
    outer Γ (Γ ⊓ S) h H (0, z) g w = a₀ • eis Γ K S c ρ (fun x => z * h x) g w := by
  rw [outer_apply h H (0, z) g hs w]
  simp only [hH]
  rw [tsum_cos_inf Γ S fun u => Complex.exp (z * h (u * g)) • a₀ • sec K S c ρ (u * g) w]
  simp only [eis]
  rw [← tsum_const_smul'' a₀]
  congr 1
  ext q
  rw [smul_comm]
end GlobalTheory.CompanionTheory.RgEisGal
