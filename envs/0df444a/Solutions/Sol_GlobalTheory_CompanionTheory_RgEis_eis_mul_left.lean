-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.eis_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:35:14.202796+00:00
-- url     : https://prove2.me/submissions/20836757-ca89-4f57-8d24-aab110811dc2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_tsum_rep_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_sec_left

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
theorem _root_.solution (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hη : IsHt Γ K P η) (hw : w ∈ secSp K P c ρ) (z : ℂ) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    eis Γ K P c ρ (fun x => z * η x) (γ * g) w = eis Γ K P c ρ (fun x => z * η x) g w := by
  unfold eis
  refine tsum_rep_mul (fun x => Complex.exp (z * η x) • sec K P c ρ x w) ?_ hγ g
  intro δ h1 h2 x
  simp only [sec_left hP h hw h1 h2 x, hη.left δ h2 x, hη.rat δ h1 h2, zero_add]
end GlobalTheory.CompanionTheory.RgEis
