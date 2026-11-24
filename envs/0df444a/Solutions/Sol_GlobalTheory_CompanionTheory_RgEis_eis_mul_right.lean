-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.eis_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:17:35.76079+00:00
-- url     : https://prove2.me/submissions/54c699b9-5771-43ac-bf99-1c3346352b80

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_sec_right
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_summable_term

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
theorem _root_.solution [CompleteSpace W] (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖)
    (hη : IsHt Γ K P η) (hw : w ∈ secSp K P c ρ) (z : ℂ) (hc : Conv Γ P fun g => z.re * η g) (g : G) (k : K) :
    eis Γ K P c ρ (fun x => z * η x) (g * k) w = ρ k⁻¹ (eis Γ K P c ρ (fun x => z * η x) g w) := by
  have hs := summable_term (Γ := Γ) (l := fun g => z.re * η g) (Λ := fun x => z * η x) hb hc
    (by intro x; simp) g w
  unfold eis
  rw [(ρ k⁻¹).map_tsum hs]
  refine tsum_congr fun q => ?_
  rw [← mul_assoc]
  beta_reduce
  rw [hη.right _ k k.2, sec_right hP h hw, map_smul]
end GlobalTheory.CompanionTheory.RgEis
