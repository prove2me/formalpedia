-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.sec_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:01:29.121646+00:00
-- url     : https://prove2.me/submissions/5d27a437-e1b4-4b0c-bdb0-675e68e09a23

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
theorem _root_.solution (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hw : w ∈ secSp K P c ρ) {δ : G} (h1 : δ ∈ Γ) (h2 : δ ∈ P) (x : G) :
    sec K P c ρ (δ * x) w = sec K P c ρ x w := by
  obtain ⟨p, hp, k, hk, rfl⟩ := hP.iwa x
  have e := h w hw (δ * p) (mul_mem h2 hp) ⟨k, hk⟩
  have e' := h w hw p hp ⟨k, hk⟩
  simp only at e e'
  rw [← mul_assoc, e, e', hP.ch.mul δ h2 p hp, hP.ch.rat δ h1 h2, one_mul]
end GlobalTheory.CompanionTheory.RgEis
