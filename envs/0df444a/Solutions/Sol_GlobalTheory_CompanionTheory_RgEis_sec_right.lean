-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.sec_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:01:30.22283+00:00
-- url     : https://prove2.me/submissions/350e731d-d026-4497-8e1c-80ff81088be8

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
    (hw : w ∈ secSp K P c ρ) (x : G) (k : K) :
    sec K P c ρ (x * k) w = ρ k⁻¹ (sec K P c ρ x w) := by
  obtain ⟨p, hp, k', hk', rfl⟩ := hP.iwa x
  have e := h w hw p hp (⟨k', hk'⟩ * k)
  have e' := h w hw p hp ⟨k', hk'⟩
  simp only at e'
  have e2 : p * k' * (k : G) = p * (((⟨k', hk'⟩ : K) * k : K) : G) := by simp [mul_assoc]
  rw [e2, e, e', map_smul, mul_inv_rev, map_mul]
  rfl
end GlobalTheory.CompanionTheory.RgEis
