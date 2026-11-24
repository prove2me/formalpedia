-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.sec_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:09:35.913264+00:00
-- url     : https://prove2.me/submissions/d3d6e117-8edb-4b7e-9fe0-dd2ede867f72

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
theorem _root_.solution {ρ : K →* (W →L[ℂ] W)} (h : IsPar Γ K P c) (hs : Law K P c ρ) {w : W}
    (hw : w ∈ secSp K P c ρ) {γ : G} (hγ : γ ∈ Γ) (hγP : γ ∈ P) (x : G) :
    sec K P c ρ (γ * x) w = sec K P c ρ x w := by
  obtain ⟨p, hp, k, hk, rfl⟩ := h.iwa x
  have h1 := hs w hw (γ * p) (P.mul_mem hγP hp) ⟨k, hk⟩
  have h2 := hs w hw p hp ⟨k, hk⟩
  simp only at h1 h2
  rw [← mul_assoc, h1, h2, h.ch.mul _ hγP _ hp, h.ch.rat γ hγ hγP, one_mul]
end GlobalTheory.CompanionTheory.RgTransfer
