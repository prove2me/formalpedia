-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.mem_secSp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:09:34.958524+00:00
-- url     : https://prove2.me/submissions/c5ec1e0d-08d3-4abf-b33e-1936ff4604db

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
theorem _root_.solution (hL : IsLevi Γ K Q Γ' K' π ι c₀) (hP : IsPull Q P P' π c₀ c c')
    (h1 : c' 1 = 1) (ρ : K →* (W →L[ℂ] W)) (w : W) :
    w ∈ secSp K P c ρ ↔ ∃ hw : w ∈ fixSp K Q π c₀ ρ,
      (⟨w, hw⟩ : fixSp K Q π c₀ ρ) ∈ secSp K' P' c' (resRep hL ρ) := by
  constructor
  · intro hw
    have hfix : w ∈ fixSp K Q π c₀ ρ := by
      intro r hr hπ
      have hrP : (r : G) ∈ P := (hP.mem _).2 ⟨hr, by rw [hπ]; exact P'.one_mem⟩
      have h2 := hw r hrP
      rwa [hP.ch ⟨r, hr⟩ (by rw [hπ]; exact P'.one_mem), hπ, h1, mul_one] at h2
    refine ⟨hfix, fun m hm => ?_⟩
    apply Subtype.ext
    have hπ : π ⟨ι m, (ι m).2⟩ = m := hL.sect m
    have hιP : ((kι hL m : K) : G) ∈ P := (hP.mem _).2 ⟨(ι m).2, by
      show π ⟨ι m, (ι m).2⟩ ∈ P'
      rw [hπ]
      exact hm⟩
    have h2 := hw _ hιP
    have h3 : c ((kι hL m : K) : G) = c' m := by
      have := hP.ch (ι m) (by rw [hL.sect]; exact hm)
      rw [hL.sect, hL.triv, one_mul] at this
      exact this
    rw [h3] at h2
    exact h2
  · rintro ⟨hfix, hw⟩ r hr
    obtain ⟨hrQ, hrπ⟩ := (hP.mem _).1 hr
    set m : K' := ⟨π ⟨r, hrQ⟩, hL.πK ⟨r, hrQ⟩ r.2⟩ with hm
    set s : K := r * (kι hL m)⁻¹ with hs
    have hsval : (s : G) = ((⟨r, hrQ⟩ * (ι (π ⟨r, hrQ⟩))⁻¹ : Q) : G) := by
      simp [hs, hm]
    have hsQ : (s : G) ∈ Q := by
      rw [hsval]
      exact Subtype.property _
    have hsπ : π ⟨s, hsQ⟩ = 1 := by
      have : (⟨(s : G), hsQ⟩ : Q) = ⟨r, hrQ⟩ * (ι (π ⟨r, hrQ⟩))⁻¹ := Subtype.ext hsval
      rw [this, map_mul, map_inv, hL.sect]
      simp
    have hcs : c₀ (s : G) = c₀ r := by
      rw [hsval, ← map_inv, c₀_ι_right hL]
    have hfs := hfix s hsQ hsπ
    rw [hcs] at hfs
    have h3 := congrArg Subtype.val (hw m hrπ)
    have h3' : c' m • ρ (kι hL m) w = w := h3
    have h4 : ρ r w = ρ s (ρ (kι hL m) w) := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, hs]
      simp
    rw [hP.ch ⟨r, hrQ⟩ hrπ, h4, mul_smul]
    have h5 : c' (π ⟨r, hrQ⟩) • ρ s (ρ (kι hL m) w) = ρ s (c' m • ρ (kι hL m) w) := by
      rw [map_smul]
    rw [h5, h3', hfs]
end GlobalTheory.CompanionTheory.RgTransfer
