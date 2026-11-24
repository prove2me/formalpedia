-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.am_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:12:12.125967+00:00
-- url     : https://prove2.me/submissions/ce477abb-9bca-4224-962a-c69f804ed307

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_resRep_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_am_apply

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
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W)) (q : Q) (k r : K)
    (hr : (r : G) ∈ Q) (v : fixSp K Q π c₀ ρ) :
    am ρ c₀ π (q * ⟨r, hr⟩) (r⁻¹ * k)
      (resRep hL ρ ⟨π ⟨r, hr⟩, hL.πK ⟨r, hr⟩ r.2⟩⁻¹ v) = am ρ c₀ π q k v := by
  set m : K' := ⟨π ⟨r, hr⟩, hL.πK ⟨r, hr⟩ r.2⟩ with hm
  set s : K := r * (kι hL m)⁻¹ with hs
  have hsQ : (s : G) ∈ Q := by
    have : (s : G) = ((⟨r, hr⟩ * (ι (π ⟨r, hr⟩))⁻¹ : Q) : G) := by
      simp [hs, hm]
    rw [this]
    exact Subtype.property _
  have hsval : (⟨(s : G), hsQ⟩ : Q) = ⟨r, hr⟩ * (ι (π ⟨r, hr⟩))⁻¹ := by
    apply Subtype.ext
    simp [hs, hm]
  have hsπ : π ⟨s, hsQ⟩ = 1 := by
    rw [hsval, map_mul, map_inv, hL.sect]
    simp
  have hcs : c₀ (s : G) = c₀ r := by
    have : c₀ (s : G) = c₀ ((⟨r, hr⟩ * (ι (π ⟨r, hr⟩))⁻¹ : Q) : G) :=
      congrArg c₀ (congrArg Subtype.val hsval)
    rw [this, ← map_inv, c₀_ι_right hL]
  have hv := v.2 s hsQ hsπ
  rw [hcs] at hv
  rw [am_apply, am_apply, c₀_mul hL]
  have h1 : ρ (r⁻¹ * k)⁻¹ ((resRep hL ρ m⁻¹ v : fixSp K Q π c₀ ρ) : W) = ρ k⁻¹ (ρ s (v : W)) := by
    rw [resRep_coe, map_inv (kι hL) m, hs]
    rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  rw [h1]
  have h2 : (c₀ (q : G) * c₀ r) • ρ k⁻¹ (ρ s (v : W)) = c₀ (q : G) • ρ k⁻¹ (c₀ r • ρ s (v : W)) := by
    rw [map_smul, smul_smul]
  simp only [Subgroup.coe_mk] at *
  rw [h2, hv]
end GlobalTheory.CompanionTheory.RgTransfer
