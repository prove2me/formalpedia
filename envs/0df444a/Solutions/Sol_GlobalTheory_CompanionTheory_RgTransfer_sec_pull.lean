-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.sec_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:47.783069+00:00
-- url     : https://prove2.me/submissions/fc5d282e-c193-4d3d-84ad-0104300b9880

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
variable {P : Subgroup G} {P' : Subgroup G'} {c : G → ℂ} {c' : G' → ℂ}
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution (hL : IsLevi Γ K Q Γ' K' π ι c₀) (hP : IsPull Q P P' π c₀ c c') (hiwa : Iwa P' K')
    {ρ : K →* (W →L[ℂ] W)} (h1 : Law K P c ρ) (h2 : Law K' P' c' (resRep hL ρ))
    {v : fixSp K Q π c₀ ρ} (hv : v ∈ secSp K' P' c' (resRep hL ρ)) (hv' : (v : W) ∈ secSp K P c ρ)
    (q : Q) (k : K) :
    sec K P c ρ ((q : G) * k) v = am ρ c₀ π q k (sec K' P' c' (resRep hL ρ) (π q) v) := by
  obtain ⟨p', hp', k', hk', h⟩ := hiwa (π q)
  set m : K' := ⟨k', hk'⟩ with hm
  set p : Q := q * ι k'⁻¹ with hpd
  have hπp : π p = p' := by
    simp [hpd, map_mul, map_inv, hL.sect, h]
  have hpP : (p : G) ∈ P := (hP.mem _).2 ⟨p.2, by
    show π p ∈ P'
    rw [hπp]
    exact hp'⟩
  have hqk : (q : G) * k = p * ((kι hL m * k : K) : G) := by
    simp [hpd, hm]
  have hcp : c p = c₀ q * c' p' := by
    rw [hP.ch p (by rw [hπp]; exact hp'), hπp, hpd, c₀_ι_right hL]
  have hsec' := h2 _ hv p' hp' m
  rw [hqk, h1 _ hv' _ hpP, hcp, h, hsec', am_apply]
  have h3 : ((resRep hL ρ m⁻¹ v : fixSp K Q π c₀ ρ) : W) = ρ (kι hL m)⁻¹ (v : W) := by
    rw [resRep_coe, map_inv]
  have h4 : ρ (kι hL m * k)⁻¹ (v : W) = ρ k⁻¹ (ρ (kι hL m)⁻¹ (v : W)) := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_rev]
  rw [Submodule.coe_smul, h3, h4, map_smul, smul_smul]
end GlobalTheory.CompanionTheory.RgTransfer
