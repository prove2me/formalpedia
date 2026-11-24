-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.eis_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:29:24.008807+00:00
-- url     : https://prove2.me/submissions/9284d69b-7e72-41b2-a605-5b139e658ade

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_cos_exists
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_sec_left
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_sec_pull
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_rep_mul

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
    (hpar : IsPar Γ' K' P' c') {ρ : K →* (W →L[ℂ] W)} (h1 : Law K P c ρ)
    (h2 : Law K' P' c' (resRep hL ρ)) {Λ : G → ℂ} {Λ' : G' → ℂ}
    (hΛ : ∀ (q : Q) (k : K), Λ ((q : G) * k) = Λ' (π q))
    (hinv : ∀ γ ∈ Γ', γ ∈ P' → ∀ x, Λ' (γ * x) = Λ' x)
    {v : fixSp K Q π c₀ ρ} (hv : v ∈ secSp K' P' c' (resRep hL ρ)) (hv' : (v : W) ∈ secSp K P c ρ)
    (q : Q) (k : K)
    (hs : Summable fun y : Cos P' Γ' =>
      Complex.exp (Λ' (rep y * π q)) • sec K' P' c' (resRep hL ρ) (rep y * π q) v) :
    eis (Γ ⊓ Q) K P c ρ Λ ((q : G) * k) v = am ρ c₀ π q k (eis Γ' K' P' c' (resRep hL ρ) Λ' (π q) v) := by
  obtain ⟨φ, hφ⟩ := cos_exists hL hP
  unfold eis
  rw [(am ρ c₀ π q k).map_tsum hs, ← φ.tsum_eq]
  refine tsum_congr (fun x => ?_)
  obtain ⟨hq, γ, hγ, hγP, h⟩ := hφ x
  have hrep : rep x ∈ Γ := (Quotient.out x).2.1
  have hcx : c₀ (rep x) = 1 := hL.par.ch.rat _ hrep hq
  rw [rep_mul hq q k rfl, hΛ, sec_pull hL hP hpar.iwa h1 h2 hv hv', map_mul, h, mul_assoc, hinv γ hγ hγP,
    sec_left hpar h2 hv hγ hγP, map_smul]
  congr 2
  simp only [am]
  rw [c₀_mul hL]
  show (c₀ (rep x) * c₀ q) • _ = _
  rw [hcx, one_mul]
end GlobalTheory.CompanionTheory.RgTransfer
