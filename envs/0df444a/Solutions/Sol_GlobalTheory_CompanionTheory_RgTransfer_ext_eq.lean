-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.ext_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:29:26.679482+00:00
-- url     : https://prove2.me/submissions/28b5f79e-92d9-4f92-b6b4-25977d10d430

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_am_move
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_qk_spec

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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W))
    {F : G' → E →L[ℂ] fixSp K Q π c₀ ρ} (hF : Equi hL ρ F) (q : Q) (k : K) :
    ext hL ρ F ((q : G) * k) = (am ρ c₀ π q k).comp (F (π q)) := by
  set g : G := (q : G) * k with hg
  have hs := qk_spec hL g
  set q₁ := qOf hL g with hq₁
  set k₁ := kOf hL g with hk₁
  set r : K := k * k₁⁻¹ with hr
  have hrv : (r : G) = ((q⁻¹ * q₁ : Q) : G) := by
    have : (q : G) * k = q₁ * k₁ := hs
    simp only [hr, Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, this]
    group
  have hrQ : (r : G) ∈ Q := by
    rw [hrv]
    exact Subtype.property _
  have hq₁' : q₁ = q * ⟨r, hrQ⟩ := by
    apply Subtype.ext
    have : (⟨r, hrQ⟩ : Q) = q⁻¹ * q₁ := Subtype.ext hrv
    rw [this]
    simp
  have hk₁' : k₁ = r⁻¹ * k := by
    simp [hr]
  ext x
  show am ρ c₀ π q₁ k₁ (F (π q₁) x) = am ρ c₀ π q k (F (π q) x)
  rw [← am_move hL ρ q k r hrQ (F (π q) x)]
  have := hF (π q) ⟨π ⟨r, hrQ⟩, hL.πK ⟨r, hrQ⟩ r.2⟩ x
  rw [← this, hq₁', ← hk₁', map_mul]
end GlobalTheory.CompanionTheory.RgTransfer
