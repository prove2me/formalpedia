-- Prove2me | solution 1 for GlobalTheory.QuotInt.exists_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:47:46.590807+00:00
-- url     : https://prove2.me/submissions/41c76193-8ad1-4ac7-8bff-788f71f82d45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Theorems.Thm_GlobalTheory_QuotInt_sb_right
import Theorems.Thm_GlobalTheory_QuotInt_sb_of_quot
import Theorems.Thm_GlobalTheory_QuotInt_finite_quot
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_StepData_IntM_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.QuotInt
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.QuotInt
theorem _root_.solution (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G))
    (R : Subgroup G) (Λ : (G → ℂ) → ℂ)
    (hsmul : ∀ (a : ℂ) φ, Λ (fun g => a * φ g) = a * Λ φ)
    (hcongr : ∀ φ ψ, (∀ r ∈ R, φ r = ψ r) → Λ φ = Λ ψ)
    (hpos : ∀ φ ∈ SB G, (∀ g, φ g = 0 ∨ φ g = 1) → (∃ r ∈ R, φ r = 1) → Λ φ ≠ 0)
    {f : G → ℂ} (hf : IsLocallyConstant f) {Ω : Set G} (hΩ : IsCompact Ω)
    (hs : ∀ h, f h ≠ 0 → ∃ r ∈ R, ∃ w ∈ Ω, h = r * w)
    (hright : ∀ r ∈ R, ∃ d : ℂ, d ≠ 0 ∧ (∀ φ, Λ (fun g => φ (g * r)) = d * Λ φ) ∧ ∀ h, f (r * h) = d * f h) :
    ∃ F ∈ SB G, ∀ h, f h = Λ (fun g => F (g * h)) := by
  classical
  obtain ⟨S, hS⟩ := finite_quot K ho hΩ
  let Φ : G → ℂ := fun g => if (g : G ⧸ K) ∈ S then 1 else 0
  have hΦ : Φ ∈ SB G := sb_of_quot K ho hc S (fun x => if x ∈ S then 1 else 0) (by intro x hx; simpa using hx)
  let A : G → ℂ := fun h => Λ (fun g => Φ (g * h))
  have hA : IsLocallyConstant A := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro h
    have : IsOpen ((fun y => h⁻¹ * y) ⁻¹' (K : Set G)) := ho.preimage (by fun_prop)
    filter_upwards [this.mem_nhds (x := h) (by simp [K.one_mem])] with y hy
    simp only [A, Φ]
    congr 1; ext g
    have : ((g * y : G) : G ⧸ K) = ((g * h : G) : G ⧸ K) := by
      symm; rw [QuotientGroup.eq]; simpa [mul_assoc] using hy
    rw [this]
  refine ⟨fun g => (f g / A g) * Φ g, ⟨(hf.div hA).mul hΦ.1, hΦ.2.mul_left⟩, fun h => ?_⟩
  rw [hcongr _ (fun g => (f h / A h) * Φ (g * h)), hsmul]
  · by_cases h0 : f h = 0
    · simp [h0]
    · obtain ⟨r, hr, w, hw, rfl⟩ := hs h h0
      have : A (r * w) ≠ 0 := by
        refine hpos _ (sb_right hΦ _) (fun g => ?_) ⟨r⁻¹, R.inv_mem hr, by simp [Φ, hS w hw]⟩
        simp only [Φ]; split_ifs <;> simp
      exact (div_mul_cancel₀ _ this).symm
  · intro r hr
    obtain ⟨d, hd, h1, h2⟩ := hright r hr
    have : A (r * h) = d * A h := by
      simp only [A]
      rw [← h1]; simp only [mul_assoc]
    simp only [this, h2, mul_div_mul_left _ _ hd]
end GlobalTheory.QuotInt
