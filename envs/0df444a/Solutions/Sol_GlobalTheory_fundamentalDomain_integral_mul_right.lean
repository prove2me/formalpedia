-- Prove2me | solution 1 for GlobalTheory.fundamentalDomain_integral_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:58:53.80921+00:00
-- url     : https://prove2.me/submissions/272d4f14-e55a-44f1-bd6f-f587f467df32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FundamentalDomainIntegralMulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G : Type} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G) (f : G → ℂ) (a : G)
    (h : IsFundamentalDomain Γ 𝓕 μ) (hf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    (IntegrableOn f 𝓕 μ ↔ IntegrableOn (fun g => f (g * a)) 𝓕 μ) ∧
      ∫ g in 𝓕, f (g * a) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  have hmp : MeasurePreserving (fun g : G => g * a) μ μ := measurePreserving_mul_right μ a
  have hme : MeasurableEmbedding (fun g : G => g * a) := measurableEmbedding_mulRight a
  have h' : IsFundamentalDomain Γ ((fun g : G => g * a) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv (e := id) hmp.quasiMeasurePreserving Function.bijective_id
      (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have hfa : ∀ (γ : Γ) (x : G), (fun g => f (g * a)) (γ • x) = (fun g => f (g * a)) x := by
    intro γ x
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
    exact hf γ γ.2 _
  refine ⟨?_, ?_⟩
  · rw [h.integrableOn_iff h' (f := fun g => f (g * a)) hfa]
    exact (hmp.integrableOn_comp_preimage hme (f := f) (s := 𝓕)).symm
  · rw [h.setIntegral_eq h' (f := fun g => f (g * a)) hfa]
    exact hmp.setIntegral_preimage_emb hme f 𝓕
end GlobalTheory
