-- Prove2me | solution 1 for GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:01:29.159048+00:00
-- url     : https://prove2.me/submissions/d15f7d9d-a4b9-4e75-9fe8-953c130f63c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsIsAddHaarMeasureIsAddFundamentalDomainPrei

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (G H : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H] (e : G ≃+ H), Continuous e → Continuous e.symm → ∀ (Γ : AddSubgroup G) (Λ : AddSubgroup H), (∀ x, e x ∈ Λ ↔ x ∈ Γ) → ∀ (μ : Measure H) (𝓕 : Set H), μ.IsAddHaarMeasure → IsAddFundamentalDomain Λ 𝓕 μ → ∃ ν : Measure G, ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ (e ⁻¹' 𝓕) ν ∧ ∀ φ : H → ℝ, ∫ w in e ⁻¹' 𝓕, φ (e w) ∂ν = ∫ w in 𝓕, φ w ∂μ := by
  intro G H _ _ _ _ _ _ _ _ _ _ e he hes Γ Λ hΓ μ 𝓕 hμ h𝓕
  let m : G ≃ᵐ H :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving m (μ.map e.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving e (μ.map e.symm) μ := hmp
  refine ⟨μ.map e.symm, AddEquiv.isAddHaarMeasure_map μ e.symm hes (by simpa using he), ?_, ?_⟩
  · let f : Λ → Γ := fun y => ⟨e.symm y, (hΓ _).1 (by simpa using y.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, (hΓ _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  · intro φ
    exact hmp.setIntegral_preimage_emb m.measurableEmbedding φ 𝓕
end GlobalTheory
