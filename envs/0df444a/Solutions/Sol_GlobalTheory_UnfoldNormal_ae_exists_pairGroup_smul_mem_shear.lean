-- Prove2me | solution 1 for GlobalTheory.UnfoldNormal.ae_exists_pairGroup_smul_mem_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:11:35.799797+00:00
-- url     : https://prove2.me/submissions/1b47faa6-3113-4fd4-8fc3-5f8617cf76ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AeExistsPairGroupSmulMemShearedDomain
import Theorems.Thm_GlobalTheory_UnfoldNormal_measurableEmbedding_shear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Function
open scoped Pointwise
open GlobalTheory GlobalTheory.UnfoldNormal
namespace GlobalTheory.UnfoldNormal
theorem _root_.solution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → ∀ᵐ p ∂((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)), ∃ g : GlobalTheory.UnfoldNormal.pairGroup Γ N hN, g • p ∈ GlobalTheory.UnfoldNormal.shear N '' (𝓝 ×ˢ 𝓕) := by
  intro H _ _ _ _ _ _ _ _ ν _ Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 hconj 𝓕 h𝓕
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : SigmaFinite κ := inferInstance
  have hgoodn : ∀ᵐ n : N ∂κ, ∀ v : Γ, ∃ δ : Γ.subgroupOf N,
      δ • (⟨(v : H) * n * (v : H)⁻¹, hN v v.2 n n.2⟩ : N) ∈ 𝓝 := by
    rw [ae_all_iff]
    intro v
    have hc : Continuous (fun n : N => (⟨(v : H) * n * (v : H)⁻¹, hN v v.2 n n.2⟩ : N)) :=
      Continuous.subtype_mk (by fun_prop) _
    have hmp : MeasurePreserving (fun n : N => (⟨(v : H) * n * (v : H)⁻¹, hN v v.2 n n.2⟩ : N)) κ κ :=
      ⟨hc.measurable, hconj v v.2⟩
    exact hmp.quasiMeasurePreserving.ae h𝓝.ae_covers
  have hboth : ∀ᵐ p ∂(κ.prod ν), (∀ v : Γ, ∃ δ : Γ.subgroupOf N,
      δ • (⟨(v : H) * p.1 * (v : H)⁻¹, hN v v.2 p.1 p.1.2⟩ : N) ∈ 𝓝) ∧
      ∃ v : Γ, v • p.2 ∈ 𝓕 :=
    (Measure.quasiMeasurePreserving_fst.ae hgoodn).and
      (Measure.quasiMeasurePreserving_snd.ae h𝓕.ae_covers)
  rw [(measurableEmbedding_shear hNc).ae_map_iff]
  filter_upwards [hboth] with p hp
  obtain ⟨n, h⟩ := p
  obtain ⟨hn, v, hv⟩ := hp
  obtain ⟨δ, hδ⟩ := hn v
  have hδN : ((δ : N) : H) ∈ N := (δ : N).2
  have hδΓ : ((δ : N) : H) ∈ Γ := δ.2
  refine ⟨⟨(((δ : N) : H) * v, (v : H)), Γ.mul_mem hδΓ v.2, v.2, ?_⟩, ?_⟩
  · simpa using hδN
  · refine ⟨(_, v • h), ⟨hδ, hv⟩, ?_⟩
    ext
    · simp [shear, Subgroup.smul_def, Submonoid.smul_def, mul_assoc]
    · simp [shear, Subgroup.smul_def, Submonoid.smul_def]
end GlobalTheory.UnfoldNormal
