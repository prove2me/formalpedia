-- Prove2me | solution 1 for GlobalTheory.T.ae_exists_pairGroup_smul_mem_sheared_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:21:11.818181+00:00
-- url     : https://prove2.me/submissions/6d81326f-d741-47f0-b464-5bce1448120c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AeExistsPairGroupSmulMemShearedDomain
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AeExistsPairGroupSmulMemShearedDomainStatement
import Theorems.Thm_GlobalTheory_UnfoldNormal_ae_exists_pairGroup_smul_mem_shear


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → ∀ᵐ p ∂((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)), ∃ g : GlobalTheory.UnfoldNormal.pairGroup Γ N hN, g • p ∈ GlobalTheory.UnfoldNormal.shear N '' (𝓝 ×ˢ 𝓕) := by
  first | exact @GlobalTheory.UnfoldNormal.ae_exists_pairGroup_smul_mem_shear | exact GlobalTheory.UnfoldNormal.ae_exists_pairGroup_smul_mem_shear | (intros; apply GlobalTheory.UnfoldNormal.ae_exists_pairGroup_smul_mem_shear <;> assumption)
end _root_.GlobalTheory.T
