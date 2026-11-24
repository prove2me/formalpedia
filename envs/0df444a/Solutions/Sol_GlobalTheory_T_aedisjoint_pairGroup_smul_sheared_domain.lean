-- Prove2me | solution 1 for GlobalTheory.T.aedisjoint_pairGroup_smul_sheared_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:21:12.552185+00:00
-- url     : https://prove2.me/submissions/b3ded481-2550-490b-9bc2-f1abc8c15dbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AedisjointPairGroupSmulShearedDomain
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AedisjointPairGroupSmulShearedDomainStatement
import Theorems.Thm_GlobalTheory_UnfoldNormal_aedisjoint_pairGroup_smul_shear_image


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
theorem _root_.solution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → Pairwise (AEDisjoint ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)) on fun g : GlobalTheory.UnfoldNormal.pairGroup Γ N hN => g • (GlobalTheory.UnfoldNormal.shear N '' (𝓝 ×ˢ 𝓕))) := by
  first | exact @GlobalTheory.UnfoldNormal.aedisjoint_pairGroup_smul_shear_image | exact GlobalTheory.UnfoldNormal.aedisjoint_pairGroup_smul_shear_image | (intros; apply GlobalTheory.UnfoldNormal.aedisjoint_pairGroup_smul_shear_image <;> assumption)
end _root_.GlobalTheory.T
