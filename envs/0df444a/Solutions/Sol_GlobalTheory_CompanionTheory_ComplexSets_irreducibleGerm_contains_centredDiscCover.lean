-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ComplexSets.irreducibleGerm_contains_centredDiscCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:55:25.883456+00:00
-- url     : https://prove2.me/submissions/be1e6805-3883-49d9-9e79-6295de58ad8c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProjectionPushforward
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_DiscCover_exists_punctured_ball_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_DiscCover_isCompact_inter_of_cut
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_DiscCover_cover_of_radii

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ComplexSets
open Metric DiscCover
namespace GlobalTheory.CompanionTheory.ComplexSets
theorem _root_.solution :
    FiniteGermProjectionOpenAt.Statement → IrreducibleGermPrimitiveForm.Statement →
    PrimitiveFormSheetedOffDiscriminant.Statement → UnbranchedProperCountConstant.Statement →
    ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)),
      IsAnalyticNear Y w → GermIrreducibleAt Y w → (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) →
      (∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
      ∃ (Y' : Set (σ → ℂ)) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ), Y' ⊆ Y ∧ IsCentredDiscCover Y' w p ρ N := by
  intro hOpen hPrim hSheet hCount σ _ Y w A hAn hIrr hIso hDom
  obtain ⟨ℓ, N0, a, δ, q, ha, hδ, hq, hδne, hp1, hsep, hcoord⟩ := hPrim σ Y w 1 A hAn hIrr hIso hDom
  obtain ⟨M, hM, hMs⟩ := hSheet σ Y w 1 A hAn hIrr hIso hDom ℓ N0 a δ q ha hδ hq hδne hp1 hsep hcoord
  obtain ⟨ρ₀, hρ₀, hδ0⟩ := exists_punctured_ball_ne_zero δ (A w) hδ hδne
  have hAn2 := hAn
  have hIso2 := hIso
  obtain ⟨Nn, k, f, hNo, hwN, hf, hYN⟩ := hAn2
  obtain ⟨W', hW', hiso⟩ := hIso2
  have hU : M ∩ Nn ∩ W' ∈ 𝓝 w := Filter.inter_mem (Filter.inter_mem hM (hNo.mem_nhds hwN)) hW'
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hU
  have hcomp : IsCompact (Y ∩ closedBall w r) :=
    isCompact_inter_of_cut hf hYN (isCompact_closedBall w r) (fun x hx => (hrU hx).1.2)
  have hS : IsCompact ((Y ∩ closedBall w r) ∩ sphere w r) := hcomp.inter_right isClosed_sphere
  have hAS : A w ∉ A '' ((Y ∩ closedBall w r) ∩ sphere w r) := by
    rintro ⟨x, ⟨⟨hxY, hxb⟩, hxs⟩, hx⟩
    have hxw := hiso x ⟨hxY, (hrU hxb).2⟩ hx
    rw [hxw, mem_sphere, dist_self] at hxs
    exact hr.ne hxs
  have hnh : (A '' ((Y ∩ closedBall w r) ∩ sphere w r))ᶜ ∈ 𝓝 (A w) :=
    (hS.image A.continuous).isClosed.isOpen_compl.mem_nhds hAS
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.mem_nhds_iff.1 hnh
  obtain ⟨N, hN⟩ := cover_of_radii hCount σ Y w A r (min ρ₀ ρ₁) hr (lt_min hρ₀ hρ₁) hIrr.1 hcomp
    (fun x hxY hd hb => hball (ball_subset_ball (min_le_right _ _) hb)
      ⟨x, ⟨⟨hxY, mem_closedBall.2 hd.le⟩, mem_sphere.2 hd⟩, rfl⟩)
    (fun x hx hxe => hiso x ⟨hx.1, (hrU hx.2).2⟩ hxe)
    (fun x hx hne hb => hMs x ⟨hx.1, (hrU hx.2).1.1⟩
      (hδ0 (A x) (ball_subset_ball (min_le_left _ _) hb) hne))
    (hOpen σ Y w 1 A hAn hIso hDom (ball w r) (ball_mem_nhds w hr))
  exact ⟨_, _, _, N, fun x hx => hx.1, hN⟩
end GlobalTheory.CompanionTheory.ComplexSets
