-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ComplexSets.DiscCover.exists_punctured_ball_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:04.553995+00:00
-- url     : https://prove2.me/submissions/7386207a-889c-4db3-86f6-1275f9de55d8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProjectionPushforward
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_DiscCover_const_coord
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_DiscCover_line_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_DiscCover_line_dist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ComplexSets GlobalTheory.CompanionTheory.ComplexSets.DiscCover
open Metric
namespace GlobalTheory.CompanionTheory.ComplexSets.DiscCover
theorem _root_.solution (δ : (Fin 1 → ℂ) → ℂ) (c : Fin 1 → ℂ) (hδ : AnalyticAt ℂ δ c)
    (hne : ¬ ∀ᶠ y in 𝓝 c, δ y = 0) : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ y ∈ ball c ρ₀, y ≠ c → δ y ≠ 0 := by
  set e := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  have hF : AnalyticAt ℂ (fun t : ℂ => δ (fun _ => t)) (c 0) := by
    have h1 : AnalyticAt ℂ δ (e.symm (c 0)) := by
      have h2 : e.symm (c 0) = c := const_coord c
      rw [h2]
      exact hδ
    exact h1.comp (e.symm.analyticAt _)
  rcases hF.eventually_eq_zero_or_eventually_ne_zero with h0 | h1
  · exfalso
    apply hne
    have ht : Tendsto (fun y : Fin 1 → ℂ => y 0) (𝓝 c) (𝓝 (c 0)) := (continuous_apply 0).tendsto c
    filter_upwards [ht h0] with y hy
    have hy' : δ (fun _ => y 0) = 0 := hy
    rwa [const_coord] at hy'
  · obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h1)
    refine ⟨ε, hε, fun y hy hyc => ?_⟩
    have h2 := h (y := y 0) (by simpa [line_dist] using mem_ball.1 hy)
      (fun h3 => hyc (line_ext h3))
    rwa [const_coord] at h2
end GlobalTheory.CompanionTheory.ComplexSets.DiscCover
