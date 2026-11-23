-- Prove2me | solution 1 for GlobalTheory.SmoothPointFamily.exists_finset_of_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:25.152152+00:00
-- url     : https://prove2.me/submissions/72fef5db-c333-4016-b198-593e79bdf403

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolomorphicSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsHolomorphicFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory GlobalTheory.SmoothPointFamily
open KaehlerDifferential
namespace GlobalTheory.SmoothPointFamily
theorem _root_.solution {A : Type} {x : A → ℂ} {U : Set (A → ℂ)} (hU : U ∈ 𝓝 x) :
    ∃ (S : Finset A) (ε : ℝ), 0 < ε ∧ ∀ y : A → ℂ, (∀ a ∈ S, ‖y a - x a‖ < ε) → y ∈ U := by
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, hI⟩ := hU
  choose δ hδ hδt using fun a => Metric.mem_nhds_iff.1 (ht a)
  have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a ∈ I, ε < δ a :=
    (Filter.eventually_all_finset I).2 fun a _ =>
      nhdsWithin_le_nhds (gt_mem_nhds (hδ a))
  obtain ⟨ε, h2, h3⟩ := (h1.and self_mem_nhdsWithin).exists
  refine ⟨I, ε, h3, fun y hy => hI fun a ha => hδt a ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  exact (hy a ha).trans (h2 a ha)
end GlobalTheory.SmoothPointFamily
