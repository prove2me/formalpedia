-- Prove2me | solution 1 for GlobalTheory.Proof.NodeGapNoncompact.interlace_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:11.368868+00:00
-- url     : https://prove2.me/submissions/8c4ce11b-9065-4c27-b6df-6f72c3175715

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_cloud
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_node
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_sign_cloud
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_sign_node
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_cloud
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_node
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.sign_cloud
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.sign_node



set_option autoImplicit false
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.NodeGapNoncompact
open PI.BesselPeriodGGP GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
namespace GlobalTheory.Proof.NodeGapNoncompact
theorem _root_.solution (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) :
    InterlacingCondition k r u v b ↔ Interlaces r k (param r k hk v b) u := by
  have hc : ∀ (i : ℕ) (hi : i < k - 1) (hi' : i < 2 * r + k + 1),
      param r k hk v b ⟨i, hi'⟩ = v ⟨i, hi⟩ := fun i hi _ => param_cloud r k hk v b ⟨i, hi⟩
  have hn : ∀ (hi' : k - 1 < 2 * r + k + 1),
      param r k hk v b ⟨k - 1, hi'⟩ = -b ⟨0, by omega⟩ :=
    fun _ => param_node r k hk v b ⟨0, by omega⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · by_cases h : i.val < k - 1
      · rw [hc i.val h]
        exact (h1 ⟨i.val, h⟩).1
      · obtain ⟨i, hi⟩ := i
        obtain rfl : i = k - 1 := by simp only at h; omega
        rw [hn]
        exact h2 hk
    · rw [hc i (by omega)]
      exact (h1 ⟨i, by omega⟩).2
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ⟨?_, ?_⟩, fun h => ?_⟩
    · have := h1 ⟨i.val, by have := i.isLt; omega⟩
      rwa [hc i.val i.isLt] at this
    · have := h2 i.val (by have := i.isLt; omega)
      rwa [hc i.val i.isLt] at this
    · have := h1 ⟨k - 1, by omega⟩
      rwa [hn] at this
end GlobalTheory.Proof.NodeGapNoncompact
