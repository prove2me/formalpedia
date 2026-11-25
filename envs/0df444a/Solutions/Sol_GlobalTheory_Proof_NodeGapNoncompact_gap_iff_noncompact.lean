-- Prove2me | solution 1 for GlobalTheory.Proof.NodeGapNoncompact.gap_iff_noncompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:10:19.550369+00:00
-- url     : https://prove2.me/submissions/cc76033a-60e0-4b60-87e1-32216b5cf90b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
import Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_gap_iff
import Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_le_sub_of_nodeGapGe
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_nodeGapGe_of_noncompactGapGe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.NodeGapNoncompact
open PI.BesselPeriodGGP GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
namespace GlobalTheory.Proof.NodeGapNoncompact
theorem _root_.solution (k r : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (hd : IsDecreasing r k hk v b) :
    LowGapGe h r b ↔ NoncompactGapGe r k hk (param r k hk v b) h := by
  rw [gap_iff]
  refine ⟨fun hg s t hne => ?_, nodeGapGe_of_noncompactGapGe r k hk v b h hd⟩
  rcases lt_trichotomy s t with hst | hst | hst
  · exact (le_sub_of_nodeGapGe r k hk v b h hd hg s t hst hne).trans (le_abs_self _)
  · exact absurd (congrArg _ hst) hne
  · rw [abs_sub_comm]
    exact (le_sub_of_nodeGapGe r k hk v b h hd hg t s hst hne.symm).trans (le_abs_self _)
end GlobalTheory.Proof.NodeGapNoncompact
