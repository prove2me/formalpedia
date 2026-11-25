-- Prove2me | solution 1 for GlobalTheory.Proof.NodeGapNoncompact.parity_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:56:54.523275+00:00
-- url     : https://prove2.me/submissions/b2ba00ac-7e27-4b0a-b7c3-992572f139e0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
import Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_lam_eq

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
theorem _root_.solution (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) :
    HalfIntegralDifference k r u v b ↔ Parity r k (param r k hk v b) u := by
  unfold HalfIntegralDifference Parity
  rw [lam_eq k r hk]
  constructor
  · intro h s i
    obtain ⟨j, hj⟩ := h i s
    exact ⟨-j - 1, by push_cast; linarith⟩
  · intro h i s
    obtain ⟨j, hj⟩ := h s i
    exact ⟨-j - 1, by push_cast; linarith⟩
end GlobalTheory.Proof.NodeGapNoncompact
