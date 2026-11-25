-- Prove2me | solution 1 for GlobalTheory.Proof.NodeGapNoncompact.typings_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:58.044853+00:00
-- url     : https://prove2.me/submissions/0031d57f-8e2b-4e83-ab14-f1c0a34e85cc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
import Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_lam_eq
import Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_sign_eq
import Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_interlace_iff
import Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_parity_iff
import Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_gap_iff

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
theorem _root_.solution (k r : ℕ) (hk : 1 ≤ k) :
    (∀ (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ), lam48 k r v b = param r k hk v b) ∧
    eps48 k r = sign r k hk ∧
    (∀ (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ),
      InterlacingCondition k r u v b ↔ Interlaces r k (param r k hk v b) u) ∧
    (∀ (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ),
      HalfIntegralDifference k r u v b ↔ Parity r k (param r k hk v b) u) ∧
    (∀ (h : ℝ) (b : Fin (2 * r + 2) → ℝ), LowGapGe h r b ↔ NodeGapGe r b h) :=
  ⟨lam_eq k r hk, sign_eq k r hk, interlace_iff k r hk, parity_iff k r hk,
    fun h b => gap_iff h r b⟩
end GlobalTheory.Proof.NodeGapNoncompact
