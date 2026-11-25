-- Prove2me | solution 1 for GlobalTheory.Proof.NodeGapNoncompact.gapAtLeast_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:05:38.230802+00:00
-- url     : https://prove2.me/submissions/65d6d688-987e-4b54-9877-567f89e78895

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
import Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_sign_eq

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
theorem _root_.solution (k r : ℕ) (hk : 1 ≤ k) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) :
    Formalism.QuantumDeterminants.GapAtLeast (eps48 k r) lam h ↔ NoncompactGapGe r k hk lam h := by
  rw [sign_eq k r hk]
  rfl
end GlobalTheory.Proof.NodeGapNoncompact
