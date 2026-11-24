-- Prove2me | solution 1 for GlobalTheory.RootNormBound.exists_root_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:23:22.920871+00:00
-- url     : https://prove2.me/submissions/f631f193-a0aa-48f6-bb90-232a83c3f8c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowCardLeNormProd
import Theorems.Thm_GlobalTheory_RootNormBound_pow_card_le_norm_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RootNormBound
open Polynomial
namespace GlobalTheory.RootNormBound
theorem _root_.solution {h : Polynomial ℂ} (hm : h.Monic) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ‖h.coeff 0‖ < ε ^ h.natDegree) : ∃ t : ℂ, h.IsRoot t ∧ ‖t‖ < ε := by
  by_contra hne
  push Not at hne
  have hsp : h.Splits := IsAlgClosed.splits h
  have hne0 : h ≠ 0 := hm.ne_zero
  have key := pow_card_le_norm_prod hε h.roots fun t ht => hne t ((mem_roots hne0).1 ht)
  rw [← hsp.eval_eq_prod_roots_of_monic hm 0, ← coeff_zero_eq_eval_zero,
    ← hsp.natDegree_eq_card_roots] at key
  exact absurd hc (not_lt.2 key)
end GlobalTheory.RootNormBound
