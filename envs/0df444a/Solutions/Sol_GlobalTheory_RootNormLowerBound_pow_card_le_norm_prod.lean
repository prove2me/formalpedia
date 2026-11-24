-- Prove2me | solution 1 for GlobalTheory.RootNormLowerBound.pow_card_le_norm_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:07:17.181801+00:00
-- url     : https://prove2.me/submissions/28fbbdbf-eff0-4ce1-8284-a7bd419d3255

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowCardLeNormProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RootNormLowerBound
namespace GlobalTheory.RootNormLowerBound
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) (s : Multiset ℂ)
    (h : ∀ t ∈ s, ε ≤ ‖t‖) : ε ^ Multiset.card s ≤ ‖(s.map (fun a => -a)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := h a (Multiset.mem_cons_self a s)
    have ih' := ih fun t ht => h t (Multiset.mem_cons_of_mem ht)
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, norm_neg, pow_succ,
      mul_comm (ε ^ Multiset.card s)]
    exact mul_le_mul ha ih' (by positivity) (norm_nonneg _)
end GlobalTheory.RootNormLowerBound
