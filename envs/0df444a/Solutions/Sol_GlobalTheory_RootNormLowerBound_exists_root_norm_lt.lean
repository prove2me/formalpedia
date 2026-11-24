-- Prove2me | solution 1 for GlobalTheory.RootNormLowerBound.exists_root_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:23:26.349087+00:00
-- url     : https://prove2.me/submissions/80469b12-bf39-47d4-b8ac-4faca080bf7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowCardLeNormProd
import Theorems.Thm_GlobalTheory_RootNormLowerBound_pow_card_le_norm_prod

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
theorem _root_.solution {F : Polynomial ℂ} (hF : Polynomial.Monic F) {ε : ℝ}
    (hε : (0 : ℝ) < ε) (h0 : ‖Polynomial.coeff F (0 : ℕ)‖ < ε ^ Polynomial.natDegree F) :
    ∃ (t : ℂ), Polynomial.IsRoot F t ∧ ‖t‖ < ε := by
  by_contra hcon
  have hall : ∀ t ∈ F.roots, ε ≤ ‖t‖ := fun t ht =>
    le_of_not_gt fun hlt => hcon ⟨t, (Polynomial.mem_roots hF.ne_zero).1 ht, hlt⟩
  have h1 := pow_card_le_norm_prod hε F.roots hall
  have hc : F.coeff 0 = (F.roots.map fun a => -a).prod := by
    rw [(IsAlgClosed.splits F).coeff_zero_eq_prod_roots_of_monic hF, Multiset.prod_map_neg,
      IsAlgClosed.card_roots_eq_natDegree]
  rw [IsAlgClosed.card_roots_eq_natDegree, ← hc] at h1
  linarith
end GlobalTheory.RootNormLowerBound
