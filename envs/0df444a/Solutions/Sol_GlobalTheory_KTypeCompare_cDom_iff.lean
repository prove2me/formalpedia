-- Prove2me | solution 1 for GlobalTheory.KTypeCompare.cDom_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:04:20.899926+00:00
-- url     : https://prove2.me/submissions/afc0f83c-2c23-4c22-b491-4555eb9bfbd3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus
import Theorems.Thm_GlobalTheory_KTypeCompare_root_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.KTypeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {n : ℕ}
namespace GlobalTheory.KTypeCompare
theorem _root_.solution (ε : Fin n → Bool) (ω Λ : Fin n → ℝ) :
    PI.UpqRep.CDom ε ω Λ ↔ HarishChandraRootData.CptLE ε ω Λ := by
  unfold PI.UpqRep.CDom HarishChandraRootData.CptLE
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨fun x => c x.1 x.2, ?_⟩
    rw [h, ← Fintype.sum_prod_type', HarishChandraRootData.cptPairs, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rfl
    · have h0 : c x.1 x.2 = 0 := by
        by_contra h0
        exact hx (hc _ _ h0)
      simp [h0]
  · rintro ⟨c, h⟩
    refine ⟨fun a b => if a < b ∧ ε a = ε b then c (a, b) else 0, ?_, ?_⟩
    · intro a b hab
      by_contra hn
      exact hab (if_neg hn)
    · rw [h, ← Fintype.sum_prod_type', HarishChandraRootData.cptPairs, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x.1 < x.2 ∧ ε x.1 = ε x.2
      · simp [if_pos hx, root_eq]
      · simp [if_neg hx]
end GlobalTheory.KTypeCompare
