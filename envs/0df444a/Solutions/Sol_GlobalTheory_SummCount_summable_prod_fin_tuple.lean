-- Prove2me | solution 1 for GlobalTheory.SummCount.summable_prod_fin_tuple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:58:43.806827+00:00
-- url     : https://prove2.me/submissions/73ee71da-5b69-433a-af98-80622e508e2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SummableRpowOfFibreCardLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummCount
namespace GlobalTheory.SummCount
theorem _root_.solution {α : Type} {g : α → ℝ} (hg : Summable g) (h0 : ∀ a, 0 ≤ g a)
    (N : ℕ) : Summable fun x : Fin N → α => ∏ i, g (x i) := by
  induction N with
  | zero => exact .of_finite
  | succ N ih =>
    have h := hg.mul_of_nonneg ih h0 fun x => Finset.prod_nonneg fun i _ => h0 _
    rw [← (Fin.consEquiv fun _ : Fin (N + 1) => α).summable_iff]
    refine h.congr fun p => ?_
    simp [Fin.prod_univ_succ, Fin.consEquiv]
end GlobalTheory.SummCount
