-- Prove2me | solution 1 for GlobalTheory.prod_affine_polyMap_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:49.950731+00:00
-- url     : https://prove2.me/submissions/142599a6-593f-4b43-9af6-3c309e8a79e8

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QdetPolyMapMonic
import Theorems.Thm_GlobalTheory_affine_mul_polyMap_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] (t : ℕ) (p q : Fin t → A) :
    ∃ c : ℕ → A, c t = (List.ofFn p).prod ∧ ∀ u : ℂ, (List.ofFn fun k => u • p k + q k).prod
      = ∑ i ∈ range (t + 1), u ^ i • c i := by
  induction t with
  | zero => exact ⟨fun _ => 1, by simp, fun u => by simp⟩
  | succ t ih =>
    obtain ⟨c, hct, hc⟩ := ih (fun k => p k.succ) (fun k => q k.succ)
    obtain ⟨c', hct', hc'⟩ := affine_mul_polyMap_top t (p 0) (q 0) c
    refine ⟨c', ?_, fun u => ?_⟩
    · rw [hct', hct, List.ofFn_succ, List.prod_cons]
    · rw [List.ofFn_succ, List.prod_cons, hc u, hc' u]
end GlobalTheory
