-- Prove2me | solution 1 for GlobalTheory.LagrangeInterpolationExistence.exists_sum_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:35:21.272678+00:00
-- url     : https://prove2.me/submissions/c301b8b6-9e00-4d60-912a-576e033ab96f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInterpolation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LagrangeInterpolationExistence
namespace GlobalTheory.LagrangeInterpolationExistence
theorem _root_.solution {X M : Type} [AddCommGroup M] [Module ℂ M] (S : Finset X) (a : X → M)
    (y : X) (b : M) :
    ∃ (T : Finset X) (u : X → M), ∀ c : X → ℂ,
      ∑ x ∈ T, c x • u x = ∑ x ∈ S, c x • a x + c y • b := by
  classical
  refine ⟨insert y S, fun x => if x = y then (if y ∈ S then a y + b else b) else a x, fun c => ?_⟩
  by_cases hy : y ∈ S
  · rw [Finset.insert_eq_of_mem hy, ← Finset.add_sum_erase S _ hy, ← Finset.add_sum_erase S _ hy]
    simp only [if_pos rfl, hy, if_true, ite_true, smul_add]
    rw [Finset.sum_congr rfl (fun x hx => by rw [if_neg (Finset.ne_of_mem_erase hx)])]
    abel
  · rw [Finset.sum_insert hy]
    simp only [if_neg hy, eq_self_iff_true, if_true, ite_true]
    rw [Finset.sum_congr rfl (fun x hx => by rw [if_neg (fun (h : x = y) => hy (h ▸ hx))]), add_comm]
end GlobalTheory.LagrangeInterpolationExistence
