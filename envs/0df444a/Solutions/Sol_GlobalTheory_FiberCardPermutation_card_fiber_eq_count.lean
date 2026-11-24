-- Prove2me | solution 1 for GlobalTheory.FiberCardPermutation.card_fiber_eq_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:00:44.851717+00:00
-- url     : https://prove2.me/submissions/938dba38-bda3-4801-ab25-5b1591fc9844

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPermOfOfFnPerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FiberCardPermutation
namespace GlobalTheory.FiberCardPermutation
theorem _root_.solution {α : Type} [DecidableEq α] {n : ℕ} (v : Fin n → α) (c : α) :
    Fintype.card {i : Fin n // v i = c} = Multiset.count c (List.ofFn v : Multiset α) := by
  rw [← Fin.univ_val_map, Multiset.count_map, Fintype.card_subtype]
  simp only [Finset.card, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun _ _ => eq_comm)
end GlobalTheory.FiberCardPermutation
