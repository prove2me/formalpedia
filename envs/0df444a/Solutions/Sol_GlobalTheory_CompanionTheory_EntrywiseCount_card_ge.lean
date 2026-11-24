-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EntrywiseCount.card_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:18.493845+00:00
-- url     : https://prove2.me/submissions/bb2434a0-f398-4891-8d77-f177899069f0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdEntrywiseLe
import Theorems.Thm_GlobalTheory_CompanionTheory_EntrywiseCount_card_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EntrywiseCount
namespace GlobalTheory.CompanionTheory.EntrywiseCount
theorem _root_.solution (n r : ℕ) (hr : r ≤ n) :
    (univ.filter (fun j : Fin n => r ≤ (j : ℕ))).card = n - r := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i : Fin n => (i : ℕ) < r)
  rw [card_lt n r hr, Finset.card_univ, Fintype.card_fin] at h
  simp only [not_lt] at h
  omega
end GlobalTheory.CompanionTheory.EntrywiseCount
