-- Prove2me | solution 1 for GlobalTheory.KaUnique.sign_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:29:50.753727+00:00
-- url     : https://prove2.me/submissions/eb78305a-d124-460b-bbd9-93726af0afb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignSwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KaUnique
namespace GlobalTheory.KaUnique
theorem _root_.solution {R : Type} [CommRing R] {g : ℕ} (P : Finset (Fin g)) {i i' : Fin g} (hi : i ∉ P) (hi' : i' ∉ P)
    (hne : i ≠ i') :
    ((-1 : R) ^ (P.filter (· < i)).card * (-1) ^ ((insert i P).filter (· < i')).card) +
      ((-1 : R) ^ (P.filter (· < i')).card * (-1) ^ ((insert i' P).filter (· < i)).card) = 0 := by
  rw [Finset.filter_insert, Finset.filter_insert]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [if_pos h, if_neg (not_lt.2 h.le), Finset.card_insert_of_notMem (fun hh => hi (Finset.mem_filter.1 hh).1)]
    ring
  · rw [if_pos h, if_neg (not_lt.2 h.le), Finset.card_insert_of_notMem (fun hh => hi' (Finset.mem_filter.1 hh).1)]
    ring
end GlobalTheory.KaUnique
