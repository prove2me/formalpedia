-- Prove2me | solution 1 for GlobalTheory.WigSh.prod_other_neighbour_raise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:09:56.872215+00:00
-- url     : https://prove2.me/submissions/27dba84c-605b-412f-a864-3cfbe2d2b632

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvSqLeWignerCoeffSqRaising

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.WigSh
namespace GlobalTheory.WigSh
theorem _root_.solution {n : ℕ} (d : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (hd : ∀ i, 0 < d i) (hl : d l = 1) :
    (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc)) * (d 0 * d (Fin.last n))
      = ∏ j : Fin n, d (l.succAbove j) := by
  have hP : ∏ i, d i = ∏ j : Fin n, d (l.succAbove j) := by
    rw [Fin.prod_univ_succAbove d l, hl, one_mul]
  have h1 := Fin.prod_univ_succ d
  have h2 := Fin.prod_univ_castSucc d
  have h3 : (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
      * ∏ j : Fin n, d (l.succAbove j) = (∏ j : Fin n, d j.succ) * ∏ j : Fin n, d j.castSucc := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold Fin.succAbove
    split_ifs
    · rfl
    · exact mul_comm _ _
  have hpos : 0 < ∏ j : Fin n, d (l.succAbove j) := Finset.prod_pos fun j _ => hd _
  apply mul_right_cancel₀ hpos.ne'
  calc _ = ((∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
      * ∏ j : Fin n, d (l.succAbove j)) * (d 0 * d (Fin.last n)) := by ring
    _ = (d 0 * ∏ j : Fin n, d j.succ) * ((∏ j : Fin n, d j.castSucc) * d (Fin.last n)) := by
      rw [h3]; ring
    _ = _ := by rw [← h1, ← h2, hP]
end GlobalTheory.WigSh
