-- Prove2me | solution 1 for GlobalTheory.WigSh.Model.factor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:05:50.832386+00:00
-- url     : https://prove2.me/submissions/6aed7c06-3bb2-4a9b-8571-d9309e6a7c58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg
import Theorems.Thm_GlobalTheory_WigSh_Model_Box_strictAnti

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
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.Model
namespace GlobalTheory.WigSh.Model
theorem _root_.solution {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M)
    (l : Fin (n + 1)) (j : Fin n) (e : ℤ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 ≤ ((M j : ℝ) - e - L l) / ((L (l.succAbove j) : ℝ) - L l) := by
  have hA := h.strictAnti
  have he0' : (0 : ℝ) ≤ e := by exact_mod_cast he0
  have he1' : (e : ℝ) ≤ 1 := by exact_mod_cast he1
  rcases lt_or_ge (Fin.castSucc j) l with hj | hj
  · rw [Fin.succAbove_of_castSucc_lt l j hj]
    have h1 : L l ≤ L j.succ := hA.antitone (Fin.castSucc_lt_iff_succ_le.mp hj)
    have h2 : L l < L j.castSucc := hA hj
    have h3 := (h j).1
    have h4 : (L l : ℝ) + 1 ≤ M j := by exact_mod_cast (by omega : L l + 1 ≤ M j)
    have h5 : (L l : ℝ) < L j.castSucc := by exact_mod_cast h2
    apply div_nonneg <;> linarith
  · rw [Fin.succAbove_of_le_castSucc l j hj]
    have h1 : L j.castSucc ≤ L l := hA.antitone hj
    have h2 : L j.succ < L l := hA (lt_of_le_of_lt hj Fin.castSucc_lt_succ)
    have h4 : (M j : ℝ) ≤ L l := by exact_mod_cast le_trans (h j).2 h1
    have h5 : (L j.succ : ℝ) < L l := by exact_mod_cast h2
    apply div_nonneg_of_nonpos <;> linarith
end GlobalTheory.WigSh.Model
