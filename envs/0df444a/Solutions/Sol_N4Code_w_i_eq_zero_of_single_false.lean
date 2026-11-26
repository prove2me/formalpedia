-- Prove2me | solution 1 for N4Code.w_i_eq_zero_of_single_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:44.785616+00:00
-- url     : https://prove2.me/submissions/c6f2add8-004d-4f2d-9552-c6fdf1120568

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_fiber_card_eq_count
import Theorems.Thm_N4Code_w_i_eq_card_onesOn


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (i : ℕ) (t : Fin n) (y : Word n)
    (hcount : count C i = 1) (ht : colVal (C t) = i) (hyt : y t = false) :
    w_i C i y = 0 := by
  have ht' : t ∈ fiber C i := by simp [fiber, ht]
  have hcard : (fiber C i).card = 1 := by
    rw [fiber_card_eq_count, hcount]
  have hfib : fiber C i = {t} := by
    rcases Finset.card_eq_one.mp hcard with ⟨a, ha⟩
    have hat : a = t := by
      have ht'a : t ∈ ({a} : Finset (Fin n)) := by
        rw [← ha]
        exact ht'
      exact (Finset.mem_singleton.mp ht'a).symm
    rw [ha, hat]
  rw [w_i_eq_card_onesOn]
  rw [hfib]
  have hone : onesOn {t} y = ∅ := by
    ext u
    by_cases hu : u = t <;> simp [onesOn, hu, hyt]
  rw [hone]
  simp
end N4Code
