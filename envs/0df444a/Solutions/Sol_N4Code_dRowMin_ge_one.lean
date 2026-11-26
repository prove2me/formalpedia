-- Prove2me | solution 1 for N4Code.dRowMin_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:12:56.615319+00:00
-- url     : https://prove2.me/submissions/5f5bce14-a841-48fc-9c0a-9911ccec4af9

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_dRow_eq_hammingDist
import Theorems.Thm_N4Code_hammingDist_eq_zero_iff


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (S : Finset (Fin 4)) (hS : S.Nonempty)
    (t : Fin n) (y : Word n) (hcol : C t = col0) (hyt : y t = true) :
    1 ≤ dRowMin C S hS y := by
  unfold dRowMin
  have hm : (S.image (fun i => dRow C i y)).min' (hS.image (fun i => dRow C i y)) ∈
      S.image (fun i => dRow C i y) := Finset.min'_mem _ _
  rcases (Finset.mem_image.mp hm) with ⟨i, hi, hfi⟩
  rw [← hfi]
  have hd : 1 ≤ dRow C i y := by
    rw [dRow_eq_hammingDist]
    have hneq : row C i ≠ y := by
      intro h
      have : row C i t = y t := congrFun h t
      have hrowt : row C i t = false := by
        unfold row
        simp [hcol, colBit, col0]
      simp [hrowt, hyt] at this
    by_contra hle
    have h0 : hammingDist (row C i) y = 0 := by omega
    exact hneq ((hammingDist_eq_zero_iff (row C i) y).mp h0)
  omega
end N4Code
