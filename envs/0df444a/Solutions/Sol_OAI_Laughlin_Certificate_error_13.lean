-- Prove2me | solution 1 for OAI.Laughlin.Certificate.error_13
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:25:58.093617+00:00
-- url     : https://prove2.me/submissions/127748be-8e06-4f90-9f40-fc0db590d62c

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_3_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_5_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_11_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_13_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_11_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_13_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_7_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_9_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_11_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_13_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_9_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_11_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_13_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_11_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_13_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_11_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_13_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_13_13_13

namespace OAI
namespace Laughlin.Certificate

lemma ysym_swap {α : Type*} (L M : List α) (F : α → α → ℚ) :
    (L.map fun e => (M.map fun f => F e f).sum).sum =
      (M.map fun f => (L.map fun e => F e f).sum).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [List.sum_map_add, ih]

lemma ysym_rows : ∀ row ∈ rows, ∀ e ∈ row.2.2, row.1 ≤ e.1 + e.2.1 := by
  decide +kernel

lemma ysym_entry (D r s t p j q l : ℕ) (a b : ℤ) (h1 : t ≤ p + j) (h2 : t ≤ q + l) :
    yEntry D r s t (p, j, a) (q, l, b) = yEntry D s r t (q, l, b) (p, j, a) := by
  simp only [yEntry]
  rw [show p + j + (q + l - t) = q + l + (p + j - t) by omega, Nat.add_comm s r]
  have e2 : (1 : ℤ) - 2 * ((q + l + (p + j - t) : ℕ) : ℤ) + (p : ℤ) + (q : ℤ) - (t : ℤ) + (((r + s) / 2 : ℕ) : ℤ)
      = 1 - 2 * ((q + l + (p + j - t) : ℕ) : ℤ) + (q : ℤ) + (p : ℤ) - (t : ℤ) + (((r + s) / 2 : ℕ) : ℤ) := by ring
  rw [e2]
  split_ifs <;> ring

lemma Y_symm (D r s : ℕ) : Y D r s = Y D s r := by
  unfold Y
  congr 3
  apply List.map_congr_left
  intro row hrow
  obtain ⟨t, ell, L⟩ := row
  have hL := ysym_rows _ hrow
  simp only [yRow] at hL ⊢
  rw [ysym_swap L L (fun e f => yEntry D s r t e f)]
  congr 1
  apply List.map_congr_left
  intro e he
  congr 1
  apply List.map_congr_left
  intro f hf
  obtain ⟨p, j, a⟩ := e
  obtain ⟨q, l, b⟩ := f
  exact ysym_entry D r s t p j q l a b (hL _ he) (hL _ hf)


set_option maxHeartbeats 4000000 in
theorem _root_.solution : errorRational 13 = candidateY_13 := by
  ext i j
  fin_cases i <;> fin_cases j
  · decide +kernel
  · exact (Y_symm 13 1 3).trans (OAI.Laughlin.Certificate.source_error_13_3_1.trans (by decide +kernel))
  · exact (Y_symm 13 1 5).trans (OAI.Laughlin.Certificate.source_error_13_5_1.trans (by decide +kernel))
  · exact (Y_symm 13 1 7).trans (OAI.Laughlin.Certificate.source_error_13_7_1.trans (by decide +kernel))
  · exact (Y_symm 13 1 9).trans (OAI.Laughlin.Certificate.source_error_13_9_1.trans (by decide +kernel))
  · exact (Y_symm 13 1 11).trans (OAI.Laughlin.Certificate.source_error_13_11_1.trans (by decide +kernel))
  · exact (Y_symm 13 1 13).trans (OAI.Laughlin.Certificate.source_error_13_13_1.trans (by decide +kernel))
  · exact OAI.Laughlin.Certificate.source_error_13_3_1.trans (by decide +kernel)
  · decide +kernel
  · exact (Y_symm 13 3 5).trans (OAI.Laughlin.Certificate.source_error_13_5_3.trans (by decide +kernel))
  · exact (Y_symm 13 3 7).trans (OAI.Laughlin.Certificate.source_error_13_7_3.trans (by decide +kernel))
  · exact (Y_symm 13 3 9).trans (OAI.Laughlin.Certificate.source_error_13_9_3.trans (by decide +kernel))
  · exact (Y_symm 13 3 11).trans (OAI.Laughlin.Certificate.source_error_13_11_3.trans (by decide +kernel))
  · exact (Y_symm 13 3 13).trans (OAI.Laughlin.Certificate.source_error_13_13_3.trans (by decide +kernel))
  · exact OAI.Laughlin.Certificate.source_error_13_5_1.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_5_3.trans (by decide +kernel)
  · decide +kernel
  · exact (Y_symm 13 5 7).trans (OAI.Laughlin.Certificate.source_error_13_7_5.trans (by decide +kernel))
  · exact (Y_symm 13 5 9).trans (OAI.Laughlin.Certificate.source_error_13_9_5.trans (by decide +kernel))
  · exact (Y_symm 13 5 11).trans (OAI.Laughlin.Certificate.source_error_13_11_5.trans (by decide +kernel))
  · exact (Y_symm 13 5 13).trans (OAI.Laughlin.Certificate.source_error_13_13_5.trans (by decide +kernel))
  · exact OAI.Laughlin.Certificate.source_error_13_7_1.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_7_3.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_7_5.trans (by decide +kernel)
  · decide +kernel
  · exact (Y_symm 13 7 9).trans (OAI.Laughlin.Certificate.source_error_13_9_7.trans (by decide +kernel))
  · exact (Y_symm 13 7 11).trans (OAI.Laughlin.Certificate.source_error_13_11_7.trans (by decide +kernel))
  · exact (Y_symm 13 7 13).trans (OAI.Laughlin.Certificate.source_error_13_13_7.trans (by decide +kernel))
  · exact OAI.Laughlin.Certificate.source_error_13_9_1.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_9_3.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_9_5.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_9_7.trans (by decide +kernel)
  · decide +kernel
  · exact (Y_symm 13 9 11).trans (OAI.Laughlin.Certificate.source_error_13_11_9.trans (by decide +kernel))
  · exact (Y_symm 13 9 13).trans (OAI.Laughlin.Certificate.source_error_13_13_9.trans (by decide +kernel))
  · exact OAI.Laughlin.Certificate.source_error_13_11_1.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_11_3.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_11_5.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_11_7.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_11_9.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_11_11.trans (by decide +kernel)
  · exact (Y_symm 13 11 13).trans (OAI.Laughlin.Certificate.source_error_13_13_11.trans (by decide +kernel))
  · exact OAI.Laughlin.Certificate.source_error_13_13_1.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_13_3.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_13_5.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_13_7.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_13_9.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_13_11.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_13_13_13.trans (by decide +kernel)
end Laughlin.Certificate
end OAI
