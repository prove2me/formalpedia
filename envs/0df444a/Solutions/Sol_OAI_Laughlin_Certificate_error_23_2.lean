-- Prove2me | solution 2 for OAI.Laughlin.Certificate.error_23
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:13:28.608863+00:00
-- url     : https://prove2.me/submissions/0103b87b-9444-4dcc-bc6c-3152f43789ac

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_1
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_3_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_5_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_7_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_9_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_11_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_13_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_15_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_17_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_19_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_21_23
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_3
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_5
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_7
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_9
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_11
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_13
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_15
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_17
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_19
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_21
import Theorems.Thm_OAI_Laughlin_Certificate_source_error_23_23_23

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


theorem _root_.solution : errorRational 23 = candidateY_23 := by
  ext i j
  fin_cases i <;> fin_cases j
  · decide +kernel
  · exact (Y_symm 23 1 3).trans (OAI.Laughlin.Certificate.source_error_23_3_1.trans (by decide +kernel))
  · exact (Y_symm 23 1 5).trans (OAI.Laughlin.Certificate.source_error_23_5_1.trans (by decide +kernel))
  · exact (Y_symm 23 1 7).trans (OAI.Laughlin.Certificate.source_error_23_7_1.trans (by decide +kernel))
  · exact (Y_symm 23 1 9).trans (OAI.Laughlin.Certificate.source_error_23_9_1.trans (by decide +kernel))
  · exact (Y_symm 23 1 11).trans (OAI.Laughlin.Certificate.source_error_23_11_1.trans (by decide +kernel))
  · exact (Y_symm 23 1 13).trans (OAI.Laughlin.Certificate.source_error_23_13_1.trans (by decide +kernel))
  · exact (Y_symm 23 1 15).trans (OAI.Laughlin.Certificate.source_error_23_15_1.trans (by decide +kernel))
  · exact (Y_symm 23 1 17).trans (OAI.Laughlin.Certificate.source_error_23_17_1.trans (by decide +kernel))
  · exact (Y_symm 23 1 19).trans (OAI.Laughlin.Certificate.source_error_23_19_1.trans (by decide +kernel))
  · exact (Y_symm 23 1 21).trans (OAI.Laughlin.Certificate.source_error_23_21_1.trans (by decide +kernel))
  · exact (Y_symm 23 1 23).trans (OAI.Laughlin.Certificate.source_error_23_23_1.trans (by decide +kernel))
  · exact OAI.Laughlin.Certificate.source_error_23_3_1.trans (by decide +kernel)
  · decide +kernel
  · exact (Y_symm 23 3 5).trans (OAI.Laughlin.Certificate.source_error_23_5_3.trans (by decide +kernel))
  · exact (Y_symm 23 3 7).trans (OAI.Laughlin.Certificate.source_error_23_7_3.trans (by decide +kernel))
  · exact (Y_symm 23 3 9).trans (OAI.Laughlin.Certificate.source_error_23_9_3.trans (by decide +kernel))
  · exact (Y_symm 23 3 11).trans (OAI.Laughlin.Certificate.source_error_23_11_3.trans (by decide +kernel))
  · exact (Y_symm 23 3 13).trans (OAI.Laughlin.Certificate.source_error_23_13_3.trans (by decide +kernel))
  · exact (Y_symm 23 3 15).trans (OAI.Laughlin.Certificate.source_error_23_15_3.trans (by decide +kernel))
  · exact (Y_symm 23 3 17).trans (OAI.Laughlin.Certificate.source_error_23_17_3.trans (by decide +kernel))
  · exact OAI.Laughlin.Certificate.source_error_23_3_19.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_3_21.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_3_23.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_5_1.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_5_3.trans (by decide +kernel)
  · decide +kernel
  · exact (Y_symm 23 5 7).trans (OAI.Laughlin.Certificate.source_error_23_7_5.trans (by decide +kernel))
  · exact (Y_symm 23 5 9).trans (OAI.Laughlin.Certificate.source_error_23_9_5.trans (by decide +kernel))
  · exact OAI.Laughlin.Certificate.source_error_23_5_11.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_5_13.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_5_15.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_5_17.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_5_19.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_5_21.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_5_23.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_7_1.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_7_3.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_7_5.trans (by decide +kernel)
  · decide +kernel
  · exact (Y_symm 23 7 9).trans (OAI.Laughlin.Certificate.source_error_23_9_7.trans (by decide +kernel))
  · exact OAI.Laughlin.Certificate.source_error_23_7_11.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_7_13.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_7_15.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_7_17.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_7_19.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_7_21.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_7_23.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_9_1.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_9_3.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_9_5.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_9_7.trans (by decide +kernel)
  · decide +kernel
  · exact OAI.Laughlin.Certificate.source_error_23_9_11.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_9_13.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_9_15.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_9_17.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_9_19.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_9_21.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_9_23.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_11_1.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_11_3.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_11_5.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_11_7.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_11_9.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_11_11.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_11_13.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_11_15.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_11_17.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_11_19.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_11_21.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_11_23.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_13_1.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_13_3.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_13_5.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_13_7.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_13_9.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_13_11.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_13_13.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_13_15.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_13_17.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_13_19.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_13_21.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_13_23.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_15_1.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_15_3.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_15_5.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_15_7.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_15_9.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_15_11.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_15_13.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_15_15.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_15_17.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_15_19.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_15_21.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_15_23.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_17_1.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_17_3.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_17_5.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_17_7.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_17_9.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_17_11.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_17_13.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_17_15.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_17_17.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_17_19.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_17_21.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_17_23.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_19_1.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_19_3.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_19_5.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_19_7.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_19_9.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_19_11.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_19_13.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_19_15.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_19_17.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_19_19.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_19_21.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_19_23.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_21_1.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_21_3.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_21_5.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_21_7.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_21_9.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_21_11.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_21_13.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_21_15.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_21_17.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_21_19.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_21_21.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_21_23.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_23_1.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_23_3.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_23_5.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_23_7.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_23_9.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_23_11.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_23_13.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_23_15.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_23_17.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_23_19.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_23_21.trans (by decide +kernel)
  · exact OAI.Laughlin.Certificate.source_error_23_23_23.trans (by decide +kernel)
end Laughlin.Certificate
end OAI
