-- Prove2me | solution 1 for HighDimProb.RandomMatrices.error_correcting_code_guarantee
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:05:12.773494+00:00
-- url     : https://prove2.me/submissions/5c88403c-4399-44b5-88e3-15d259daf97b

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_hammingDist
import Definitions.Def_HighDimProb_RandomMatrices_IsErrorCorrectingCode

namespace HighDimProb.RandomMatrices

theorem aux_eccg_hd_le {n : ℕ} (x y : Fin n → Bool) : hammingDist x y ≤ n := by
  unfold hammingDist
  calc (Finset.univ.filter (fun i => x i ≠ y i)).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_filter_le _ _
    _ = n := by simp

theorem aux_eccg_logb_nonpos :
    Real.logb 2 (Real.exp 1 * ((1 : ℕ) : ℝ) / (2 * ((2 : ℕ) : ℝ))) ≤ 0 := by
  apply Real.logb_nonpos (by norm_num)
  · positivity
  · have := Real.exp_one_lt_d9
    push_cast
    rw [div_le_one (by norm_num)]
    linarith

end HighDimProb.RandomMatrices

open HighDimProb.RandomMatrices

theorem solution : ¬ (∀ (k n r : ℕ) (hk : 0 < k) (hn : 0 < n) (hr : 0 < r)
    (h : (n : ℝ) ≥ (k : ℝ) + 2 * (r : ℝ) * Real.logb 2 (Real.exp 1 * (n : ℝ) / (2 * (r : ℝ)))),
    ∃ E : (Fin k → Bool) → (Fin n → Bool), ∃ D : (Fin n → Bool) → (Fin k → Bool),
      IsErrorCorrectingCode (r := r) E D) := by
  intro H
  have hl := aux_eccg_logb_nonpos
  obtain ⟨E, D, hED⟩ := H 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by
    have : ((2 : ℕ) : ℝ) * 0 ≥ 2 * ((2 : ℕ) : ℝ) * Real.logb 2 (Real.exp 1 * ((1 : ℕ) : ℝ) / (2 * ((2 : ℕ) : ℝ))) := by
      push_cast at hl ⊢
      nlinarith
    push_cast at this ⊢
    linarith)
  let y : Fin 1 → Bool := fun _ => false
  have h1 := hED (fun _ => false) y (le_trans (aux_eccg_hd_le _ _) (by norm_num))
  have h2 := hED (fun _ => true) y (le_trans (aux_eccg_hd_le _ _) (by norm_num))
  have := congrFun (h1.symm.trans h2) 0
  simp at this
