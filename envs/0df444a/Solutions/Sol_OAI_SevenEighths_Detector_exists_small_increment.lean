-- Prove2me | solution 1 for OAI.SevenEighths.Detector.exists_small_increment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:53:41.358914+00:00
-- url     : https://prove2.me/submissions/095e1030-b08f-44b0-944c-c6a4e22b3fb8

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Detector
namespace OAI.SevenEighths.Detector
theorem _root_.solution (M : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {lo hi e : ℝ} (hlo : lo ≤ M 0) (hhi : M n ≤ hi)
    (hwidth : hi - lo ≤ n * e) :
    ∃ i < n, M (i + 1) - M i ≤ e := by
  by_contra h
  have hinc : ∀ i ∈ Finset.range n, e < M (i + 1) - M i := by
    intro i hi
    exact lt_of_not_ge (fun hle => h ⟨i, Finset.mem_range.mp hi, hle⟩)
  have hs := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn)) hinc
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_range_sub] at hs
  linarith
end OAI.SevenEighths.Detector
