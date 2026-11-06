-- Prove2me | solution 1 for OAI.SevenEighths.Detector.exists_buffered_bin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:27.396549+00:00
-- url     : https://prove2.me/submissions/4b4dd654-84b2-4694-9bd7-f9bdd900f4c6

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector
import Theorems.Thm_OAI_SevenEighths_Detector_exists_small_increment
import Theorems.Thm_OAI_SevenEighths_Detector_exists_grid_rounding

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Detector
namespace OAI.SevenEighths.Detector
theorem _root_.solution (M : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {e : ℝ} (he : 0 < e)
    (hbound : ∀ j ≤ n, (51 / 100 : ℝ) ≤ M j ∧ M j ≤ 1)
    (hwidth : (49 / 100 : ℝ) ≤ n * e) :
    ∃ i < n, ∃ k : ℕ,
      let a : ℝ := 51 / 100 + e * k
      a ≤ 1 ∧ a ≤ M i ∧ M i < a + e ∧ M (i + 1) < a + 2 * e := by
  obtain ⟨i, hi, hstep⟩ := exists_small_increment M hn (e := e)
    (hbound 0 (Nat.zero_le _)).1 (hbound n le_rfl).2 (by linarith)
  obtain ⟨k, hklo, hkhi⟩ := exists_grid_rounding he (hbound i hi.le).1
  refine ⟨i, hi, k, ?_, hklo, hkhi, ?_⟩
  · exact hklo.trans (hbound i hi.le).2
  · linarith
end OAI.SevenEighths.Detector
