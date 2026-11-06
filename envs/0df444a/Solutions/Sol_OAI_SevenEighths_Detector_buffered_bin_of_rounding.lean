-- Prove2me | solution 1 for OAI.SevenEighths.Detector.buffered_bin_of_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:24.194199+00:00
-- url     : https://prove2.me/submissions/e3fd1612-1a99-4579-84a7-3f2dadc56e33

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
theorem _root_.solution {x y a e : ℝ}
    (hround : a ≤ x ∧ x < a + e) (hstep : y - x ≤ e) :
    a ≤ x ∧ x < a + e ∧ y < a + 2 * e := by
  exact ⟨hround.1, hround.2, by linarith [hround.2]⟩
end OAI.SevenEighths.Detector
