-- Prove2me | solution 1 for OAI.SevenEighths.Supremum.max_normalized_signal_exponents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:12:27.085296+00:00
-- url     : https://prove2.me/submissions/7831f555-3c63-46be-a3c5-e680212b5492

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
import Theorems.Thm_OAI_SevenEighths_Supremum_max_signal_exponents

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section
namespace OAI.SevenEighths.Supremum
theorem _root_.solution (β ω σ : ℝ) :
    max (3 / 16 + ω) (β - 11 / 16 - σ) =
      β - 11 / 16 - continuationMargin β ω σ := by
  have h : (7 / 8 : ℝ) + -(11 / 16) = 3 / 16 := by norm_num
  simpa only [sub_eq_add_neg, h] using max_signal_exponents β ω σ (-(11 / 16))
end OAI.SevenEighths.Supremum
