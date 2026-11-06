-- Prove2me | solution 1 for OAI.SevenEighths.Detector.inverse_length_of_saturation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:39.408826+00:00
-- url     : https://prove2.me/submissions/7dd5e8f2-8d2d-4ace-9491-cb3a943950db

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
theorem _root_.solution {r m t ε κ : ℝ}
    (hsupport : t - κ ≤ r + m) (hplain : m ≤ 1 / 2 + 75 * ε) :
    t - 1 / 2 - 75 * ε - κ ≤ r := by linarith
end OAI.SevenEighths.Detector
