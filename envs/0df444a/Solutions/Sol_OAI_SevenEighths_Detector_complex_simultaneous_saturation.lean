-- Prove2me | solution 1 for OAI.SevenEighths.Detector.complex_simultaneous_saturation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:42.990941+00:00
-- url     : https://prove2.me/submissions/09fec4c3-cb25-4f18-a81f-2d16f9090545

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector
import Theorems.Thm_OAI_SevenEighths_Detector_simultaneous_saturation

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Detector
namespace OAI.SevenEighths.Detector
theorem _root_.solution {U δ r m ε : ℝ} {M S : ℂ}
    (hU : 1 < U) (hδ : (1 / 50 : ℝ) ≤ δ) (hε : 0 ≤ ε)
    (hprod : U ^ (δ * (r + m) - ε) ≤ ‖M * S‖ ^ 2)
    (hupperM : ‖M‖ ^ 2 ≤ U ^ (δ * r + ε))
    (hupperS : ‖S‖ ^ 2 ≤ U ^ (δ * min m (1 - m) + ε)) :
    m ≤ 1 / 2 + 75 * ε ∧
      U ^ (δ * r - 2 * ε) ≤ ‖M‖ ^ 2 ∧
      U ^ (δ * m - 2 * ε) ≤ ‖S‖ ^ 2 := by
  apply simultaneous_saturation hU hδ hε (sq_nonneg _) (sq_nonneg _)
    _ hupperM hupperS
  simpa only [norm_mul, mul_pow] using hprod
end OAI.SevenEighths.Detector
