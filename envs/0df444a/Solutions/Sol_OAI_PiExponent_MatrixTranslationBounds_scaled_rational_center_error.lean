-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.scaled_rational_center_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T08:57:13.518303+00:00
-- url     : https://prove2.me/submissions/2f8cb7e3-f45b-4f4b-af00-2b5de387239c

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OAI.PiExponent OAI.PiExponent.MatrixArithmetic

/-!
The scaled complex centre error has norm twice the scale times the
absolute rational approximation error. The proof includes zero scales.
-/
theorem solution {m : ℕ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (j : ℕ) (i : Fin m)
    (hq : 1 ≤ q i) :
    ‖(j : ℂ) * (MatrixArithmetic.rationalCenters p q i - logarithmicPeriod)‖ ≤
      (2 * (j : ℝ)) * |Real.pi - (p i : ℝ) / (q i : ℝ)| := by
  have hdiff :
      (p i : ℂ) / (q i : ℂ) - (Real.pi : ℂ) =
        ((((p i : ℝ) / (q i : ℝ)) - Real.pi : ℝ) : ℂ) := by
    push_cast
    rfl
  have hcenter :
      MatrixArithmetic.rationalCenters p q i - logarithmicPeriod =
        (2 : ℂ) * Complex.I * ((p i : ℂ) / (q i : ℂ) - (Real.pi : ℂ)) := by
    simp [MatrixArithmetic.rationalCenters, logarithmicPeriod]
    ring
  have hnormdiff :
      ‖(p i : ℂ) / (q i : ℂ) - (Real.pi : ℂ)‖ =
        |(p i : ℝ) / (q i : ℝ) - Real.pi| := by
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
  have habs :
      |(p i : ℝ) / (q i : ℝ) - Real.pi| =
        |Real.pi - (p i : ℝ) / (q i : ℝ)| := by
    rw [← abs_neg]
    congr 1
    ring
  calc
    ‖(j : ℂ) * (MatrixArithmetic.rationalCenters p q i - logarithmicPeriod)‖ =
        (j : ℝ) * (2 * |(p i : ℝ) / (q i : ℝ) - Real.pi|) := by
      rw [hcenter, norm_mul, norm_mul, norm_mul,
        Complex.norm_natCast, Complex.norm_ofNat, Complex.norm_I, hnormdiff]
      ring
    _ = (2 * (j : ℝ)) * |Real.pi - (p i : ℝ) / (q i : ℝ)| := by
      rw [habs]
      ring
    _ ≤ _ := le_rfl
