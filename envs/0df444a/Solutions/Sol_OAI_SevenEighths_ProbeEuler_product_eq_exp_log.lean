-- Prove2me | solution 1 for OAI.SevenEighths.ProbeEuler.product_eq_exp_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:53:22.730249+00:00
-- url     : https://prove2.me/submissions/0718a0e0-c93e-4c4e-b61c-094ad1b3913e

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_CorrectionBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_NormalProduct
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_factor_ne_zero_of_defect
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_log_summable_of_defect

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler
namespace OAI.SevenEighths.ProbeEuler
theorem _root_.solution {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2) :
    (∏' i, F i) = Complex.exp (∑' i, Complex.log (F i)) := by
  apply HasProd.tprod_eq
  apply ((log_summable_of_defect F b hb hF hhalf).of_norm.hasSum.cexp).congr
  intro s
  apply Finset.prod_congr rfl
  intro i hi
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hF i).trans (hhalf i)))
end OAI.SevenEighths.ProbeEuler
