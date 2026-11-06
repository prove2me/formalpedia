-- Prove2me | solution 1 for OAI.SevenEighths.LatticeSummability.summable_one_div_normForm_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:45:50.559072+00:00
-- url     : https://prove2.me/submissions/a2b6c1d2-1812-420a-80a5-5d72bef4c1e2

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability
import Theorems.Thm_OAI_SevenEighths_LatticeSummability_normForm_nonneg
import Theorems.Thm_OAI_SevenEighths_LatticeSummability_summable_normForm_neg_rpow
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k



set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.LatticeSummability
open EisensteinTheta
namespace OAI.SevenEighths.LatticeSummability
theorem _root_.solution {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => 1 / normForm n.1 n.2 ^ σ) := by
  simpa only [Real.rpow_neg (normForm_nonneg _ _), one_div] using
    summable_normForm_neg_rpow hσ
end OAI.SevenEighths.LatticeSummability
