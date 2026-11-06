-- Prove2me | solution 1 for OAI.SevenEighths.LatticeSummability.normForm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:40:59.179795+00:00
-- url     : https://prove2.me/submissions/9f19fd23-2dcc-473f-9b7a-df530492a46f

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability

set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.LatticeSummability
open EisensteinTheta
namespace OAI.SevenEighths.LatticeSummability
theorem _root_.solution (x y : ℝ) : 0 ≤ normForm x y := by
  unfold normForm
  nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]
end OAI.SevenEighths.LatticeSummability
