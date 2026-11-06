-- Prove2me | solution 1 for OAI.SevenEighths.Endpoint.balanced_endpoint_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:42.5351+00:00
-- url     : https://prove2.me/submissions/72727b0d-e6cc-46c7-a9a7-eaac992e64d7

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Endpoint
import Theorems.Thm_OAI_SevenEighths_Endpoint_balanced_endpoint_margin

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Endpoint
noncomputable section
namespace OAI.SevenEighths.Endpoint
theorem _root_.solution {δ y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    balancedExponent δ y < -(1 / 10000 : ℝ) := by
  have h := balanced_endpoint_margin hδ0 hδ1 hy0 hy1
  norm_num at *
  linarith
end OAI.SevenEighths.Endpoint
