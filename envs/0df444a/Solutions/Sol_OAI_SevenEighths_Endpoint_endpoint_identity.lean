-- Prove2me | solution 1 for OAI.SevenEighths.Endpoint.endpoint_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:58:24.541767+00:00
-- url     : https://prove2.me/submissions/72250772-ef6d-4309-9f19-d843cf79d3d0

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Endpoint

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Endpoint
noncomputable section
namespace OAI.SevenEighths.Endpoint
theorem _root_.solution (δ y : ℝ) (hJ : balanceDenominator δ y ≠ 0) :
    10368 * certificateWeight y * balanceDenominator δ y * (-balancedExponent δ y) =
      (3 + 5 * y) * ((4 * certificateWeight y * δ - 79) ^ 2 + 49) +
      4 * y * (4 * certificateWeight y * δ *
        ((1 + 3 * y) * (15 + 32 * y) * δ + 9 - 13 * y) + 265 + 3485 * y) := by
  unfold balancedExponent balancedRowCount balancedCutoff
  field_simp
  simp only [balanceDenominator, denominator, primeWeight, certificateWeight]
  ring
end OAI.SevenEighths.Endpoint
