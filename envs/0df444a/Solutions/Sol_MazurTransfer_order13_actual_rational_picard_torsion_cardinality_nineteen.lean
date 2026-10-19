-- Prove2me | solution 1 for MazurTransfer.order13_actual_rational_picard_torsion_cardinality_nineteen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T17:53:49.128611+00:00
-- url     : https://prove2.me/submissions/78d62778-53a6-4a2d-a513-6a7091d49ebd

import Mathlib
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_MazurTransfer_Order13ActualRationalPicardTorsionNineteen_actual_rational_arithmetic_picard_torsion_card
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses the already accepted original rational Picard torsion-cardinality theorem; original official Anthropic FLT arithmetic Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: expose the unchanged full rational Picard torsion-cardinality statement with the literal arithmetic group constructors and minimal public statement imports. Named downstream consumer: the actual arithmetic norm-kernel cardinality product; no new torsion computation or rank assertion is made by this packaging bridge.
-/
noncomputable section
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
local instance sourceMinimalRationalPicardTorsionFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem solution :
    Finite (CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ)))) ∧
    Nat.card (CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ)))) = 19 := by
  exact MazurTransfer.Order13ActualRationalPicardTorsionNineteen.actual_rational_arithmetic_picard_torsion_card
#print axioms solution
