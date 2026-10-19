-- Prove2me | solution 1 for MazurTransfer.Order13PellReciprocalExpression.reciprocal_expression
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T13:37:33.600997+00:00
-- url     : https://prove2.me/submissions/95f04123-e25c-4bc5-8988-c942e34b5ce1

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the explicit Pell polynomial and its reversed expression
agree after inverting the abscissa. Named downstream consumer: the actual
ordinary-chart unit expression for the Pell function.
-/
import Definitions.Def_MazurTransfer_Order13PellPolynomialCertificate
noncomputable section
universe u
open MazurTransfer
open Order13PellChartCertificate
open Order13PellChartCertificate

theorem solution (F : Type u) [Field F] (z w : F) (hz : z ≠ 0) :
    (pellH z⁻¹ + (w * (z⁻¹) ^ 3) * pellK z⁻¹) * z ^ 19 =
      infinityPellH z + w * infinityPellK z := by
  dsimp [pellH, pellK, infinityPellH, infinityPellK]
  field_simp <;> ring

#print axioms solution
