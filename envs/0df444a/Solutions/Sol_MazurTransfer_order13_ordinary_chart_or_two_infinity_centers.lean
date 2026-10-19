-- Prove2me | solution 1 for MazurTransfer.order13_ordinary_chart_or_two_infinity_centers
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T19:09:32.900507+00:00
-- url     : https://prove2.me/submissions/5adecc29-063b-4143-bf02-a8c777399fbd

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualInfinityPlaceCenterData
import Definitions.Def_MazurTransfer_Order13PellInfinityLocalOrders
import Theorems.Thm_MazurTransfer_Order13OrdinaryChartComplement_point_in_ordinary_or_infinity
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: expose the exact original ordinary-chart complement theorem through a minimal statement interface with a unique named field fact. Named downstream consumer: the cubic principal-divisor support calculation, which also imports the accepted infinity uniformizer-order theorem. This is packaging of an existing proved statement and adds no new curve geometry.
-/
noncomputable section
open MazurTransfer AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13ActualInfinityPlaceCenters
local instance sourceOrdinaryComplementFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem solution (x : curveScheme ℚ) :
    x ∈ (ordinaryChartMap ℚ).opensRange ∨
      x = center 1 (Order13PellInfinityLocalOrders.positiveProof ℚ) ∨
      x = center (-1) (Order13PellInfinityLocalOrders.negativeProof ℚ) := by
  exact MazurTransfer.Order13OrdinaryChartComplement.point_in_ordinary_or_infinity x
#print axioms solution
