-- Prove2me | solution 1 for OAI.RationalPrimeExtraction.selected_row_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:29:05.252325+00:00
-- url     : https://prove2.me/submissions/708e3414-14f7-4ff3-9517-6e7e52c01e40

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Theorems.Thm_OAI_RationalQuant_rational_row_error_power

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open OAI.RationalPrimeExtraction
namespace OAI.RationalPrimeExtraction
theorem _root_.solution (D : ℕ) (hD : 1 ≤ D)
    (r : ℕ) (hr : r ∈ selected ((D : ℝ) ^ (4 / 45 : ℝ))) :
    ((128 * (D / r + 1) : ℕ) : ℝ) ≤
      512 * (D : ℝ) ^ (41 / 45 : ℝ) := by
  have hrlo : ⌊(D : ℝ) ^ (4 / 45 : ℝ) / 3⌋₊ < r :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1).1
  exact RationalQuant.rational_row_error_power D r hD
    (Nat.lt_of_floor_lt hrlo)
end OAI.RationalPrimeExtraction
