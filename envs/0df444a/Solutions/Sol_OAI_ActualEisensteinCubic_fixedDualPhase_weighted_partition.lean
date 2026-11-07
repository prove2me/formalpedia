-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.fixedDualPhase_weighted_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:29:06.351458+00:00
-- url     : https://prove2.me/submissions/880278b3-696f-4021-b027-477d1e1486da

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Theorems.Thm_OAI_ActualEisensteinCubic_fixedDualPhase_period_two
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_GaussianAbelPartition_tsum_by_finite_fibers
import Theorems.Thm_OAI_GaussianFiberEquiv_fiber_tsum
import Theorems.Thm_OAI_GaussianShiftedPartition_representative_spec


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
open ActualEisensteinCubic ShortDraftLatticeCount
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (c : O) (W : O → ℂ)
    (hsum : Summable (fun y : O => fixedDualPhase c y * W y)) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    (∑' y : O, fixedDualPhase c y * W y) =
      ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) *
          ∑' w : O,
            W (GaussianShiftedPartition.representative 2 r + 2*w) := by
  let h2 : (2 : O) ≠ 0 := by norm_num
  let : Finite (O ⧸ Ideal.span {(2 : O)}) := finite_quotient_span h2
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  rw [GaussianAbelPartition.tsum_by_finite_fibers
    (Ideal.Quotient.mk (Ideal.span {(2 : O)})) _ hsum]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    (∑' z : ((Ideal.Quotient.mk (Ideal.span {(2 : O)})) ⁻¹' {r}),
      fixedDualPhase c z.1 * W z.1) =
        ∑' w : O, fixedDualPhase c
          (GaussianShiftedPartition.representative 2 r + 2*w) *
          W (GaussianShiftedPartition.representative 2 r + 2*w) :=
      GaussianFiberEquiv.fiber_tsum 2 h2 r
        (GaussianShiftedPartition.representative 2 r)
        (GaussianShiftedPartition.representative_spec 2 r)
        (fun y => fixedDualPhase c y * W y)
    _ =
        ∑' w : O, fixedDualPhase c
          (GaussianShiftedPartition.representative 2 r) *
          W (GaussianShiftedPartition.representative 2 r + 2*w) := by
      apply tsum_congr
      intro w
      rw [fixedDualPhase_period_two]
    _ = _ := tsum_mul_left
end OAI.ActualEisensteinCubic
