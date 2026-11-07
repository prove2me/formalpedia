-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.variableDualPhase_abel_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:30:59.541805+00:00
-- url     : https://prove2.me/submissions/db416e47-c5a8-424b-ad96-0b31fd61add1

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Theorems.Thm_OAI_ActualEisensteinCubic_fixedDualPhase_norm_one
import Theorems.Thm_OAI_ActualEisensteinCubic_actual_O_fiber_gaussian_mass
import Theorems.Thm_OAI_ActualEisensteinCubic_coordinate_norm_pos_of_nonzero
import Theorems.Thm_OAI_ActualEisensteinCubic_eis_gaussian_summable
import Theorems.Thm_OAI_ActualEisensteinCubic_fixedDualPhase_weighted_partition
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_OscSpecial_abel_mass_dual_scale
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open Filter
open scoped Topology
open OAI.ActualEisensteinCubic
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    let c : O := ActualEisensteinCoordinates.eval a b
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    let L2 : ℂ := ((2 / (Real.sqrt 3 *
      (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
    let K : ℂ := (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) * L2)
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' y : O, fixedDualPhase c y *
        Complex.exp (-(Real.pi : ℂ) *
          (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
          (‖eisEmbedding y‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (K * ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r))) := by
  let h2 : (2 : O) ≠ 0 := by norm_num
  let : Finite (O ⧸ Ideal.span {(2 : O)}) := finite_quotient_span h2
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  let c : O := ActualEisensteinCoordinates.eval a b
  let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
  let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
  let L2 : ℂ := ((2 / (Real.sqrt 3 *
    (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
  let K : ℂ := (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) * L2)
  let W (η : ℝ) (y : O) := Complex.exp
    (-(Real.pi : ℂ) *
      (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
      (‖eisEmbedding y‖ ^ 2 : ℂ))
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  have hfiber (r : O ⧸ Ideal.span {(2 : O)}) :
      Tendsto (fun η : ℝ => (η : ℂ) *
        (∑' w : O, W η
          (GaussianShiftedPartition.representative 2 r + 2*w)))
        (𝓝[>] (0 : ℝ)) (𝓝 K) := by
    let F : ℝ → ℂ := fun t => ∑' w : O,
      Complex.exp (-(Real.pi : ℂ) * (t : ℂ) *
        (‖eisEmbedding (GaussianShiftedPartition.representative 2 r + 2*w)‖ ^ 2 : ℂ))
    have hbase : Tendsto (fun t : ℝ => (t : ℂ) * F t)
        (𝓝[>] (0 : ℝ)) (𝓝 L2) := by
      simpa only [F, L2, a2, b2] using
        actual_O_fiber_gaussian_mass (2 : O)
          (GaussianShiftedPartition.representative 2 r) h2
    have h := OscSpecial.abel_mass_dual_scale (a : ℝ) (b : ℝ) hq F L2 hbase
    simpa only [W, F, K] using h
  have hsum : Tendsto (fun η : ℝ =>
      ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative 2 r + 2*w))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) * K)) := by
    apply tendsto_finsetSum Finset.univ
    intro r hr
    exact (hfiber r).const_mul _
  have hpoint (η : ℝ) (hη : 0 < η) :
      (η : ℂ) * (∑' y : O, fixedDualPhase c y * W η y) =
      ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative 2 r + 2*w))) := by
    have hrpos : 0 < OscSpecial.r η (a : ℝ) (b : ℝ) := by
      unfold OscSpecial.r
      positivity
    have htpos : 0 < OscSpecial.dualScale η (a : ℝ) (b : ℝ) := by
      unfold OscSpecial.dualScale
      positivity
    have hbase := (eis_gaussian_summable htpos).norm
    have hkernel : Summable (fun y : O => fixedDualPhase c y * W η y) := by
      apply hbase.of_norm_bounded
      intro y
      simp only [norm_mul]
      have hp : ‖fixedDualPhase c y‖ = 1 := fixedDualPhase_norm_one c y
      rw [hp, one_mul]
    have hpart := fixedDualPhase_weighted_partition c (W η) hkernel
    rw [hpart, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have heq : (fun η : ℝ => (η : ℂ) *
      (∑' y : O, fixedDualPhase c y * W η y)) =ᶠ[
        𝓝[>] (0 : ℝ)]
      (fun η : ℝ => ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative 2 r + 2*w)))) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hpoint η hη
  have hlim := hsum.congr' heq.symm
  have hKsum :
      (∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) * K) =
      K * ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) := by
    rw [← Finset.sum_mul, mul_comm]
  rw [hKsum] at hlim
  exact hlim
end OAI.ActualEisensteinCubic
