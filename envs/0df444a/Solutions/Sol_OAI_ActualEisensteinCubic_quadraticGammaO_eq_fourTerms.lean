-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.quadraticGammaO_eq_fourTerms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:52:38.199265+00:00
-- url     : https://prove2.me/submissions/70f1e98b-7bc7-4524-a089-522cc0dd45ff

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Theorems.Thm_OAI_ActualEisensteinCubic_actualOriginalAbelDualLimit
import Theorems.Thm_OAI_ActualEisensteinCubic_full_dual_abel_coefficient
import Theorems.Thm_OAI_ActualEisensteinCubic_fixedDualPhase_four_terms
import Theorems.Thm_OAI_ActualEisensteinCubic_original_abel_gamma_limit
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
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
    quadraticGammaO (ActualEisensteinCoordinates.eval a b) hc =
      breveGaussianFourTerms a b := by
  let c : O := ActualEisensteinCoordinates.eval a b
  let n : ℝ := ‖eisEmbedding c‖
  let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
  let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
  let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
  let L2 : ℂ := ((2 / (Real.sqrt 3 *
    (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
  let : Finite (O ⧸ Ideal.span {(2 : O)}) :=
    finite_quotient_span (by norm_num : (2 : O) ≠ 0)
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  let S : ℂ := ∑ r : O ⧸ Ideal.span {(2 : O)},
    fixedDualPhase c (GaussianShiftedPartition.representative 2 r)
  have hEq0 := tendsto_nhds_unique
    (original_abel_gamma_limit c hc)
    (actualOriginalAbelDualLimit a b hc)
  have hEq : (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * quadraticGammaO c hc) =
      (((Real.sqrt q / 2 : ℝ) : ℂ) *
        ((((4 / q : ℝ) : ℂ) * L2) * S)) := by
    simpa only [c, n, q, a2, b2, L2, S, mul_assoc] using hEq0
  have hC : (((Real.sqrt q / 2 : ℝ) : ℂ) *
      (((4 / q : ℝ) : ℂ) * L2)) =
      (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) / 2) := by
    simpa only [c, n, q, a2, b2, L2] using
      full_dual_abel_coefficient a b hc
  have hA : ((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) ≠ 0 := by
    have hn : 0 < n := norm_pos_iff.mpr (eisEmbedding_ne_zero hc)
    have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    exact_mod_cast (ne_of_gt (div_pos (by norm_num : (0 : ℝ) < 2)
      (mul_pos hs hn)))
  have hG : quadraticGammaO c hc = S / 2 := by
    apply mul_left_cancel₀ hA
    calc
      ((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * quadraticGammaO c hc =
          ((Real.sqrt q / 2 : ℝ) : ℂ) *
            ((((4 / q : ℝ) : ℂ) * L2) * S) := hEq
      _ = (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) / 2) * S := by rw [← mul_assoc, hC]
      _ = ((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * (S / 2) := by ring
  change quadraticGammaO c hc = breveGaussianFourTerms a b
  calc
    quadraticGammaO c hc = S / 2 := hG
    _ = breveGaussianFourTerms a b := fixedDualPhase_four_terms a b
end OAI.ActualEisensteinCubic
