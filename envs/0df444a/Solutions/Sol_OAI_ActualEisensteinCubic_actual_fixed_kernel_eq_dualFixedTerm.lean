-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.actual_fixed_kernel_eq_dualFixedTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:43:54.572195+00:00
-- url     : https://prove2.me/submissions/39b366ae-7578-41ec-8993-87df98171d46

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Theorems.Thm_OAI_ActualEisensteinCubic_breveE_dual_quadratic_real_scale
import Theorems.Thm_OAI_ActualEisensteinCubic_dualFrequencyEquiv_norm_sq
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
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (a b k l : ℤ) (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let y : O := dualFrequencyEquiv (k,l)
    Complex.exp (-(Real.pi : ℂ) *
        (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) *
      fixedDualPhase c y =
      OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) (k,l) := by
  let c : O := ActualEisensteinCoordinates.eval a b
  let y : O := dualFrequencyEquiv (k,l)
  have hnormC : ((‖eisEmbedding y‖ : ℂ)^2) =
      (((k^2+k*l+l^2 : ℤ) : ℂ)) := by
    exact_mod_cast dualFrequencyEquiv_norm_sq k l
  have hreal : Complex.exp (-(Real.pi : ℂ) *
        (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) =
      (OscSpecial.dualAmp η (a : ℝ) (b : ℝ) (k,l) : ℂ) := by
    rw [hnormC]
    dsimp [OscSpecial.dualAmp, OscSpecial.dualScale, OscSpecial.dualQ]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hphase : fixedDualPhase c y =
      Complex.exp (Complex.I *
        (OscSpecial.phaseAngle (a : ℝ) (b : ℝ) (k,l) : ℂ)) := by
    have h := breveE_dual_quadratic_real_scale 1 a b k l
    have harg : fixedDualPhase c y =
        Complex.exp (-(2 * Real.pi * Complex.I *
          (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) / (4 : ℂ)) := by
      change ShortDraftTrace.breveE
        (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
          (ActualEisensteinCoordinates.eval (k+l) k)^2)) /
          eisLam / (4 : ℂ)) = _
      simpa using h
    rw [harg]
    congr 1
    dsimp [OscSpecial.phaseAngle, OscSpecial.dualTrace]
    push_cast
    ring
  dsimp only
  rw [hreal, hphase]
  rfl
end OAI.ActualEisensteinCubic
