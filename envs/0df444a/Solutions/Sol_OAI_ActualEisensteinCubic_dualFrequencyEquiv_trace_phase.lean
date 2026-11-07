-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.dualFrequencyEquiv_trace_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:27:41.705676+00:00
-- url     : https://prove2.me/submissions/5eb18dcf-f791-4e1c-b1e8-1a9b481c6983

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Theorems.Thm_OAI_ActualEisensteinCubic_breveE_dual_quadratic_real_scale

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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (r : ℝ) (a b k l : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
        (dualFrequencyEquiv (k,l))^2)) /
        eisLam / ((4*r : ℝ) : ℂ)) =
      Complex.exp (-(2 * Real.pi * Complex.I *
        (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) /
        ((4*r : ℝ) : ℂ)) := by
  exact breveE_dual_quadratic_real_scale r a b k l
end OAI.ActualEisensteinCubic
