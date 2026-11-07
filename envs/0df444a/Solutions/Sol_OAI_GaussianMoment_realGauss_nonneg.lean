-- Prove2me | solution 1 for OAI.GaussianMoment.realGauss_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:25:36.423204+00:00
-- url     : https://prove2.me/submissions/bcd8a573-4c3b-483a-9103-cfa163c70cc8

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian

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
open OAI.GaussianMoment
open scoped Topology
open Filter
namespace OAI.GaussianMoment
theorem _root_.solution (t : ℝ) (z : ℤ × ℤ) :
    0 ≤ realGauss t z := (Real.exp_pos _).le
end OAI.GaussianMoment
