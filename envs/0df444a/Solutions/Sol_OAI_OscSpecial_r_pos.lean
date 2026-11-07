-- Prove2me | solution 1 for OAI.OscSpecial.r_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:25:13.488493+00:00
-- url     : https://prove2.me/submissions/f3212d3a-4f09-4d59-97e1-06c79ccd445c

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
open OAI.OscSpecial
namespace OAI.OscSpecial
theorem _root_.solution {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    0 < r η a b := by
  unfold r
  positivity
end OAI.OscSpecial
