-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.quadraticGammaO_traceLambda
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:26:07.010228+00:00
-- url     : https://prove2.me/submissions/722aa1b9-4235-4857-b4a1-71b2e441dfca

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization

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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
namespace OAI.ActualEisensteinCubic
theorem _root_.solution :
    quadraticGammaO traceLambda traceLambda_ne_zero =
      quadraticGammaTraceLambda := by rfl
end OAI.ActualEisensteinCubic
