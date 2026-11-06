-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.quadraticGammaO_rational
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:25:13.057112+00:00
-- url     : https://prove2.me/submissions/57acff03-eddb-47c0-8be8-fd03dcc671dc

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
theorem _root_.solution (m : ℕ) (hm : m ≠ 0)
    (hc : (m : O) ≠ 0) :
    quadraticGammaO (m : O) hc = quadraticGammaRational m hm := by rfl
end OAI.ActualEisensteinCubic
