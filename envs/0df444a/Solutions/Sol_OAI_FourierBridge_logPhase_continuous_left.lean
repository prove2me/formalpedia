-- Prove2me | solution 1 for OAI.FourierBridge.logPhase_continuous_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:15:01.440834+00:00
-- url     : https://prove2.me/submissions/0abbea16-0ae3-49c2-9159-a3a4eade18bf

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly

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
open OAI.FourierBridge
open scoped FourierTransform SchwartzMap
namespace OAI.FourierBridge
theorem _root_.solution (y : ℝ) :
    Continuous (fun t : ℝ => logPhase t y) := by
  unfold logPhase
  fun_prop
end OAI.FourierBridge
