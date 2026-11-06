-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.omega_sq_for_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:22:10.528801+00:00
-- url     : https://prove2.me/submissions/0313bb3f-3c44-41b7-a361-79c91a1cc2fd

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
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
open OAI.ActualEisensteinCubic
open ActualEisensteinCoordinates ShortDraftLatticeCount
namespace OAI.ActualEisensteinCubic
theorem _root_.solution : omega ^ 2 = -omega - 1 := by
  simpa [omega] using
    IsCyclotomicExtension.Rat.Three.eta_sq
      (IsCyclotomicExtension.zeta_spec 3 ℚ K)
end OAI.ActualEisensteinCubic
