-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.conjO_eval_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:23:07.940855+00:00
-- url     : https://prove2.me/submissions/3a178140-6fc1-446d-8c6c-72f546a52aa2

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_omega_sq_for_norm
import Theorems.Thm_OAI_ActualEisensteinCubic_conjO_omega
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
theorem _root_.solution (a b : ℤ) :
    conjO (eval a b) = eval (a - b) (-b) := by
  have hω : ActualEisensteinCoordinates.omega = omega := rfl
  simp only [eval, map_add, map_mul, map_intCast, hω, conjO_omega]
  rw [omega_sq_for_norm]
  push_cast
  ring
end OAI.ActualEisensteinCubic
