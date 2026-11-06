-- Prove2me | solution 1 for OAI.ShortDraftCusp.A3_ramified_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:17:37.69482+00:00
-- url     : https://prove2.me/submissions/134222c9-4b18-4ccb-9e17-b4de8ac3dbb6

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
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
open OAI.ShortDraftCusp
variable {R : Type*} [CommRing R]
namespace OAI.ShortDraftCusp
theorem _root_.solution (a b c d u : R) :
    cuspMatrix a b c d * L (-u) =
      !![a - u * b,b;c - u * d,d] := by
  simp [cuspMatrix, L, mul_comm, sub_eq_add_neg]
end OAI.ShortDraftCusp
