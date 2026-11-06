-- Prove2me | solution 1 for OAI.ShortDraftCusp.A3_unramified_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:17:43.688257+00:00
-- url     : https://prove2.me/submissions/3b92d7f9-bdda-4132-b689-eee6905f6f25

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
    cuspMatrix a b c d * unramifiedHInv u =
      !![-b,a + u * b;-d,c + u * d] := by
  simp [cuspMatrix, unramifiedHInv, mul_comm]
end OAI.ShortDraftCusp
