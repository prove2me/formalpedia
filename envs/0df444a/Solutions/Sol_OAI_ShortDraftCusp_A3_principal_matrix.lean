-- Prove2me | solution 1 for OAI.ShortDraftCusp.A3_principal_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:39:12.934837+00:00
-- url     : https://prove2.me/submissions/6e6679fe-a03a-4f6a-8411-280b79672719

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
theorem _root_.solution (a b c d : R) :
    cuspMatrix a b c d * (1 : Matrix (Fin 2) (Fin 2) R) =
      !![a,b;c,d] := by
  simp [cuspMatrix]
end OAI.ShortDraftCusp
