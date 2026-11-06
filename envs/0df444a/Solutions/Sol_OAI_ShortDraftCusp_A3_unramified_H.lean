-- Prove2me | solution 1 for OAI.ShortDraftCusp.A3_unramified_H
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:17:38.212869+00:00
-- url     : https://prove2.me/submissions/da5e0c0b-a911-4a31-b68f-bcda6428fd4c

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
theorem _root_.solution (u : R) :
    unramifiedH u = !![u,-1;1,0] := by
  simp [unramifiedH, U, E]
end OAI.ShortDraftCusp
