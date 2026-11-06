-- Prove2me | solution 1 for OAI.ShortDraftCusp.A3_ramified_coprime_a_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:19:51.6218+00:00
-- url     : https://prove2.me/submissions/da4076c0-5064-4e86-9a2f-09b25503e683

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount

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
theorem _root_.solution (a b cprime d u : R)
    (hdet : a * d - b * (u * cprime) = 1) :
    IsCoprime a (a - u * b) := by
  refine ⟨d - cprime, cprime, ?_⟩
  linear_combination hdet
end OAI.ShortDraftCusp
