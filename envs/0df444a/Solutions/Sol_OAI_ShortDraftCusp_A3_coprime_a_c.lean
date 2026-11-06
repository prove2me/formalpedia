-- Prove2me | solution 1 for OAI.ShortDraftCusp.A3_coprime_a_c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:19:49.256623+00:00
-- url     : https://prove2.me/submissions/5ae7c15d-900f-43ca-b84b-c72718f67f74

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
theorem _root_.solution (a b c d : R)
    (hdet : a * d - b * c = 1) : IsCoprime a c := by
  refine ⟨d, -b, ?_⟩
  linear_combination hdet
end OAI.ShortDraftCusp
