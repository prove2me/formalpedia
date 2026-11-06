-- Prove2me | solution 1 for OAI.ShortDraftCusp.A3_unramified_coprime_a_minus_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:19:55.557201+00:00
-- url     : https://prove2.me/submissions/d077f741-9be5-4fdb-a4a4-44c11d0556d1

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
    (hdet : a * d - b * c = 1) : IsCoprime a (-b) := by
  refine ⟨d, c, ?_⟩
  linear_combination hdet
end OAI.ShortDraftCusp
