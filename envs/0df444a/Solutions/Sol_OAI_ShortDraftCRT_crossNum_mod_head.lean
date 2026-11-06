-- Prove2me | solution 1 for OAI.ShortDraftCRT.crossNum_mod_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:07.457601+00:00
-- url     : https://prove2.me/submissions/538f4c4d-e616-4623-9b13-c82e67d994e9

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.ShortDraftCRT
open AddChar
variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R]
namespace OAI.ShortDraftCRT
theorem _root_.solution (a c₀ p h : R) (rows : List (R × R)) :
    p ∣ crossNum a c₀ ((p, h) :: rows) - h * crossDen c₀ rows := by
  refine ⟨crossNum a c₀ rows, ?_⟩
  simp only [crossNum]
  ring
end OAI.ShortDraftCRT
