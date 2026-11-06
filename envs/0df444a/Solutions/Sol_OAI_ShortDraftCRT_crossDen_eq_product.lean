-- Prove2me | solution 1 for OAI.ShortDraftCRT.crossDen_eq_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:16:55.392943+00:00
-- url     : https://prove2.me/submissions/095ee44b-f122-48e7-bdb3-356cdac9bab8

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
theorem _root_.solution (c₀ : R) (rows : List (R × R)) :
    crossDen c₀ rows = c₀ * (rows.map Prod.fst).prod := by
  induction rows with
  | nil => simp [crossDen]
  | cons ph rows ih =>
      rcases ph with ⟨p, h⟩
      simp only [crossDen, List.map_cons, List.prod_cons, ih]
      ring
end OAI.ShortDraftCRT
