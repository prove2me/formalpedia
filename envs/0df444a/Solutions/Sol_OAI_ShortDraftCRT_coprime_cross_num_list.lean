-- Prove2me | solution 1 for OAI.ShortDraftCRT.coprime_cross_num_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:31:52.355202+00:00
-- url     : https://prove2.me/submissions/d5d4a55b-b4f7-4b64-a01c-17c63948c3f2

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Theorems.Thm_OAI_ShortDraftCRT_coprime_cross_numerator

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
theorem _root_.solution (a c₀ : R) (rows : List (R × R))
    (hbase : IsCoprime a c₀) (hrows : GoodRows c₀ rows) :
    IsCoprime (crossNum a c₀ rows) (crossDen c₀ rows) := by
  revert hrows
  induction rows with
  | nil =>
      intro _
      simpa [crossNum, crossDen] using hbase
  | cons ph rows ih =>
      rcases ph with ⟨p, h⟩
      intro hrows
      rcases hrows with ⟨hrows, hhp, hdp⟩
      simpa [crossNum, crossDen] using
        coprime_cross_numerator (crossNum a c₀ rows)
          (crossDen c₀ rows) h p (ih hrows) hhp hdp
end OAI.ShortDraftCRT
