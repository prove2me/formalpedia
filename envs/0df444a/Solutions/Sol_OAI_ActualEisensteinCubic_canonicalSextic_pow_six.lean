-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonicalSextic_pow_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:37:31.374476+00:00
-- url     : https://prove2.me/submissions/591d70e7-6606-43c0-89dd-52543f53e7f8

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Theorems.Thm_OAI_ActualEisensteinCubic_sexticChar_powers


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
open OAI.ActualEisensteinCubic
open AddChar MulChar
open AddChar MulChar
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : canonicalSextic P hgood ^ 6 = 1 := by
  change ((sexticChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding) ^ 6 = 1
  rw [MulChar.ringHomComp_pow, (sexticChar_powers P hgood).2.2,
    MulChar.ringHomComp_one]
end OAI.ActualEisensteinCubic
