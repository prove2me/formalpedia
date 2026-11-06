-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonicalSextic_pow_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:38:29.585985+00:00
-- url     : https://prove2.me/submissions/2550e841-85b9-419f-8630-512268318b7b

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Theorems.Thm_OAI_ActualEisensteinCubic_sexticChar_order


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
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {j : ℕ} (hj0 : j ≠ 0) (hj6 : j < 6) :
    canonicalSextic P hgood ^ j ≠ 1 := by
  change ((sexticChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding) ^ j ≠ 1
  rw [MulChar.ringHomComp_pow]
  apply (MulChar.ringHomComp_ne_one_iff
    ConcreteTraceCRT.eisEmbedding_injective).2
  apply pow_ne_one_of_lt_orderOf hj0
  rwa [sexticChar_order P hgood hchar]
end OAI.ActualEisensteinCubic
