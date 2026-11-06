-- Prove2me | solution 1 for OAI.ConcreteTraceCRT.coordinateSubring_eq_traceSubring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:11.812933+00:00
-- url     : https://prove2.me/submissions/5a400a83-18ec-4442-a1ed-9dc6d9e80098

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding

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
open OAI.ConcreteTraceCRT
open EisensteinEmbedding IdealGaussCRT
namespace OAI.ConcreteTraceCRT
theorem _root_.solution :
    coordinateSubring = ShortDraftTrace.eisensteinSubring := by
  rfl
end OAI.ConcreteTraceCRT
