-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.ringComplex_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:20:17.794784+00:00
-- url     : https://prove2.me/submissions/e0154560-2f08-47e7-9a53-a62bfc8bd657

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier

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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution : Function.Injective ringComplex :=
  complexEmbedding.injective.comp NumberField.RingOfIntegers.coe_injective
end OAI.ActualEisensteinCubic
