-- Prove2me | solution 2 for OAI.ActualEisensteinCubic.quadraticCharO_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:34:45.220203+00:00
-- url     : https://prove2.me/submissions/6eade318-2a4b-4afd-8d0f-88523cf79439

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
theorem _root_.solution (P : Ideal O) [P.IsMaximal] :
    quadraticCharO P ^ 2 = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  change ((quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O)) ^ 2 = 1
  exact ((quadraticChar_isQuadratic (O ⧸ P)).comp (Int.castRingHom O)).sq_eq_one
end OAI.ActualEisensteinCubic
