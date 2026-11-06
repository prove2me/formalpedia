-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.quadraticCharO_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:34:55.71192+00:00
-- url     : https://prove2.me/submissions/a6f2778b-d865-4f40-907e-196a0c49eb92

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
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hchar : ringChar (O ⧸ P) ≠ 2) : quadraticCharO P ≠ 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  change (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O) ≠ 1
  exact (MulChar.ringHomComp_ne_one_iff
    (Int.cast_injective (α := O))).2 (quadraticChar_ne_one hchar)
end OAI.ActualEisensteinCubic
