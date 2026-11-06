-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicGauss_cube_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:43:42.14724+00:00
-- url     : https://prove2.me/submissions/14194349-7394-4182-9ef0-10dc19c2a93c

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicGauss_cube
import Theorems.Thm_OAI_ActualEisensteinCubic_ringComplex_injective

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
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    gaussSum ((cubicChar P hgood).ringHomComp ringComplex)
      (AddChar.FiniteField.primitiveChar_to_Complex (O ⧸ P)) ^ 3 =
      -(ringComplex p) * (Nat.card (O ⧸ P) : ℂ) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  exact cubicGauss_cube ringComplex ringComplex_injective P hgood p hP hprimary
    (AddChar.FiniteField.primitiveChar_to_Complex (O ⧸ P))
    (AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (O ⧸ P))
end OAI.ActualEisensteinCubic
