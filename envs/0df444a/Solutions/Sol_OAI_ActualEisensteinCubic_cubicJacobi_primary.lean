-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicJacobi_primary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:36:30.717368+00:00
-- url     : https://prove2.me/submissions/ff248ea6-b340-4758-8e8c-b88658417adb

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_pow_three

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
open NumberField
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    ∃ z ∈ Algebra.adjoin ℤ {omega},
      jacobiSum (cubicChar P hgood) (cubicChar P hgood) =
        -1 + z * lambda ^ 2 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  simpa only [lambda] using
    (exists_jacobiSum_eq_neg_one_add (n := 3) (by decide)
      (cubicChar_pow_three P hgood) (cubicChar_pow_three P hgood)
      (by simpa only [Nat.card_eq_fintype_card] using card_sub_one_div_three P hgood)
      omega_primitive)
end OAI.ActualEisensteinCubic
